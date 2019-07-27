module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module ST = Ast.Surface.Type
module D = Ast.Desugared.Expr
module DT = Ast.Desugared.Type

let error e =
  raise (MuleErr.MuleExn e)

let incomplete_pattern p =
  error (MuleErr.IncompletePattern p)

let unreachable_case (_p:SP.t) =
  error MuleErr.UnreachableCases

let var_to_lbl v = Ast.Var.to_string v |> Ast.Label.of_string

let substitue_type_apps: ST.t -> ST.t -> VarSet.t -> ST.t -> ST.t =
  fun old new_ vars ->
  let rec go ty =
    if Poly.equal ty old then
      new_
    else
      begin match ty with
        | ST.Quant (q, vs, body) ->
            let shadowed =
              List.fold
                vs
                ~init:false
                ~f:(fun ret var -> ret || Set.mem vars var)
            in
            if shadowed then
              ty
            else
              ST.Quant(q, vs, go body)
        | ST.Recur(v, body) ->
            if Set.mem vars v then
              ty
            else
              ST.Recur(v, go body)
        | ST.Fn(p, r) -> ST.Fn(go p, go r)
        | ST.App(f, x) -> ST.App(go f, go x)
        | ST.Union(l, r) -> ST.Union(go l, go r)
        | ST.Annotated(v, t) -> ST.Annotated(v, go t)
        | ST.Record items -> ST.Record(List.map items ~f:go_record_item)
        | ST.RowRest _ | ST.Var _ | ST.Ctor _ | ST.Path _ -> ty
      end
  and go_record_item = function
    | ST.Field(l, t) -> ST.Field(l, go t)
    | ST.Type(_, _, None) as ty -> ty
    | ST.Type(lbl, vs, Some ty) ->
        let shadowed =
          List.fold
            (Ast.var_of_label lbl :: vs)
            ~init:false
            ~f:(fun ret var -> ret || Set.mem vars var)
        in
        if shadowed then
          ST.Type(lbl, vs, Some ty)
        else
          ST.Type(lbl, vs, Some (go ty))
    | ST.Rest v -> ST.Rest v
  in
  go

let rec quantify_opaques = function
  (* Transform opaque type members into existentials, e.g.
   *
   * { type t }
   *
   * becomes:
   *
   * exist a. { type t = a }
  *)
  | DT.App(i, f, x) ->
      DT.App
        ( i
        , quantify_opaques f
        , quantify_opaques x
        )
  | DT.TypeLam(i, v, t) ->
      DT.TypeLam(i, v, quantify_opaques t)
  | DT.Annotated(i, v, t) ->
      DT.Annotated(i, v, quantify_opaques t)
  | DT.Record {r_info; r_types = (i, fields, rest); r_values} ->
      let vars = ref [] in
      let fields' = List.map fields ~f:(fun (lbl, ty) ->
          match quantify_opaques ty with
          | DT.Opaque (i, k) ->
              let var = Gensym.anon_var () in
              vars := (var, k) :: !vars;
              (lbl, DT.Var (i, var))
          | ty' -> (lbl, ty')
        )
      in
      let init =
        DT.Record
          { r_info
          ; r_types = (i, fields', rest)
          ; r_values = quantify_row_opaques r_values
          }
      in
      List.fold !vars ~init ~f:(fun ty (v, k) ->
          DT.Quant((), `Exist, v, k, ty)
        )
  | DT.Opaque i -> DT.Opaque i
  | DT.Fn(i, param, ret) ->
      DT.Fn(i, quantify_opaques param, quantify_opaques ret)
  | DT.Recur (i, v, t) -> DT.Recur(i, v, quantify_opaques t)
  | DT.Var v -> DT.Var v
  | DT.Union row -> DT.Union(quantify_row_opaques row)
  | DT.Quant(i, q, v, k, t) -> DT.Quant(i, q, v, k, quantify_opaques t)
  | DT.Named(i, s) -> DT.Named(i, s)
  | DT.Path p -> DT.Path p
and quantify_row_opaques (i, fields, rest) =
  ( i
  , List.map
      fields
      ~f:(fun (lbl, ty) -> (lbl, quantify_opaques ty))
  , rest
  )


let rec desugar_type' = function
  | ST.Fn(param, ret) ->
      DT.Fn((), desugar_type' param, desugar_type' ret)
  | ST.Quant(q, vs, body) ->
      List.fold_right
        vs
        ~init:(desugar_type' body)
        ~f:(fun v body -> DT.Quant((), q, v, `Unknown, body))
  | ST.Recur(v, body) ->
      DT.Recur((), v, desugar_type' body)
  | ST.Var v ->
      DT.Var((), v)
  | ST.Union u ->
      DT.Union (desugar_union_type None u)
  | ST.Record r ->
      desugar_record_type [] [] r
  | ST.App(ST.Ctor l, t) ->
      DT.Union((), [(l, desugar_type' t)], None)
  | ST.RowRest v ->
      DT.Union((), [], Some v)
  | ST.Annotated(v, ty) ->
      DT.Annotated((), v, desugar_type' ty)
  | ST.Path(v, ls) ->
      DT.Path((), v, ls)
  | ST.App(f, x) ->
      DT.App((), desugar_type' f, desugar_type' x)
  | ST.Ctor _ ->
      failwith "BUG: ctors should be applied."
and desugar_union_type tail (l, r) =
  match desugar_type' l, desugar_type' r, tail with
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, None), (Some v)
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, Some v), None
  | DT.Union((), lbls_l, Some v), DT.Union((), lbls_r, None), None ->
      ((), lbls_l @ lbls_r, Some v)
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, None), None ->
      ((), lbls_l @ lbls_r, None)
  | _ -> raise
        (MuleErr.MuleExn
           (MuleErr.MalformedType
              "Unions must be composed of ctors and at most one ...r"))
and desugar_record_type types fields = function
  (* TODO: how do we have variable fields for the type row? *)
  | (ST.Type(lbl, params, Some t) :: fs) ->
      let (_, ty) = desugar_type_binding (Ast.var_of_label lbl, params, t) in
      desugar_record_type ((lbl, ty)::types) fields fs
  | (ST.Type(lbl, params, None) :: fs) ->
      let kind = List.fold params ~init:`Unknown ~f:(fun k _ -> `Arrow(`Unknown, k)) in
      desugar_record_type ((lbl, DT.Opaque ((), kind))::types) fields fs
  | [] ->
      DT.Record
        { r_info = ()
        ; r_types = ((), types, None)
        ; r_values = ((), fields, None)
        }
  | [ST.Rest v] ->
      DT.Record
        { r_info = ()
        ; r_types = ((), types, None)
        ; r_values = ((), fields, Some v)
        }
  | (ST.Field (l, t) :: rest) ->
      desugar_record_type types ((l, desugar_type' t)::fields) rest
  | (ST.Rest _ :: _) -> raise
        (MuleErr.MuleExn
           (MuleErr.MalformedType "row variable before the end of a record type."))
and desugar_type t =
  desugar_type' t
  |> quantify_opaques
and desugar = function
  | S.Integer n -> D.Integer n
  | S.Text s -> D.Text s
  | S.Var v -> D.Var v
  | S.App (f, x) -> D.App (desugar f, desugar x)
  | S.Lam (SP.Var (v, None) :: pats, body) ->
      D.Lam(v, desugar (S.Lam (pats, body)))
  | S.Lam (SP.Wild :: pats, body) ->
      D.Lam(Gensym.anon_var (), desugar (S.Lam (pats, body)))
  | S.Lam ((SP.Var (v, Some ty) :: pats), body) ->
      let v' = Gensym.anon_var () in
      D.Lam
        ( v'
        , D.Let
            ( v
            , D.App(D.WithType (desugar_type ty), D.Var v')
            , desugar (S.Lam (pats, body))
            )
        )
  | S.Lam ((SP.Integer _) as p :: _, _) ->
      incomplete_pattern p
  | S.Lam (pat :: pats, body) ->
      let var = Gensym.anon_var () in
      D.Lam
        ( var
        , desugar
            (S.Match
               ( S.Var var
               , [ (pat
                   , S.Lam (pats, body)
                   )
                 ]
               )
            )
        )
  | S.Lam ([], body) -> desugar body
  | S.Record [] -> D.EmptyRecord
  | S.Record fields -> desugar_record fields
  | S.Update(e, []) ->
      desugar e
  | S.Update(e, (`Value (l, _, v)::fs)) ->
      D.App(D.App(D.Update(`Value, l), (desugar (S.Update(e, fs)))), desugar v)
  | S.Update(e, (`Type (lbl, params, ty) :: fs)) ->
      let (_, ty) = desugar_type_binding (Ast.var_of_label lbl, params, ty) in
      D.App(D.App(D.Update(`Type, lbl), desugar (S.Update(e, fs))), D.Witness ty)
  | S.GetField (e, l) ->
      D.App(D.GetField(`Strict, l), desugar e)
  | S.Ctor label ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let param = Ast.Var.of_string "x" in
      D.Lam (param, D.Ctor (label, D.Var param))
  | S.Match (e, cases) ->
      D.App (desugar_match cases, desugar e)
  | S.WithType(e, ty) ->
      D.App(D.WithType(desugar_type ty), desugar e)
  | S.Let(bindings, body) ->
      desugar_let bindings body
and desugar_record fields =
  let record_var = Gensym.anon_var () in
  let get_record_field lbl =
    D.App(D.GetField(`Lazy, lbl), D.Var record_var)
  in
  let label_map =
    List.filter_map fields ~f:(function
        | `Value (l, ty, _) ->
            Some (l, ty)
        | `Type _ -> None)
    |> Map.of_alist_exn (module Ast.Label)
  in
  let rec subst env expr = match expr with
    (* TODO: do stuff with type variables *)
    | D.Integer n -> D.Integer n
    | D.Text s -> D.Text s
    | D.Var v ->
        let lbl = var_to_lbl v in
        begin match Map.find env lbl with
          | None -> D.Var v
          | Some None -> get_record_field lbl
          | Some (Some ty) ->
              D.App(D.WithType(desugar_type ty), get_record_field lbl)
        end
    | D.Ctor(lbl, body) ->
        D.Ctor(lbl, subst env body)
    | D.Lam (v, body) ->
        D.Lam
          ( v
          , subst
              (Map.remove env (var_to_lbl v))
              body
          )
    | D.App(f, x) ->
        D.App(subst env f, subst env x)
    | D.Match {cases; default} ->
        D.Match
          { cases =
              Map.map cases ~f:(fun (var, body) ->
                  let env' = Map.remove env (var_to_lbl var) in
                  ( var
                  , subst env' body
                  )
                )
          ; default = Option.map default ~f:(function
                | (None, body) -> (None, subst env body)
                | (Some var, body) ->
                    ( Some var
                    , let env' = Map.remove env (var_to_lbl var) in
                      subst env' body
                    )
              )
          }
    | D.IntMatch {im_cases; im_default} ->
        D.IntMatch
          { im_cases = Map.map im_cases ~f:(subst env)
          ; im_default = subst env im_default
          }
    | D.Let(v, e, body) ->
        D.Let
          ( v
          , subst env e
          , subst (Map.remove env (var_to_lbl v)) body
          )
    | D.LetType(binds, body) ->
        D.LetType(binds, subst env body)
    | D.Fix _ | D.EmptyRecord | D.GetField _ | D.Update _ | D.WithType _ | D.Witness _ ->
        expr
  in
  let build_record =
    List.fold_right
      ~init:D.EmptyRecord
      ~f:(fun field old ->
          match field with
          | `Type (lbl, params, body) ->
              (* TODO: this is insufficient, since the types may need to
               * be mutually recursive, and in scope for all record fields.
               *)
              let (v, ty) =
                desugar_type_binding
                  ( Ast.var_of_label lbl
                  , params
                  , body
                  )
              in
              D.LetType
                ( [v, ty]
                , D.App
                    ( D.Update(`Type, lbl)
                    , old
                    )
                )
          | `Value(l, ty, v) ->
              let v' =
                begin match ty with
                  | None -> v
                  | Some ty' -> S.WithType(v, ty')
                end
              in
              D.App
                ( D.App(D.Update (`Value, l), old)
                , subst label_map (desugar v')
                )
        )
  in
  D.App(D.Fix `Record, D.Lam(record_var, build_record fields))
and desugar_match cases =
  begin match cases with
    | ((SP.Ctor _, _) :: _) ->
        desugar_lbl_match LabelMap.empty cases
    | ((SP.Integer _, _) :: _) ->
        desugar_int_match ZMap.empty cases
    | [(pat, body)] ->
        desugar (S.Lam([pat], body))
    | [] -> D.Match
          { cases = LabelMap.empty
          ; default = None
          }
    | ((SP.Wild, _) :: _) | ((SP.Var _, _) :: _) ->
        unreachable_case SP.Wild
  end
and desugar_int_match dict = function
  | [(SP.Wild, body)] -> D.IntMatch
        { im_default = D.Lam(Gensym.anon_var (), desugar body)
        ; im_cases = dict
        }
  | ((SP.Wild, _) :: _) ->
      unreachable_case SP.Wild
  | [(SP.Var _) as p, body] ->
      D.IntMatch
        { im_default = desugar (S.Lam([p], body))
        ; im_cases = dict
        }
  | ((SP.Var _, _) :: _) ->
      unreachable_case SP.Wild
  | ((SP.Integer n, body) :: rest) ->
      begin match Map.find dict n with
        | Some _ -> unreachable_case (SP.Integer n)
        | None ->
            desugar_int_match
              (Map.set dict ~key:n ~data:(desugar body))
              rest
      end
  | [] ->
      (* TODO: what should the argument actually be here? *)
      incomplete_pattern SP.Wild
  | ((SP.Ctor _, _) :: _) ->
      error
        (MuleErr.TypeError
           (MuleErr.MismatchedCtors (`Named "union", `Named "int")))
and desugar_lbl_match dict = function
  | [] -> D.Match
        { default = None
        ; cases = finalize_dict dict
        }
  | [(SP.Wild, body)] -> D.Match
        { default = Some (None, desugar body)
        ; cases = finalize_dict dict
        }
  | [SP.Var (v, None), body] ->
      D.Match
        { default = Some (Some v, desugar body)
        ; cases = finalize_dict dict
        }
  | [SP.Var (v, Some ty), body] ->
      let v' = Gensym.anon_var () in
      let let_ = D.Let
          ( v
          , D.App(D.WithType(desugar_type ty), D.Var v')
          , desugar body
          )
      in
      D.Match
        { default = Some(Some v', let_)
        ; cases = finalize_dict dict
        }
  | (SP.Ctor (lbl, p), body) :: cases ->
      let dict' =
        Map.update dict lbl ~f:(function
            | None -> [(p, body)]
            | Some cases -> ((p, body) :: cases)
          )
      in
      desugar_lbl_match dict' cases
  | (_ :: _) ->
      raise MuleErr.(MuleExn UnreachableCases)
and finalize_dict dict =
  Map.map dict
    ~f:( fun cases ->
        let v = Gensym.anon_var () in
        ( v
        , D.App
            ( desugar_lbl_match LabelMap.empty (List.rev cases)
            , D.Var v
            )
        )
      )
and desugar_let bs body = match simplify_bindings bs with
  | [] ->
      (* Shouldn't ever happen, but the correct behavior is clear. *)
      desugar body
  | [`Value(v, e)] ->
      D.Let(v, D.App(D.Fix `Let, D.Lam(v, desugar e)), desugar body)
  | [`Type t] ->
      let (v, ty) = desugar_type_binding t in
      D.LetType([v, ty], desugar body)
  | bindings ->
      let record =
        List.map bindings ~f:(function
            | `Value(v, S.WithType(e, ty)) ->
                `Value(Ast.var_to_label v, Some ty, e)
            | `Value (v, e) ->
                `Value(Ast.var_to_label v, None, e)
            | `Type (f, params, body) ->
                `Type(Ast.var_to_label f, params, body)
          )
        |> desugar_record
      in
      let record_name = Gensym.anon_var () in
      let body =
        List.fold bindings ~init:(desugar body) ~f:(fun accum bind ->
            match bind with
            | `Value(v, _) ->
                D.Let
                  ( v
                  , D.App
                      ( D.GetField(`Strict, Ast.var_to_label v)
                      , D.Var record_name
                      )
                  , accum
                  )
            | `Type t ->
                let (v, ty) = desugar_type_binding t in
                D.LetType([v, ty], accum)
          )
      in
      D.Let(record_name, record, body)
and desugar_type_binding (v, params, ty) =
  (* Here, we convert things like `type t a b = ... (t a b) ...` to
   * `lam a b. rec t. ... t ...`.
  *)
  let target =
    List.fold_left
      params
      ~init:(ST.Var v)
      ~f:(fun f x -> ST.App(f, ST.Var x))
  in
  let ty =
    ST.Recur
      ( v
      , substitue_type_apps
          target
          (ST.Var v)
          (Set.of_list (module Ast.Var) params)
          ty
      )
  in
  let ty =
    List.fold_right
      params
      ~init:(desugar_type ty)
      ~f:(fun param tybody -> DT.TypeLam((), param, tybody))
  in
  (v, ty)
and simplify_bindings = function
  (* Simplify a list of bindings, such that there are no "complex" patterns;
   * everything is a simple variable. *)
  | [] -> []
  | `BindType t :: bs ->
      `Type t :: simplify_bindings bs
  | `BindVal (SP.Var (v, None), e) :: bs ->
      `Value(v, e) :: simplify_bindings bs
  | `BindVal((SP.Integer _) as p, _) :: _ ->
      incomplete_pattern p
  | `BindVal(SP.Wild, e) :: bs  ->
      `Value(Gensym.anon_var (), e) :: simplify_bindings bs
  | `BindVal(SP.Var(v, Some ty), e) :: bs ->
      `Value(v, S.WithType(e, ty)) :: simplify_bindings bs
  | `BindVal(SP.Ctor(lbl, pat), e) :: bs ->
      let bind_var = Gensym.anon_var () in
      let match_var = Gensym.anon_var () in
      `Value(bind_var, S.Match(e, [(SP.Ctor(lbl, SP.Var(match_var, None)), S.Var match_var)]))
      :: simplify_bindings (`BindVal(pat, S.Var bind_var) :: bs)


let desugar e =
  try Ok (desugar e)
  with MuleErr.MuleExn err -> Error err
