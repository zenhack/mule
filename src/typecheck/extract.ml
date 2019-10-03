open Typecheck_types
open Ast
open Ast.Desugared

module ST = Ast.Surface.Type

(* A "semi-extracted" type. This has the basic structure and some metadata,
 * but still needs a bit of work to fix up/label the quantifiers.
*)
type semi_t =
  [ `Quant of q_args
  | `Fn of (int * semi_t * semi_t)
  | `Var of semi_var
  | `Named of (int * string * semi_t list)
  | `Union of (int * semi_row)
  | `Record of (int * semi_row * semi_row)
  | `Recur of (int * semi_t)
  | `Visited of int
  | `App of (int * semi_t * semi_t)
  | `Lambda of (int * semi_var * semi_t)
  ]
and semi_row =
  [ `Extend of (Label.t * semi_t * semi_row)
  | `Empty
  | `Var of semi_var
  ]
and q_args =
  { q_id : int
  ; q_var : int
  ; q_flag : bound_ty
  ; q_arg : semi_t
  }
and semi_var =
  { v_flag : bound_ty
  ; v_var_id : int
  ; v_q_id : int
  }

type sign = [ `Pos | `Neg ]

let ivar i = Ast.Var.of_string ("t" ^ Int.to_string i)

let maybe_add_rec: int -> IntSet.t -> semi_t -> (IntSet.t * semi_t) =
  fun i vars ty ->
  if Set.mem vars i then
    (Set.remove vars i, `Recur(i, ty))
  else
    (vars, ty)

let rec add_rec_binders: semi_t -> (IntSet.t * semi_t) = fun ty ->
  match ty with
  | `Named _ ->
      ( IntSet.empty
      , ty
      )
  | `App(i, f, x) ->
      let (fvars, f') = add_rec_binders f in
      let (xvars, x') = add_rec_binders x in
      ( Set.union fvars xvars
      , `App(i, f', x')
      )
  | `Var {v_var_id; _} ->
      ( IntSet.singleton v_var_id
      , ty
      )
  | `Visited v ->
      ( IntSet.singleton v
      , ty
      )
  | `Recur(i, t) ->
      let (vs, ts) = add_rec_binders t in
      ( Set.remove vs i
      , `Recur(i, ts)
      )
  | `Lambda(i, param, body) ->
      let (vs, body) = add_rec_binders body in
      ( Set.remove vs i
      , `Lambda(i, param, body)
      )
  | `Fn (i, f, x) ->
      let (fv, ft) = add_rec_binders f in
      let (xv, xt) = add_rec_binders x in
      maybe_add_rec i (Set.union fv xv) (`Fn(i, ft, xt))
  | `Record(r_info, r_types, r_values) ->
      let (ty_vars, ty_ret) = row_add_rec_binders r_types in
      let (val_vars, val_ret) = row_add_rec_binders r_values in
      maybe_add_rec
        r_info
        (Set.union ty_vars val_vars)
        (`Record
           ( r_info
           , ty_ret
           , val_ret
           )
        )
  | `Union(i, row) ->
      let (vars, ret) = row_add_rec_binders row in
      maybe_add_rec i vars (`Union(i, ret))
  | `Quant q ->
      let (vars, arg) = add_rec_binders q.q_arg in
      maybe_add_rec q.q_id vars (`Quant { q with q_arg = arg })
and row_add_rec_binders: semi_row -> (IntSet.t * semi_row) = function
  | `Empty -> (IntSet.empty, `Empty)
  | `Var v -> (IntSet.singleton v.v_var_id, `Var v)
  | `Extend(lbl, head, tail) ->
      let (hv, ht) = add_rec_binders head in
      let (tv, tt) = row_add_rec_binders tail in
      ( Set.union hv tv
      , `Extend(lbl, ht, tt)
      )
let add_rec_binders ty =
  snd (add_rec_binders ty)


let rec semi_extract_t: IntSet.t -> u_var -> semi_t =
  fun visited uvar ->
  let t = UnionFind.get uvar in
  let {ty_id; _} = get_tyvar t in
  if Set.mem visited ty_id then
    `Visited ty_id
  else
    begin
      let visited = Set.add visited ty_id in
      match t with
      | `Quant(_, arg) ->
          `Quant
            { q_id = ty_id
            ; q_arg = semi_extract_t visited arg
            (* These will get changed later, in a second pass: *)
            ; q_var = ty_id
            ; q_flag = `Flex
            }
      | `Free(tyvar, _) -> `Var (semi_extract_tyvar tyvar)
      | `Const (_, `Named name, args, _) ->
          begin match name, args with
            | "->", [param, _; ret, _] ->
                `Fn(ty_id, semi_extract_t visited param, semi_extract_t visited ret)
            | "{...}", [r_types, _; r_values, _] ->
                `Record
                  ( ty_id
                  , semi_extract_row visited r_types
                  , semi_extract_row visited r_values
                  )
            | "|", [row, _] ->
                `Union(ty_id, semi_extract_row visited row)
            | "<apply>", [f, _; x, _] ->
                `App(ty_id, semi_extract_t visited f, semi_extract_t visited x)
            | "<lambda>", [param, _; body, _] ->
                let param_var = semi_extract_tyvar (get_tyvar (UnionFind.get param)) in
                `Lambda(ty_id, param_var, semi_extract_t visited body)
            | _ ->
                `Named(ty_id, name, List.map args ~f:(fun (ty, _) -> semi_extract_t visited ty))
          end
      | `Const (_, `Extend _, _, _) ->
          MuleErr.bug "Kind error"
    end
and semi_extract_row visited uvar = match UnionFind.get uvar with
  | `Quant _ -> MuleErr.bug "Kind error"
  | `Free(tyvar, _) -> `Var(semi_extract_tyvar tyvar)
  | `Const(_, `Extend lbl, [head, _; tail, _], _) ->
      `Extend(lbl, semi_extract_t visited head, semi_extract_row visited tail)
  | `Const(_, `Named "<empty>", [], _) ->
      `Empty
  | `Const _ ->
      MuleErr.bug "illegal const"
and semi_extract_tyvar: tyvar -> semi_var = fun {ty_id; ty_bound} ->
  let {b_at; b_ty} = !ty_bound in
  { v_flag = b_ty
  ; v_var_id = ty_id
  ; v_q_id =
      match b_at with
      | `Ty bnd -> (get_tyvar (UnionFind.get (Lazy.force bnd))).ty_id
      | `G {g_id; _} -> g_id
  }

type fix_q_ctx =
  { fq_var_to_q: int IntMap.t
  ; fq_var_of_q: IntSet.t IntMap.t
  ; fq_vars_by_id: semi_var IntMap.t
  }

let empty_ctx =
  { fq_var_to_q = IntMap.empty
  ; fq_var_of_q = IntMap.empty
  ; fq_vars_by_id = IntMap.empty
  }

let merge_ctxs l r =
  let merge_right = Map.merge_skewed ~combine:(fun ~key:_ _ v -> v) in
  { fq_var_to_q = merge_right l.fq_var_to_q r.fq_var_to_q
  ; fq_var_of_q =
      Map.merge_skewed l.fq_var_of_q r.fq_var_of_q
        ~combine:(fun ~key:_ l r -> Set.union l r)
  ; fq_vars_by_id = merge_right l.fq_vars_by_id r.fq_vars_by_id
  }

let rec fix_quantifiers: semi_t -> (semi_t * fix_q_ctx) = function
  | `Visited v -> (`Visited v, empty_ctx)
  | `Recur(v, arg) ->
      let (arg', ctx) = fix_quantifiers arg in
      (`Recur(v, arg'), ctx)
  | `Var v -> (`Var v, fix_var_quantifiers v)
  | `Fn(i, param, ret) ->
      let (param', param_ctx) = fix_quantifiers param in
      let (ret', ret_ctx) = fix_quantifiers ret in
      ( `Fn(i, param', ret')
      , merge_ctxs param_ctx ret_ctx
      )
  | `Named (i, name, args) ->
      let fixed_args_ctxs = List.map args ~f:fix_quantifiers in
      let fixed_args = List.map fixed_args_ctxs ~f:fst in
      let fixed_ctx =
        List.map fixed_args_ctxs ~f:snd
        |> List.fold ~init:empty_ctx ~f:merge_ctxs
      in
      (`Named(i, name, fixed_args), fixed_ctx)
  | `App(i, f, x) ->
      let (f', f_ctx) = fix_quantifiers f in
      let (x', x_ctx) = fix_quantifiers x in
      ( `App(i, f', x')
      , merge_ctxs f_ctx x_ctx
      )
  | `Lambda(i, param, body) ->
      let (body', ctx) = fix_quantifiers body in
      (`Lambda(i, param, body'), ctx)
  | `Quant q ->
      let (arg', arg_ctx) = fix_quantifiers q.q_arg in
      begin match Map.find arg_ctx.fq_var_of_q q.q_id with
        | None -> (arg', arg_ctx)
        | Some vars ->
            let vars = Set.to_list vars in
            ( List.fold vars ~init:arg' ~f:(fun arg v ->
                  let {v_flag; _} = Util.find_exn arg_ctx.fq_vars_by_id v in
                  `Quant
                    { q with
                      q_var = v
                    ; q_flag = v_flag
                    ; q_arg = arg
                    }
                )
            , List.fold
                  vars
                  ~init:{ arg_ctx with fq_var_of_q = Map.remove arg_ctx.fq_var_of_q q.q_id }
                  ~f:(fun ctx v ->
                      { ctx with
                        fq_var_to_q = Map.remove ctx.fq_var_to_q v
                      ; fq_vars_by_id = Map.remove ctx.fq_vars_by_id v
                      }
                    )
            )
      end
  | `Union (i, row) ->
      let (row', row_ctx) = fix_row_quantifiers row in
      (`Union (i, row'), row_ctx)
  | `Record(i, l, r) ->
      let (rowl, ctxl) = fix_row_quantifiers l in
      let (rowr, ctxr) = fix_row_quantifiers r in
      ( `Record(i, rowl, rowr)
      , merge_ctxs ctxl ctxr
      )
and fix_var_quantifiers v =
  { fq_var_to_q = IntMap.singleton v.v_var_id v.v_q_id
  ; fq_var_of_q = IntMap.singleton v.v_q_id (IntSet.singleton v.v_var_id)
  ; fq_vars_by_id = IntMap.singleton v.v_var_id v
  }
and fix_row_quantifiers: semi_row -> (semi_row * fix_q_ctx) = function
  | `Var v -> (`Var v, fix_var_quantifiers v)
  | `Empty -> (`Empty, empty_ctx)
  | `Extend(lbl, head, tail) ->
      let (head', head_ctx) = fix_quantifiers head in
      let (tail', tail_ctx) = fix_row_quantifiers tail in
      ( `Extend(lbl, head', tail')
      , merge_ctxs head_ctx tail_ctx
      )

let fix_quantifiers t =
  (* Some of the type variables may be bound on the g-node that is at the
   * root; look for any remaining variables and add quantifier nodes with
   * them attached. *)
  let (ty, {fq_vars_by_id; _}) = fix_quantifiers t in
  Map.to_alist fq_vars_by_id
  |> List.map ~f:snd
  |> List.fold
    ~init:ty
    ~f:(fun arg v ->
        `Quant
          { q_id = v.v_q_id
          ; q_var = v.v_var_id
          ; q_flag = v.v_flag
          ; q_arg = arg
          }
      )


let invert_sign = function
  | `Neg -> `Pos
  | `Pos -> `Neg

let sign_flag_to_q sign flag = match sign, flag with
  | `Pos, `Flex -> `All
  | `Pos, `Rigid -> `Exist
  | `Neg, `Flex -> `Exist
  | `Neg, `Rigid -> `All
  | `Neg, `Explicit | `Pos, `Explicit ->
      `All

let rec finish_extract_t: sign -> semi_t -> int Type.t = fun sign -> function
  | `Var v -> Type.Var{ v_info = v.v_var_id; v_var = ivar v.v_var_id }
  | `Visited v -> Type.Var{ v_info = v; v_var = ivar v }
  | `Recur(v, arg) -> Type.Recur {
      mu_info = v;
      mu_var = ivar v;
      mu_body = finish_extract_t sign arg;
    }
  | `Lambda(i, param, body) ->
      Type.TypeLam {
        tl_info = i;
        tl_param = ivar param.v_var_id;
        tl_body = finish_extract_t sign body;
      }
  | `Quant q ->
      Type.Quant
        { q_info = q.q_id
        ; q_quant = sign_flag_to_q sign q.q_flag
        ; q_var = ivar q.q_var
        ; q_body = finish_extract_t sign q.q_arg
        }
  | `Fn (i, param, ret) ->
      Type.Fn
        { fn_info = i
        ; fn_pvar = None
        ; fn_param = finish_extract_t (invert_sign sign) param
        ; fn_ret = finish_extract_t sign ret
        }
  | `Named(i, name, []) ->
      Type.Named {n_info = i; n_name = name}
  | `App(i, f, x) ->
      Type.App {
        app_info = i;
        app_fn = finish_extract_t sign f;
        app_arg = finish_extract_t sign x;
      }
  | `Named (_i, _name, _params) ->
      MuleErr.bug "can't use Named with arguments in desugared ast."
  | `Union(_, row) ->
      Type.Union {u_row = finish_extract_row sign row}
  | `Record(i, rowl, rowr) ->
      Type.Record
        { r_src = ST.Var {v_var = Var.of_string "<unknown>"}
        ; r_info = i
        ; r_types = finish_extract_row sign rowl
        ; r_values = finish_extract_row sign rowr
        }
and finish_extract_row sign row =
  let rec go_field = function
    | `Var _ -> []
    | `Empty -> []
    | `Extend(lbl, head, tail) ->
        (lbl, finish_extract_t sign head) :: go_field tail
  in
  let rec go_var = function
    | `Extend(_, _, tail) -> go_var tail
    | `Empty -> None
    | `Var v -> Some (ivar (v.v_var_id))
  in
  let fields = go_field row in
  let rest = go_var row in

  (* Filter out duplicate field names: *)
  let seen = ref LabelSet.empty in
  let fields = List.filter fields ~f:(fun (l, _) ->
      if Set.mem !seen l then
        false
      else
        (seen := Set.add !seen l; true)
    )
  in

  (* Ensure a consistent ordering: *)
  ( Gensym.gensym ()
  , List.sort fields ~compare:(fun (ll, _) (lr, _) -> Label.compare ll lr)
  , rest
  )

let get_var_type uvar =
  uvar
  |> Normalize.nf
  |> semi_extract_t IntSet.empty
  |> fix_quantifiers
  |> add_rec_binders
  |> finish_extract_t `Pos
  |> Relabel.relabel_type ()
