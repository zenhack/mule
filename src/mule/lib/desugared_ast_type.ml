open Common_ast
open Desugared_ast_common
include Desugared_ast_type_t

let rec subst old new_ ty = match ty with
  | Fn {fn_info; fn_pvar = Some v; fn_param; fn_ret} when Var.equal v old ->
      Fn {
        fn_info;
        fn_pvar = Some v;
        fn_param = subst old new_ fn_param;
        fn_ret;
      }
  | Fn {fn_info; fn_pvar; fn_param; fn_ret} ->
      Fn {
        fn_info;
        fn_pvar;
        fn_param = subst old new_ fn_param;
        fn_ret = subst old new_ fn_ret;
      }
  | Recur{mu_info; mu_var; mu_body} ->
      if Var.equal mu_var old then
        Recur{mu_info; mu_var; mu_body}
      else
        Recur{mu_info; mu_var; mu_body = subst old new_ mu_body}
  | Var{v_var; _} ->
      if Var.equal v_var old then
        new_
      else
        ty
  | Path{p_var; _} ->
      begin match p_var with
        | `Var v when Var.equal v old ->
            MuleErr.bug "TODO"
        | _ ->
            ty
      end
  | Record {r_info; r_types; r_values; r_src} ->
      Record {
        r_info;
        r_src;
        r_types = subst_row old new_ r_types;
        r_values = subst_row old new_ r_values;
      }
  | Union {u_row} ->
      Union { u_row = subst_row old new_ u_row }
  | Quant{q_info; q_quant; q_var; q_body} ->
      if Var.equal q_var old then
        Quant {q_info; q_quant; q_var; q_body}
      else
        Quant{q_info; q_quant; q_var; q_body = subst old new_ q_body}
  | Named _ -> ty
  | Opaque _ -> ty
  | TypeLam{tl_info; tl_param; tl_body} ->
      if Var.equal tl_param old then
        TypeLam{tl_info; tl_param; tl_body}
      else
        TypeLam{tl_info; tl_param; tl_body = subst old new_ tl_body}
  | App{app_info; app_fn; app_arg} ->
      App {
        app_info;
        app_fn = subst old new_ app_fn;
        app_arg = subst old new_ app_arg;
      }
and subst_row old new_ {row_info; row_fields = ls; row_rest} = {
  row_info;
  row_fields = List.map ls ~f:(fun (l, field) -> (l, subst old new_ field));
  row_rest =
    match row_rest with
    | Some t -> Some(subst old new_ t)
    | None -> None
}


let sexp_of_path_start = function
  | `Import i -> sexp_of_import i
  | `Var v -> Var.sexp_of_t v

let rec sexp_of_t: 'i t -> Sexp.t = function
  | Fn{fn_pvar = None; fn_param; fn_ret; _} ->
      Sexp.List [sexp_of_t fn_param; Sexp.Atom "->"; sexp_of_t fn_ret]
  | Fn{fn_pvar = Some v; fn_param; fn_ret; _} ->
      Sexp.List [
        Sexp.List [ Var.sexp_of_t v; Sexp.Atom ":"; sexp_of_t fn_param ];
        Sexp.Atom "->";
        sexp_of_t fn_ret;
      ]
  | Recur{mu_var = v; mu_body = body; _} ->
      Sexp.List [Sexp.Atom "rec"; Var.sexp_of_t v; sexp_of_t body]
  | Var{v_var; _} ->
      Var.sexp_of_t v_var
  | Path{p_var; p_lbls; _} -> Sexp.(
      List ([
        Atom ".";
        sexp_of_path_start p_var;
      ] @ List.map p_lbls ~f:Label.sexp_of_t)
    )
  | Record { r_info = _; r_src = _; r_types; r_values } -> Sexp.(
      List [
        Atom "record";
        List [Atom "types"; sexp_of_row r_types];
        List [Atom "values"; sexp_of_row r_values];
      ]
    )
  | Union {u_row} ->
      Sexp.(List [Atom "union"; sexp_of_row u_row])
  | Quant {q_quant; q_var; q_body; _} ->
      Sexp.List [
        sexp_of_quantifier q_quant;
        Sexp.Atom(Var.to_string q_var);
        sexp_of_t q_body;
      ]
  | TypeLam{tl_param; tl_body; _} ->
      Sexp.List [
        Sexp.Atom "lam";
        Sexp.Atom(Var.to_string tl_param);
        sexp_of_t tl_body;
      ]
  | Named{n_name; _} -> Typecheck_types_t.sexp_of_typeconst_name n_name
  | Opaque _ -> Sexp.Atom "<opaque>"
  | App{app_fn; app_arg; _} -> Sexp.List [
      sexp_of_t app_fn;
      sexp_of_t app_arg;
    ]
and sexp_of_row {row_fields; row_rest; _} =
  let fields =
    List.map row_fields ~f:(fun (l, t) ->
      Sexp.List [Label.sexp_of_t l; sexp_of_t t]
    )
  in
  match row_rest with
  | Some t -> Sexp.List (fields @ [Sexp.List [Sexp.Atom "..."; sexp_of_t t]])
  | None -> Sexp.List fields

let get_info = function
  | Fn{fn_info; _} -> fn_info
  | Recur{mu_info; _} -> mu_info
  | Var{v_info; _} -> v_info
  | Path{p_info; _} -> p_info
  | Record{r_info; _} -> r_info
  | Union{u_row = {row_info; _}} -> row_info
  | Quant{q_info; _} -> q_info
  | Named{n_info; _} -> n_info
  | Opaque {o_info; _} -> o_info
  | TypeLam{tl_info; _} -> tl_info
  | App{app_info; _} -> app_info

let rec map ty ~f = match ty with
  | Opaque {o_info} -> Opaque { o_info = f o_info }
  | Named{n_info; n_name} ->
      Named{n_info = f n_info; n_name}
  | Fn{fn_info; fn_pvar; fn_param; fn_ret} ->
      Fn {
        fn_info = f fn_info;
        fn_pvar;
        fn_param = map fn_param ~f;
        fn_ret = map fn_ret ~f;
      }
  | Recur{ mu_info; mu_var; mu_body } ->
      Recur {
        mu_info = f mu_info;
        mu_var;
        mu_body = map mu_body ~f;
      }
  | Path{p_info; p_var; p_lbls; p_src} ->
      Path{
        p_info = f p_info;
        p_var;
        p_lbls;
        p_src;
      }
  | Var {v_info; v_var; v_src} ->
      Var{v_info = f v_info; v_var; v_src}
  | Record {r_info; r_types; r_values; r_src} ->
      Record {
        r_info = f r_info;
        r_src;
        r_types = map_row r_types ~f;
        r_values = map_row r_values ~f;
      }
  | Union {u_row} ->
      Union {u_row = map_row u_row ~f}
  | Quant {q_info; q_quant; q_var; q_body} ->
      Quant {
        q_info = f q_info;
        q_quant;
        q_var;
        q_body = map q_body ~f;
      }
  | TypeLam{tl_info; tl_param; tl_body} ->
      TypeLam {
        tl_info = f tl_info;
        tl_param;
        tl_body = map tl_body ~f;
      }
  | App{app_info; app_fn; app_arg} ->
      App {
        app_info = f app_info;
        app_fn = map app_fn ~f;
        app_arg = map app_arg ~f;
      }
and map_row {row_info; row_fields; row_rest} ~f = {
  row_info = f row_info;
  row_fields = List.map row_fields ~f:(fun(l, t) -> (l, map t ~f));
  row_rest = Option.map row_rest ~f:(map ~f);
}

let pretty_import {i_orig_path; _} =
  PP.(group (string "import" ^/^ text i_orig_path))

let pretty_path_root = function
  | `Var v -> Var.pretty v
  | `Import i -> pretty_import i

let rec pretty_t = function
  | Fn {fn_pvar; fn_param; fn_ret; _} ->
      PP.(
        let param = pretty_t fn_param in
        let param =
          match fn_pvar with
          | None -> param
          | Some v -> Var.pretty v ^/^ colon ^/^ group param
        in
        let param = group (parens param) in
        group (param ^/^ string "->" ^/^ group (pretty_t fn_ret))
      )
  | Recur{mu_var; mu_body; _} ->
      PP.binder "rec" [Var.pretty mu_var] (pretty_t mu_body)
  | Var{v_var; _} ->
      Var.pretty v_var;
  | Path {p_var; p_lbls; _} ->
      PP.(
        (pretty_path_root p_var
         :: List.map p_lbls ~f:(fun l -> string (Label.to_string l))
        )
        |> separate dot
      )
  | Record {
      r_types = {row_fields = types; row_rest = types_rest; _};
      r_values = {row_fields = vals; row_rest = vals_rest; _};
      _;
    } ->
      List.concat [
        List.map types ~f:(fun (lbl, ty) -> pretty_type_member lbl ty);
        begin match types_rest with
          | None -> []
          | Some t -> [PP.(string "...type" ^/^ pretty_t t)]
        end;
        List.map vals ~f:(fun (lbl, ty) ->
          PP.(group (group (Label.pretty lbl ^/^ colon) ^/^ indent (pretty_t ty)))
        );
        begin match vals_rest with
          | None -> []
          | Some t -> [PP.(string "..." ^^ pretty_t t)]
        end;
      ]
      |> PP.opt_fst PPrint.comma
      |> PP.braces
  | Union{u_row = {row_fields; row_rest; _}} ->
      List.map row_fields ~f:(fun (lbl, ty) ->
        PP.(
          Label.pretty lbl ^/^ parens (pretty_t ty)
        )
      )
      @ begin match row_rest with
        | None -> []
        | Some t -> [PP.(string "..." ^^ pretty_t t)]
      end
      |> PP.(opt_fst (break 1 ^^ bar))
  | Quant{q_quant; q_var; q_body; _} ->
      pretty_quant q_quant q_var q_body
  | Named {n_name; _} ->
      Typecheck_types_t.string_of_typeconst_name n_name
      |> PP.string
  | Opaque _ -> PP.string "<opaque>"
  | TypeLam _ -> PP.string "<type lambda>"
  | App{app_fn; app_arg; _} ->
      PP.(parens (group (pretty_t app_fn)) ^/^ indent (pretty_t app_arg))
and pretty_quant quant var body =
  let rec go vars = function
    | Quant{q_quant; q_var; q_body; _} when Poly.equal quant q_quant ->
        go (q_var :: vars) q_body
    | body ->
        (List.rev vars, body)
  in
  let q = match quant with
    | `All -> "all"
    | `Exist -> "exist"
  in
  let vars, body = go [var] body in
  PP.binder
    q
    (List.map vars ~f:Var.pretty)
    (pretty_t body)
and pretty_type_member lbl ty =
  let rec go params = function
    | Recur{mu_var; mu_body; _}
      when String.equal (Var.to_string mu_var) (Label.to_string lbl) ->
        (List.rev params, mu_body)
    | TypeLam{tl_param; tl_body; _} ->
        go (tl_param :: params) tl_body
    | t -> (List.rev params, t)
  in
  let (params, body) = go [] ty in
  PP.(group (
      group (
        string "type"
        ^/^
        separate
          (break 1)
          (Label.pretty lbl :: List.map params ~f:Var.pretty)
      )
      ^^
      begin match body with
        | Opaque _ -> empty
        | _ -> break 1 ^^ string "=" ^/^ group (pretty_t body)
      end
    ))

let to_string ty =
  let buf = Buffer.create 1 in
  PP.(ToBuffer.pretty 1.0 80 buf (indent (pretty_t ty)));
  Buffer.contents buf

let rec apply_to_kids t ~f = match t with
  | Var _ | Path _ | Named _ | Opaque _ -> t
  | Fn {fn_info; fn_pvar; fn_param; fn_ret} -> Fn {
      fn_info;
      fn_pvar;
      fn_param = f fn_param;
      fn_ret = f fn_ret;
    }
  | Recur {mu_info; mu_var; mu_body} ->
      Recur{mu_info; mu_var; mu_body = f mu_body}
  | Record {r_info; r_types; r_values; r_src} ->
      Record {
        r_src;
        r_info;
        r_types = apply_to_row r_types ~f;
        r_values = apply_to_row r_values ~f;
      }
  | Union {u_row} -> Union {
      u_row = apply_to_row u_row ~f;
    }
  | Quant{q_info; q_quant; q_var; q_body} ->
      Quant {
        q_info;
        q_quant;
        q_var;
        q_body = f q_body;
      }
  | TypeLam{tl_info; tl_param; tl_body} ->
      TypeLam {tl_info; tl_param; tl_body = f tl_body}
  | App{app_info; app_fn; app_arg} ->
      App {
        app_info;
        app_fn = f app_fn;
        app_arg = f app_arg;
      }
and apply_to_row {row_info; row_fields; row_rest} ~f = {
  row_info;
  row_fields = List.map row_fields ~f:(fun (l, t) -> (l, f t));
  row_rest;
}

(* Collect the free type variables in a type *)
let rec ftv = function
  | Var {v_var; _} -> Set.singleton (module Var) v_var
  | Path{p_var = `Var v; _} -> Set.singleton (module Var) v
  | Path{p_var = `Import _; _} -> Set.empty (module Var)

  | TypeLam {tl_param; tl_body; _} -> Set.remove (ftv tl_body) tl_param
  | Quant   {q_var;    q_body;  _} -> Set.remove (ftv  q_body) q_var
  | Recur   {mu_var;   mu_body; _} -> Set.remove (ftv mu_body) mu_var

  | Fn {fn_pvar = None; fn_param; fn_ret; _} ->
      Set.union (ftv fn_param) (ftv fn_ret)
  | Fn {fn_pvar = Some v; fn_param; fn_ret; _} ->
      Set.union (ftv fn_param) (Set.remove (ftv fn_ret) v)

  | Record {r_types; r_values; _} ->
      Set.union (ftv_row r_types) (ftv_row r_values)
  | Union {u_row} -> ftv_row u_row

  | App {app_fn; app_arg; _} -> Set.union (ftv app_fn) (ftv app_arg)

  | Opaque _ | Named _ -> Set.empty (module Var)
(*  Like ftv, but for rows: *)
and ftv_row {row_fields; row_rest; _} =
  let rest_ftv = match row_rest with
    | None -> Set.empty (module Var)
    | Some t -> ftv t
  in
  List.fold
    row_fields
    ~init:rest_ftv
    ~f:(fun vs (_, t) -> Set.union vs (ftv t))
