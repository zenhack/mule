open Common_ast

type quantifier = [ `All | `Exist ]

let sexp_of_quantifier = function
  | `All -> Sexp.Atom "all"
  | `Exist -> Sexp.Atom "exist"

type 'i t =
  | Fn of {
      fn_info : 'i;
      fn_pvar : Var.t option;
      fn_param : 'i t;
      fn_ret : 'i t;
    }
  | Recur of {
      mu_info : 'i;
      mu_var : Var.t;
      mu_body : 'i t;
    }
  | Var of {
      v_info : 'i;
      v_var : Var.t;
    }
  | Path of {
      p_info : 'i;
      p_var : Var.t;
      p_lbls : Label.t list;
    }
  | Record of {
      r_info : 'i;
      r_types : 'i row;
      r_values : 'i row;
      r_src : Surface_ast.Type.lt option;
    }
  | Union of {
      u_row : 'i row;
    }
  | Quant of {
      q_info : 'i;
      q_quant : quantifier;
      q_var : Var.t;
      q_body : 'i t;
    }
  | Named of {
      n_info : 'i;
      n_name : Typecheck_types_t.typeconst_name;
    }
  | Opaque of { o_info : 'i }
  | TypeLam of {
      tl_info : 'i;
      tl_param : Var.t;
      tl_body : 'i t;
    }
  | App of {
      app_info : 'i;
      app_fn : 'i t;
      app_arg : 'i t;
    }
and 'i row = {
  row_info: 'i;
  row_fields: (Label.t * 'i t) list;
  row_rest: Var.t option;
}

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
  | Var{v_info; v_var} ->
      if Var.equal v_var old then
        new_
      else
        Var{v_info; v_var}
  | Path{p_info; p_var; p_lbls} ->
      if Var.equal p_var old then
        MuleErr.bug "TODO"
      else
        Path{p_info; p_var; p_lbls}
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
    | Some v when Var.equal v old -> MuleErr.bug "TODO"
    | _ -> row_rest;
}

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
      List ([Atom "."; Var.sexp_of_t p_var] @ List.map p_lbls ~f:Label.sexp_of_t)
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
  | Some v -> Sexp.List (fields @ [Sexp.Atom ("..." ^ Var.to_string v)])
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
  | Path{p_info; p_var; p_lbls} ->
      Path{
        p_info = f p_info;
        p_var;
        p_lbls;
      }
  | Var {v_info; v_var} ->
      Var{v_info = f v_info; v_var}
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
  row_rest;
}

let rec to_string = function
  | Fn {fn_pvar = Some p; fn_param; fn_ret; _} ->
      String.concat [
        "(";
        Var.to_string p;
        " : ";
        to_string fn_param;
        ") -> ";
        to_string fn_ret;
      ]
  | Fn {fn_pvar = None; fn_param; fn_ret; _} ->
      String.concat ["("; to_string fn_param; ") -> "; to_string fn_ret]
  | Recur{mu_var; mu_body; _} -> String.concat [
      "rec ";
      Var.to_string mu_var;
      ". ";
      to_string mu_body;
    ]
  | Var {v_var; _} -> Var.to_string v_var
  | Path {p_var; p_lbls; _} ->
      String.concat ~sep:"." (Var.to_string p_var :: List.map p_lbls ~f:Label.to_string)
  | Record {
      r_types = {row_fields = types; row_rest = types_rest; _};
      r_values = {row_fields = vals; row_rest = vals_rest; _};
      _;
    } ->
      List.concat [
        List.map types ~f:(fun (lbl, ty) -> format_type_member lbl ty);
        begin match types_rest with
          | None -> []
          | Some v -> ["...type " ^ Var.to_string v]
        end;
        List.map vals ~f:(fun (lbl, ty) -> Label.to_string lbl ^ " : " ^ to_string ty);
        begin match vals_rest with
          | None -> []
          | Some v -> ["..." ^ Var.to_string v]
        end;
      ]
      |> String.concat ~sep:", "
      |> (fun s -> "{" ^ s ^ "}")
  | Union{u_row = {row_fields; row_rest; _}} ->
      String.concat ~sep:" | " (
        List.map row_fields ~f:(fun (lbl, ty) ->
          String.concat [
            Label.to_string lbl;
            " (";
            to_string ty;
            ")";
          ]
        )
        @ begin match row_rest with
          | None -> []
          | Some v -> ["..." ^ Var.to_string v]
        end)
  | Quant{q_quant; q_var; q_body; _} ->
      let q = match q_quant with `All -> "all" | `Exist -> "exist" in
      String.concat [
        q;
        " ";
        Var.to_string q_var;
        ". ";
        to_string q_body;
      ]
  | Named {n_name; _} ->
      Typecheck_types_t.string_of_typeconst_name n_name
  | Opaque _ -> "<opaque>"
  | TypeLam _ -> "<type lambda>"
  | App{app_fn; app_arg; _} ->
      String.concat [
        "(";
        to_string app_fn;
        ") ";
        to_string app_arg;
      ]
and format_type_member lbl ty =
  let rec go params = function
    | Recur{mu_var; mu_body; _}
      when String.equal (Var.to_string mu_var) (Label.to_string lbl) ->
        (List.rev params, mu_body)
    | TypeLam{tl_param; tl_body; _} ->
        go (tl_param :: params) tl_body
    | t -> (List.rev params, t)
  in
  let (params, body) = go [] ty in
  String.concat [
    "type ";
    Label.to_string lbl;
    String.concat (List.map params ~f:(fun p -> " " ^ Var.to_string p))
  ] ^ begin match body with
    | Opaque _ -> ""
    | _ -> " = " ^ to_string body
  end

(* Collect the free type variables in a type *)
let rec ftv = function
  | Var {v_var; _} -> VarSet.singleton v_var
  | Path{p_var; _} -> VarSet.singleton p_var

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

  | Opaque _ | Named _ -> VarSet.empty
(*  Like ftv, but for rows: *)
and ftv_row {row_fields; row_rest; _} =
  let rest_ftv = match row_rest with
    | None -> VarSet.empty
    | Some v -> VarSet.singleton v
  in
  List.fold
    row_fields
    ~init:rest_ftv
    ~f:(fun vs (_, t) -> Set.union vs (ftv t))
