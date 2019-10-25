
module Wm = With_meta

type var = {
  v_id : int;
  v_name : string;
}
[@@deriving sexp]

type 'm var_ = ('m, var) Wm.t
[@@deriving sexp]

type 'm pattern =
  | PVar of var
[@@deriving sexp]
type 'm pattern_ = ('m, 'm pattern) Wm.t
[@@deriving sexp]

type 'm exp =
  | EVar of var
  | ELam of ('m pattern_ * 'm exp_)
  | EApp of ('m exp_ * 'm exp_)
  | EWithType of ('m exp_ * 'm typ_)
  | EConst of Common_ast.Const.t
[@@deriving sexp]
and 'm exp_ = ('m, 'm exp) Wm.t
[@@deriving sexp]
and 'm typ =
  | TVar of var
  | TFn of ('m typ_ * 'm typ_)
  | TQuant of ([`All|`Exist] * 'm var_ * 'm typ_)
[@@deriving sexp]
and 'm typ_ = ('m, 'm typ) Wm.t
[@@deriving sexp]

type 'cmp rename_env = {
  re_terms: (string, var, 'cmp) Map.t;
  re_types: (string, var, 'cmp) Map.t;
}

module Pattern = struct
  module T = struct
    type 'a t = 'a pattern
    [@@deriving sexp]
    let apply_kids p ~f:_ = p
  end
  include T
  include Collapse.Make(T)

  let apply_types p ~f:_ = p

  (* Assign new v_id's to each variable in the pattern, and return a pair
   * of (new_pattern, new_env), where new_env has an updated env_terms. *)
  let rebind env = function
    | PVar {v_name; _} ->
        let var = {v_name; v_id = Gensym.gensym () } in
        ( PVar var
        , { env with re_terms = Map.set env.re_terms ~key:v_name ~data:var }
        )
end

module Type = struct
  module T = struct
    type 'a t = 'a typ
    [@@deriving sexp]
    let apply_kids ty ~f = match ty with
      | TVar _ -> ty
      | TFn (param, ret) -> TFn
            ( Wm.map_data ~f param
            , Wm.map_data ~f ret
            )
      | TQuant (q, v, body) ->
          TQuant(q, v, Wm.map_data ~f body)
  end
  include T
  include Collapse.Make(T)

  let subst ty ~var ~replacement = bottom_up ty ~f:(function
      | TVar data when data.v_id = var.v_id -> replacement
      | ty -> ty
    )

  (* Populate the v_ids of variables in the type for the first time. This allows us to
   * in future uses ignore the possibility of shadowing; each variable has a v_id which
   * is shared only when the variables are truely the same, not when the names merely
   * collide. *)
  let rec rebind env ty = match ty with
    | TVar var ->
        begin match Map.find env.re_types var.v_name with
          | None -> MuleErr.throw (`UnboundVar (Common_ast.Var.of_string var.v_name))
          | Some var' -> TVar var'
        end
    | TQuant(q, {data; meta}, body) ->
        let var = {
          v_name = data.v_name;
          v_id = Gensym.gensym ();
        }
        in
        TQuant
          ( q
          , Wm.{data = var; meta}
          , Wm.map_data
              ~f:(rebind
                  { env with
                    re_types = Map.set env.re_types ~key:var.v_name ~data:var
                  }
              )
              body
          )
    | _ ->
        apply_kids ty ~f:(rebind env)
end

module Exp = struct
  module T = struct
    type 'a t = 'a exp
    [@@deriving sexp]
    let apply_kids e ~f = match e with
      | EVar _ | EConst _ -> e
      | ELam (pat, body) -> ELam (pat, Wm.map_data body ~f)
      | EApp (fn, arg) ->
          EApp
            ( Wm.map_data ~f fn
            , Wm.map_data ~f arg
            )
      | EWithType (e, ty) ->
          EWithType (Wm.map_data e ~f, ty)
  end
  include T
  include Collapse.Make(T)

  let apply_patterns ~f = bottom_up ~f:(function
      | ELam (pat, body) -> ELam (Wm.map_data pat ~f, body)
      | e -> e
    )

  let apply_types e ~f =
    apply_patterns e ~f:(Pattern.apply_types ~f)
    |>  bottom_up ~f:(function
      | EWithType (e, ty) -> EWithType (e, f ty)
      | e -> e
    )

  let subst e ~var ~replacement =
    bottom_up e ~f:(function
      | EVar data when data.v_id = var.v_id -> replacement
      | e -> e
    )

  let subst_type e ~var ~replacement =
    apply_types e ~f:(Wm.map_data ~f:(Type.bottom_up ~f:(Type.subst ~var ~replacement)))

  (* See [Type.rebind] *)
  let rec rebind env = function
    | EVar var ->
        begin match Map.find env.re_terms var.v_name with
          | None -> MuleErr.throw (`UnboundVar (Common_ast.Var.of_string var.v_name))
          | Some var' -> EVar var'
        end
    | ELam(pat, body) ->
        let pat' = Wm.map_data pat ~f:(Pattern.rebind env) in
        let _, env' = pat'.data in
        let pat' = Wm.map_data pat' ~f:fst in
        ELam(pat', Wm.map_data body ~f:(rebind env'))
    | e ->
        apply_kids e ~f:(rebind env)
end
