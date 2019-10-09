
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
  | EVar of 'm var_
  | ELam of ('m, 'm pattern_ * 'm exp_) Wm.t
  | EApp of ('m, 'm exp_ * 'm exp_) Wm.t
  | EWithType of ('m, 'm exp_ * 'm typ_) Wm.t
  [@@deriving sexp]
and 'm exp_ = ('m, 'm exp) Wm.t
  [@@deriving sexp]
and 'm typ =
  | TVar of 'm var_
  | TFn of ('m, 'm typ_ * 'm typ_) Wm.t
  [@@deriving sexp]
and 'm typ_ = ('m, 'm typ) Wm.t
  [@@deriving sexp]

module Pattern = struct
  module T = struct
    type 'a t = 'a pattern
    [@@deriving sexp]
    let apply_kids p ~f:_ = p
  end
  include T
  include Collapse.Make(T)

  let apply_types p ~f:_ = p
end

module Type = struct
  module T = struct
    type 'a t = 'a typ
    [@@deriving sexp]
    let apply_kids ty ~f = match ty with
      | TVar _ -> ty
      | TFn m -> TFn (Wm.map_data m ~f:(fun (param, ret) ->
          ( Wm.map_data ~f param
          , Wm.map_data ~f ret
          )
        ))
  end
  include T
  include Collapse.Make(T)

  let subst ty ~var ~replacement = bottom_up ty ~f:(function
      | TVar {data; _} when data.v_id = var.v_id -> replacement
      | ty -> ty
    )
end

module Exp = struct
  module T = struct
    type 'a t = 'a exp
    [@@deriving sexp]
    let apply_kids e ~f = match e with
      | EVar _ -> e
      | ELam m -> ELam (Wm.map_data m ~f:(fun (pat, body) ->
          (pat, Wm.map_data body ~f)
        ))
      | EApp m ->
          EApp (Wm.map_data m ~f:(fun (fn, arg) ->
              ( Wm.map_data ~f fn
              , Wm.map_data ~f arg
              )
            ))
      | EWithType m ->
          EWithType (
            Wm.map_data m ~f:(fun (e, ty) -> (Wm.map_data e ~f, ty))
          )
  end
  include T
  include Collapse.Make(T)

  let apply_patterns ~f = bottom_up ~f:(function
      | ELam m -> ELam (Wm.map_data m ~f:(fun (pat, body) ->
          (Wm.map_data pat ~f, body)
        ))
      | e -> e
    )

  let apply_types e ~f =
    apply_patterns e ~f:(Pattern.apply_types ~f)
    |>  bottom_up ~f:(function
        | EWithType m -> EWithType (
            Wm.map_data m ~f:(fun (e, ty) -> (e, f ty))
          )
        | e -> e
      )

  let subst e ~var ~replacement =
    bottom_up e ~f:(function
      | EVar {data; _} when data.v_id = var.v_id -> replacement
      | e -> e
    )

  let subst_type e ~var ~replacement =
    apply_types e ~f:(Wm.map_data ~f:(Type.bottom_up ~f:(Type.subst ~var ~replacement)))
end
