open Common_ast

module Type = struct
  type quantifier = [ `All | `Exist ]
  [@@deriving sexp_of]

  type t =
    | Fn of  {
        fn_param : t;
        fn_ret : t;
      }
    | Quant of {
        q_quant : quantifier;
        q_vars : Var.t list;
        q_body : t;
      }
    | Recur of {
        recur_var : Var.t;
        recur_body : t;
      }
    | Var of {v_var : Var.t}
    | Record of {
        record_items : record_item list;
      }
    | Ctor of {
        c_lbl : Label.t;
        c_loc : Loc.t;
      }
    | App of {
        app_fn : t;
        app_arg : t;
      }
    | Union of {
        u_l : t;
        u_r : t;
      }
    | RowRest of {
        rr_var : Var.t;
      }
    | Annotated of {
        anno_var : Var.t;
        anno_ty : t;
        anno_loc : Loc.t;
      }
    | Path of {
        p_var : Var.t;
        p_lbls : Label.t list;
        p_loc : Loc.t;
      }
    | Import of {
        i_path : string;
        i_loc : Loc.t;
      }
  [@@deriving sexp_of]

  and record_item =
    | Field of (Label.t * t)
    | Type of (Label.t * Var.t list * t option)
    | Rest of Var.t
  [@@deriving sexp_of]
end

module Pattern = struct
  type t =
    | Ctor of {
        c_lbl : Label.t;
        c_arg : t;
      }
    | Var of {
        v_var : Var.t;
        v_type : Type.t option;
      }
    | Wild
    | Const of {
        const_val : Const.t;
      }
  [@@deriving sexp_of]
end

module Expr = struct
  type t =
    | App of (t * t)
    | Lam of (Pattern.t list * t)
    | Var of Var.t
    | Record of field list
    | GetField of (t * Label.t)
    | Ctor of Label.t
    | Update of (t * field list)
    | Match of (t * (Pattern.t * t) list)
    | Let of (binding list * t)
    | WithType of (t * Type.t)
    | Const of Const.t
    | Import of
        { i_path : string
        ; i_loc : Loc.t
        }
    | Embed of {
        e_path : string;
        e_loc : Loc.t;
      }
  [@@deriving sexp_of]
  and binding =
    [ `BindType of Var.t * Var.t list * Type.t
    | `BindVal of Pattern.t * t
    ]
  [@@deriving sexp_of]
  and field =
    [ `Value of
        ( Label.t
          * Type.t option
          * t
        )
    | `Type of (Label.t * Var.t list * Type.t)
    ]
  [@@deriving sexp_of]
end
