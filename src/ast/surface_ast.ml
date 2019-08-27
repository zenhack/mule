open Common_ast

(* During desugaring, we construct some "intermediate" surface-level nodes.
 * These don't always correspond to exact source locations, so we have a more
 * general datatype that we use to describe the "origin" of a source level
 * ast node. *)
type origin =
  [ `SrcLoc of Loc.t
  ]
  [@@deriving sexp_of]

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
        q_loc : origin;
      }
    | Recur of {
        recur_var : Var.t;
        recur_body : t;
      }
    | Var of {v_var : Var.t}
    | Record of {
        r_items : record_item list;
      }
    | Ctor of {
        c_lbl : Label.t;
        c_loc : origin;
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
        anno_loc : origin;
      }
    | Path of {
        p_var : Var.t;
        p_lbls : Label.t list;
        p_loc : origin;
      }
    | Import of {
        i_path : string;
        i_loc : origin;
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
    | App of {
        app_fn : t;
        app_arg : t;
      }
    | Lam of {
        lam_params : Pattern.t list;
        lam_body : t;
      }
    | Var of {v_var : Var.t}
    | Record of {r_fields : field list}
    | GetField of {
        gf_arg : t;
        gf_lbl : Label.t;
      }
    | Ctor of {c_lbl : Label.t}
    | Update of {
        up_arg : t;
        up_fields : field list;
      }
    | Match of {
        match_arg : t;
        match_cases : (Pattern.t * t) list;
      }
    | Let of {
        let_binds : binding list;
        let_body : t;
      }
    | WithType of {
        wt_term : t;
        wt_type : Type.t;
      }
    | Const of {const_val : Const.t}
    | Import of
        { i_path : string
        ; i_loc : origin;
        }
    | Embed of {
        e_path : string;
        e_loc : origin;
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
    | `Type of
        ( Label.t
          * Var.t list
          * Type.t
        )
    ]
  [@@deriving sexp_of]
end
