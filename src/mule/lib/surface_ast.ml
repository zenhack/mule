open Common_ast

type var = Var.t Loc.located
[@@deriving sexp_of]
type label = Label.t Loc.located
[@@deriving sexp_of]

let var_of_label = Loc.map ~f:var_of_label

module Import = struct
  type t = {
    i_path: string Loc.located;
    i_from: string;
  }
  [@@deriving sexp_of]

  type lt = t Loc.located
  [@@deriving sexp_of]
end

module Type = struct
  type quantifier = [ `All | `Exist ]
  [@@deriving sexp_of]

  type lt = t Loc.located
  and t =
    | Fn of  {
        fn_param : lt;
        fn_ret : lt;
      }
    | Quant of {
        q_quant : quantifier Loc.located;
        q_vars : (var * lt option) list;
        q_body : lt;
      }
    | Recur of {
        recur_var : var;
        recur_body : lt;
      }
    | Var of {
        v_var : var;
      }
    | Record of {
        r_items : record_item Loc.located list;
      }
    | Ctor of {
        c_lbl : label;
      }
    | App of {
        app_fn : lt;
        app_arg : lt;
      }
    | Union of {
        u_l : lt;
        u_r : lt;
      }
    | RowRest of lt
    | Annotated of {
        anno_var : var;
        anno_ty : lt;
      }
    | Path of {
        p_var : [ `Var of var | `Import of Import.t Loc.located ];
        p_lbls : label NonEmpty.t;
      }
    | Import of Import.t
  [@@deriving sexp_of]

  and record_item =
    | Field of (label * lt)
    | Type of (label * var list * lt option)
    | Rest of lt
  [@@deriving sexp_of]
end

module Pattern = struct
  type lt = t Loc.located
  and t =
    | Ctor of {
        c_lbl : label;
        c_arg : lt;
      }
    | Var of {
        v_var : var;
        v_type : Type.lt option;
      }
    | Wild
    | Const of {
        const_val : Const.t;
      }
  [@@deriving sexp_of]
end

module Expr = struct
  type lt = t Loc.located
  and t =
    | App of {
        app_fn : lt;
        app_arg : lt;
      }
    | Lam of {
        lam_params : Pattern.lt list;
        lam_body : lt;
      }
    | Var of {
        v_var : var;
      }
    | Record of {
        r_fields : field Loc.located list;
      }
    | List of {l_elts : lt list}
    | GetField of {
        gf_arg : lt;
        gf_lbl : label;
      }
    | Ctor of {c_lbl : label}
    | Update of {
        up_arg : lt;
        up_fields : field Loc.located list;
      }
    | Match of {
        match_arg : lt;
        match_cases : (Pattern.lt * lt) list;
      }
    | Let of {
        let_binds : binding Loc.located list;
        let_body : lt;
      }
    | WithType of {
        wt_term : lt;
        wt_type : Type.lt;
      }
    | Const of {
        const_val : Const.t;
      }
    | Import of Import.t
    | Embed of {
        e_path : string;
        e_from : string;
      }
    | Unquote of lt
    | UnquoteSplice of lt
    | Quote of lt
  [@@deriving sexp_of]
  and binding =
    [ `BindType of var * var list * Type.lt
    | `BindVal of Pattern.lt * lt
    ]
  [@@deriving sexp_of]
  and field =
    [ `Value of
        ( label
          * Type.lt option
          * lt
        )
    | `Type of
        ( label
          * var list
          * Type.lt
        )
    ]
  [@@deriving sexp_of]
end

module Module = struct
  type t = {
    path : string;
    expr : Expr.t;
    typ : Type.t option;
  }
  [@@deriving sexp_of]
end
