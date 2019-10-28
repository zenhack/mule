open Common_ast

type var = {
  sv_var : Var.t;
  sv_loc : Loc.t;
}
[@@deriving sexp_of]

type label = {
  sl_label : Label.t;
  sl_loc : Loc.t;
}
[@@deriving sexp_of]

let var_of_label {sl_label; sl_loc} = {
  sv_var = var_of_label sl_label;
  sv_loc = sl_loc;
}

module Type = struct
  type quantifier = [ `All | `Exist ]
  [@@deriving sexp_of]

  type t =
    | Fn of  {
        fn_param : t;
        fn_ret : t;
        fn_loc : Loc.t;
      }
    | Quant of {
        q_quant : quantifier;
        q_vars : var list;
        q_body : t;
        q_loc : Loc.t;
      }
    | Recur of {
        recur_var : var;
        recur_body : t;
        recur_loc : Loc.t;
      }
    | Var of {
        v_var : var;
      }
    | Record of {
        r_items : record_item list;
        r_loc : Loc.t;
      }
    | Ctor of {
        c_lbl : label;
      }
    | App of {
        app_fn : t;
        app_arg : t;
        app_loc : Loc.t;
      }
    | Union of {
        u_l : t;
        u_r : t;
        u_loc : Loc.t;
      }
    | RowRest of {
        rr_var : var;
        rr_loc : Loc.t;
      }
    | Annotated of {
        anno_var : var;
        anno_ty : t;
        anno_loc: Loc.t;
      }
    | Path of {
        p_var : var;
        p_lbls : label list;
      }
    | Import of {
        i_path : string;
        i_from : string;
        i_loc : Loc.t;
      }
  [@@deriving sexp_of]

  and record_item =
    | Field of (label * t)
    | Type of (label * var list * t option)
    | Rest of var
  [@@deriving sexp_of]

  let t_loc = function
    | Fn{fn_loc; _} -> fn_loc
    | Quant{q_loc; _} -> q_loc
    | Recur{recur_loc; _} -> recur_loc
    | Var{v_var = {sv_loc; _}} -> sv_loc
    | Record{r_loc; _} -> r_loc
    | Ctor{c_lbl = {sl_loc; _}} -> sl_loc
    | App{app_loc; _} -> app_loc
    | Union{u_loc; _} -> u_loc
    | RowRest{rr_loc; _} -> rr_loc
    | Annotated{anno_loc; _} -> anno_loc
    | Path{p_var; p_lbls} ->
        List.fold
          p_lbls
          ~init:p_var.sv_loc
          ~f:(fun loc {sl_loc; _} -> Loc.spanning loc sl_loc)
    | Import{i_loc; _} -> i_loc
end

module Pattern = struct
  type t =
    | Ctor of {
        c_lbl : label;
        c_arg : t;
        c_loc : Loc.t;
      }
    | Var of {
        v_var : var;
        v_type : Type.t option;
        v_loc : Loc.t;
      }
    | Wild of {w_loc : Loc.t}
    | Const of {
        const_val : Const.t;
        const_loc : Loc.t;
      }
  [@@deriving sexp_of]

  let t_loc = function
    | Ctor{c_loc; _} -> c_loc
    | Var{v_loc; _} -> v_loc
    | Wild{w_loc; _} -> w_loc
    | Const{const_loc; _} -> const_loc
end

module Expr = struct
  type t =
    | App of {
        app_fn : t;
        app_arg : t;
        app_loc : Loc.t;
      }
    | Lam of {
        lam_params : Pattern.t list;
        lam_body : t;
        lam_loc : Loc.t;
      }
    | Var of {
        v_var : var;
      }
    | Record of {
        r_fields : field list;
        r_loc : Loc.t;
      }
    | GetField of {
        gf_arg : t;
        gf_lbl : label;
        gf_loc : Loc.t;
      }
    | Ctor of {c_lbl : label}
    | Update of {
        up_arg : t;
        up_fields : field list;
        up_loc : Loc.t;
      }
    | Match of {
        match_arg : t;
        match_cases : (Pattern.t * t) list;
        match_loc : Loc.t;
      }
    | Let of {
        let_binds : binding list;
        let_body : t;
        let_loc : Loc.t;
      }
    | WithType of {
        wt_term : t;
        wt_type : Type.t;
        wt_loc : Loc.t;
      }
    | Const of {
        const_val : Const.t;
        const_loc : Loc.t;
      }
    | Import of
        { i_path : string
        ; i_from : string
        ; i_loc : Loc.t;
        }
    | Embed of {
        e_path : string;
        e_from : string;
        e_loc : Loc.t;
      }
  [@@deriving sexp_of]
  and binding =
    [ `BindType of var * var list * Type.t
    | `BindVal of Pattern.t * t
    ]
  [@@deriving sexp_of]
  and field =
    [ `Value of
        ( label
          * Type.t option
          * t
        )
    | `Type of
        ( label
          * var list
          * Type.t
        )
    ]
  [@@deriving sexp_of]

  let t_loc = function
    | App{app_loc; _} -> app_loc
    | Lam{lam_loc; _} -> lam_loc
    | Var{v_var = {sv_loc; _}} -> sv_loc
    | Record{r_loc; _} -> r_loc
    | GetField{gf_loc; _} -> gf_loc
    | Ctor{c_lbl = {sl_loc; _}} -> sl_loc
    | Update{up_loc; _} -> up_loc
    | Match{match_loc; _} -> match_loc
    | Let{let_loc; _} -> let_loc
    | WithType{wt_loc; _} -> wt_loc
    | Const{const_loc; _} -> const_loc
    | Import{i_loc; _} -> i_loc
    | Embed{e_loc; _} -> e_loc
end
