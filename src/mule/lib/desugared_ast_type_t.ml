
open Common_ast

type quantifier = [ `All | `Exist ]

let sexp_of_quantifier = function
  | `All -> Sexp.Atom "all"
  | `Exist -> Sexp.Atom "exist"

type var_src =
  [ `Generated
  | `Sourced of Var.t Loc.located
  ]

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
      v_src : var_src;
    }
  | Path of {
      p_info : 'i;
      p_var : Var.t;
      p_src : var_src;
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
  row_rest: 'i t option;
}
