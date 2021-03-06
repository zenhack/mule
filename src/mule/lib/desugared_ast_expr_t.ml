open Common_ast
open Desugared_ast_common
module Type_t = Desugared_ast_type_t

type withtype_src =
  [ `Pattern of (Var.t Loc.located * Surface_ast.Type.lt)
  | `WithType of (Surface_ast.Expr.lt * Surface_ast.Type.lt)
  | `RecordVal of (Label.t Loc.located * Surface_ast.Type.lt * Surface_ast.Expr.lt)
  | `Msig
  | `Main
  ]
type partial_lambda_src =
  (* Something that was part of an actually lambda. We do desugaring of
   * currying though, so we keep track of how many arguments have been
   * stripped * off the front via an argument index, and record the pattern
   * corresponding to this argument, and record the depth of the pattern
   * into our argument. *)
  ( int (* Argument index *)
    * Surface_ast.Pattern.lt
    * int (* Pattern depth *)
    * Surface_ast.Expr.lt (* The original lambda. *)
  )

type lam_src =
  [ (* This was a union tag/ctor, but it was wrapped
       in a lambda since ctors have to be fully applied after
       desugaring: *)
    `Ctor of Label.t Loc.located

  | `PartialLambda of partial_lambda_src
  | `Generated
  ]

type match_src =
  [ `PartialLambda of partial_lambda_src
  | `Generated
  ]

type 'i t =
  | Embed of {
      e_path: string;
      e_value: string;
      e_src: Surface_ast.Expr.lt;
    }
  | Import of import
  | Var of {
      v_var : Var.t;
      v_src :
        [ `Generated
        | `Sourced of Var.t Loc.located
        ]
    }
  | Lam of {
      l_param : Var.t;
      l_body : 'i t;
      l_src : lam_src;
    }
  | App of {
      app_fn : 'i t;
      app_arg : 'i t;
    }
  | Record of 'i rec_bind
  | GetField of {
      gf_lbl : Label.t;
      gf_record : 'i t;
    }
  | UpdateType of {
      ut_lbl    : Label.t;
      ut_type   : 'i Type_t.t;
      ut_record : 'i t;
    }
  | UpdateVal of {
      uv_lbl : Label.t;
      uv_val : 'i t;
      uv_record : 'i t;
    }
  | Ctor of {
      c_lbl : Label.t;
      c_arg : 'i t;
    }
  | Match of {
      m_branch : 'i branch;
      m_src : match_src;
    }
  | WithType of {
      wt_src : withtype_src;
      wt_expr : 'i t;
      wt_type : 'i Type_t.t;
    }
  | Let of {
      let_v : Var.t;
      let_e : 'i t;
      let_body : 'i t;
    }
  | LetRec of {
      letrec_binds : 'i rec_bind;
      letrec_body: 'i t;
    }
  | Const of {
      const_val : Const.t;
    }
and 'i branch =
  | BLabel of {
      lm_cases : 'i branch LabelMap.t;
      lm_default : 'i leaf option;
    }
  | BConst of {
      cm_cases : (Const.t, 'i t, Const.comparator_witness) Map.t;
      cm_default: 'i leaf option;
    }
  | BLeaf of 'i leaf
and 'i leaf = {
  lf_var: Var.t option;
  lf_body: 'i t;
}
and 'i rec_bind = {
  rec_vals: (Var.t * 'i Type_t.t option * 'i t) list;
  rec_types: (Var.t * 'i Type_t.t) list list;
}
