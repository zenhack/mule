module GT = Graph_types
module DE = Desugared_ast_expr_t

(* Reason for an instance constraint *)
type instance_why =
  [ (* In a function application, the function's parameter type must be an
       instance of the type of its argument. *)
    `ParamArg of
      ( unit DE.t (* Function *)
      * unit DE.t (* Argument *)
      )
  | (* If in expresssion is being applied, it must be a function. *)
      `FnApply of (unit DE.t) (* The expression for the function *)

    (* Use of a let-bound variable: *)
  | `VarUse of DE.var_src
  ]

(* Reason for a unification constraint *)
type unify_why =
  [ (* This was an instance constraint, demoted after expansion: *)
    `Instance of instance_why

    (* Use of a lambda bound variable: *)
  | `VarUse of (DE.var_src * DE.lam_src)
  ]

(* A constraint to be solved *)
type constr =
  [ `Unify of
      ( GT.quant GT.var
        * GT.quant GT.var
        * unify_why
      )
  | `Instance of
      ( GT.g_node
        * GT.quant GT.var
        * instance_why
      )
  ]

type instance_constraint = {
  inst_why: instance_why;
  inst_super: GT.g_node GT.var;
  inst_sub: GT.typ GT.var;
}

type unify_constraint = {
  unify_why: unify_why;

  (* Note: the names `super` and `sub` suggest a subtyping relationship,
     but unification constraints are symmetric. We do this so that when
     we lower an instance constraint to a unification constraint, it is
     easy to keep track of which variable was on which side of the instance
     constraint, for the purposes of error reporting. *)
  unify_super: GT.typ GT.var;
  unify_sub: GT.typ GT.var;
}


(* For tracking the environment while building constraints: *)

type val_var =
  [ `LambdaBound of GT.quant GT.var
  | `LetBound of GT.g_node GT.var
  ]

type env = {
  vals: val_var VarMap.t;
}
