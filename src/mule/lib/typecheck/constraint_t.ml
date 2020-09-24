open Common_ast
module GT = Graph_types
module DE = Desugared_ast_expr_t

(* Reason for an `Instance constraint *)
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

  (* Record field access -- argument must be a record with the given field. *)
  | `GetField of (Label.t * unit DE.t)

  (* Record update -- argument must be a record. *)
  | `RecordUpdate of unit DE.t
  ]

(* Reason for a `Unify constraint *)
type unify_why =
  [ (* This was an instance constraint, demoted after expansion: *)
    `Instance of instance_why

  (* Use of a lambda bound variable: *)
  | `VarUse of (DE.var_src * DE.lam_src)
  ]

(* Reason for a `UnifyKind constraint. *)
type unify_kind_why =
  [ (* Type was is an argument to a primitive constructor. The argument to `CtorArg
     * denotes a "path" for the argument in the primitive constructor. e.g. `Fn `Param
     * indicates that the constrained kind was in the argument position of a ->
     * constructor. *)
    | `CtorArg of [ `Fn of [ `Param | `Result ] ]
  ]

type instance_constraint = {
  inst_why: instance_why;
  inst_super: GT.g_node;
  inst_sub: GT.quant GT.var;
}

type unify_constraint = {
  unify_why: unify_why;

  (* Note: the names `super` and `sub` suggest a subtyping relationship,
     but unification constraints are symmetric. We do this so that when
     we lower an instance constraint to a unification constraint, it is
     easy to keep track of which variable was on which side of the instance
     constraint, for the purposes of error reporting. *)
  unify_super: GT.quant GT.var;
  unify_sub: GT.quant GT.var;
}

type unify_kind_constraint = {
  unify_kind_why: unify_kind_why;

  (* Note: kind constraints are actually symmetric, but the sub/super
     terminology is nice for humans, as it makes it clear which kind was
     the "constraint" and which was supposed to be "constrained." *)
  unify_kind_super: GT.kind GT.var;
  unify_kind_sub: GT.kind GT.var;
}

(* A constraint to be solved *)
type constr =
  [ `Unify of unify_constraint
  | `Instance of instance_constraint
  | `UnifyKind of unify_kind_constraint
  ]

(* For tracking the environment while building constraints: *)

type val_var =
  [ `LambdaBound of
      ( GT.quant GT.var
        * DE.lam_src
      )
  | `LetBound of GT.g_node
  ]

type polarity = [ `Pos | `Neg ]

type type_var = (polarity -> GT.bound_target -> GT.typ GT.var)

type env = {
  vals: val_var VarMap.t;
  types: type_var VarMap.t;
}
