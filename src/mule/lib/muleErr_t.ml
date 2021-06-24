open Common_ast

module DT = Desugared_ast_type_t
module DE = Desugared_ast_expr_t

module GT = Graph_types

type kind =
  [ `Row
  | `Type
  | `Unknown
  | `Arrow of kind * kind
  ]

type unify_error_cause =
  [ `MismatchedCtors of GT.ctor * GT.ctor
  | `CantInstantiate of [ `Rigid | `Explicit ] * GT.typ
  ]

type unify_error = {
  ue_constraint: Constraint_t.unify_constraint;
  ue_cause: unify_error_cause;
}

type type_error =
  [ `UnifyFailed of unify_error
  | `MismatchedKinds of (kind * kind)
  | `MismatchedGuards
  | `OccursCheckKind
  ]

type path_error =  {
  pe_path: string;
  pe_loc: Loc.t;
  pe_problem :
    [ `AbsoluteEmbed
    | `IllegalChar of char
    | `BadPathPart of string
    ]
}

type t =
  [ `UnboundVar of Var.t Loc.located

  (* We hit int/text etc. literals in the same match expression as patterns
   * that match sum types. This is conceptually a type error, but it's easier
   * to have a separate variant for it since it's caught earlier in the
   * pipeline. *)
  | `MatchDesugarMismatch of Surface_ast.Pattern.lt

  | `LazyLoop

  | `TypeError of type_error
  | `DuplicateFields of [`Type|`Value] * (Label.t * Loc.t list) list
  | `UnreachableCases of (Surface_ast.Pattern.lt * Surface_ast.Expr.lt) list
  | `MalformedType of string
  | `IncompletePattern
  | `IllegalAnnotatedType of Surface_ast.Type.lt
  | `PathError of path_error
  | `Bug of string
  | `NotImplemented of string
  ]

exception MuleExn of t
