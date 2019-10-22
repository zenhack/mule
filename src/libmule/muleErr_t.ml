open Common_ast

type op = [ `Graft | `Merge | `Raise | `Weaken ]
type ctor =
  [ `Named of string
  | `Extend of Label.t
  ]
type kind =
  [ `Row
  | `Type
  | `Unknown
  | `Arrow of kind * kind
  ]
type type_error =
  [ `MismatchedCtors of (ctor * ctor)
  | `MismatchedKinds of (kind * kind)
  | `OccursCheckKind
  | `PermissionErr of op
  ]

type path_error =  {
  pe_path: string;
  pe_problem :
    [ `AbsoluteEmbed
    | `IllegalChar of char
    | `BadPathPart of string
    ]
}

type t =
  [ `UnboundVar of Var.t

  (* We hit int/text etc. literals in the same match expression as patterns
   * that match sum types. This is conceptually a type error, but it's easier
   * to have a separate variant for it since it's caught earlier in the
   * pipeline. *)
  | `MatchDesugarMismatch

  | `LazyLoop

  | `TypeError of type_error
  | `DuplicateFields of (Label.t list)
  | `UnreachableCases of (Surface_ast.Pattern.t * Surface_ast.Expr.t) list
  | `EmptyMatch
  | `MalformedType of string
  | `IncompletePattern of Surface_ast.Pattern.t
  | `IllegalAnnotatedType of Surface_ast.Type.t
  | `PathError of path_error
  | `Bug of string
  ]

exception MuleExn of t
