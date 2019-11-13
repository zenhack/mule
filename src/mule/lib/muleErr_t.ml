open Common_ast

type ctor = Typecheck_types_t.u_typeconst
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
  | `CantInstantiate
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
  ]

exception MuleExn of t
