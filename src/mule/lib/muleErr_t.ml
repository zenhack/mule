open Common_ast

(* A segment in a path through a type. See the disucssion for the `Cascade
 * variant of [subtype_reason] *)
type type_path =
  [ `RowLabel of Label.t
  | `RowTail
  | `Fn of [ `Param | `Result ]
  | `RecordPart of [ `Type | `Value ]
  | `UnionRow
  | `TypeLamBody
  ]

(* A reason for a subtyping constraint. *)
type subtype_reason =
  [ (* This subtyping constraint is a result of another subtyping constraint.
     * It checks if some smaller part of a type matches. The path describes
     * how we got here from the parent constraint. *)
    `Cascaded of (subtype_reason * type_path)

  (* No reason given. Eventually this will go away, but for now it exists so
   * we don't have to add reasons everywhere all at once. *)
  | `Unspecified
  ]

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
