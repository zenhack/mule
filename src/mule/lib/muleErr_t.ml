open Common_ast

module DT = Desugared_ast_type_t
module DE = Desugared_ast_expr_t

module TT = Typecheck_types_t


module TypePath = struct
  (* A segment in a path through a type. *)
  type seg =
    [ `RowLabel of Label.t
    | `RowTail
    | `Fn of [ `Param | `Result ]
    | `RecordPart of [ `Type | `Value ]
    | `UnionRow
    | `TypeLamBody
    | `Unroll of Typecheck_types_t.u_quant * [ `Left | `Right ]
    ]

  type t = {
    roots: (TT.u_var * TT.u_var);
    segs: seg list;
  }

  let base: TT.u_var -> TT.u_var -> t =
    fun l r -> {
        roots = (l, r);
        segs = [];
      }

  let append: t -> seg -> t =
    fun t seg -> { t with segs = seg :: t.segs }
end

(* A reason for a subtyping constraint. *)
type subtype_reason =
  [ `RecordUpdate of TT.k_var DE.t
  | `TypeAnnotation of  (DE.withtype_src * TT.k_var DT.t)
  | `ApplyFn of (TT.k_var DE.t * TT.k_var DE.t)

  | `Path of [ `Var of Var.t | `Import of Surface_ast.Import.t ] DT.src

  (* No reason given. Eventually this will go away, but for now it exists so
   * we don't have to add reasons everywhere all at once. *)
  | `Unspecified
  ]

type subtype_error = {
  se_sub : int DT.t;
  se_super : int DT.t;
  se_path : TypePath.t;
  se_reason : subtype_reason;
}

type ctor = Typecheck_types_t.u_typeconst
type kind =
  [ `Row
  | `Type
  | `Unknown
  | `Arrow of kind * kind
  ]
type cant_instantiate = {
  ci_info : TT.var_info;
  ci_other:
    [ `Type of int DT.t
    | `Row of int DT.row
    ];
}
type type_error =
  [ `MismatchedCtors of subtype_error
  | `MismatchedKinds of (kind * kind)
  | `OccursCheckKind
  | `CantInstantiate of cant_instantiate
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
