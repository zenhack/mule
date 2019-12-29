module TT = Typecheck_types_t

(* A segment in a path through a type. *)
type seg =
  [ `RowLabel of Common_ast.Label.t
  | `RowTail
  | `Fn of [ `Param | `Result ]
  | `RecordPart of [ `Type | `Value ]
  | `UnionRow
  | `TypeLamBody
  | `Unroll of TT.u_quant * [ `Left | `Right ]
  ]

type t = {
  roots: (TT.u_var * TT.u_var);
  segs: seg list;
}

let sexp_of_seg = function
  | `RowLabel l -> Sexp.List [Sexp.Atom "RowLabel"; Common_ast.Label.sexp_of_t l]
  | `RowTail -> Sexp.Atom "RowTail";
  | `Fn `Param -> Sexp.List [Sexp.Atom "Fn"; Sexp.Atom "Param"]
  | `Fn `Result -> Sexp.List [Sexp.Atom "Fn"; Sexp.Atom "Result"]
  | `RecordPart `Type -> Sexp.List [Sexp.Atom "RecordPart"; Sexp.Atom "Type"]
  | `RecordPart `Value -> Sexp.List [Sexp.Atom "RecordPart"; Sexp.Atom "Value"]
  | `UnionRow -> Sexp.Atom "UnionRow"
  | `TypeLamBody -> Sexp.Atom "TypeLamBody"
  | `Unroll(_, side) -> Sexp.List [
      Sexp.Atom "Unroll";
      Sexp.Atom "_";
      Sexp.Atom begin match side with
        | `Left -> "Left"
        | `Right -> "Right"
      end;
    ]

let base: TT.u_var -> TT.u_var -> t =
  fun l r -> {
      roots = (l, r);
      segs = [];
    }

let append: t -> seg -> t =
  fun t seg -> { t with segs = seg :: t.segs }
