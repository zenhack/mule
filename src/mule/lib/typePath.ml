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

let base: TT.u_var -> TT.u_var -> t =
  fun l r -> {
      roots = (l, r);
      segs = [];
    }

let append: t -> seg -> t =
  fun t seg -> { t with segs = seg :: t.segs }
