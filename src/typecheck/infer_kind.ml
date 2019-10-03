open Desugared_ast
open Typecheck_types
open Types

let rec extract: u_kind -> Kind.maybe_kind = function
  | `Free _ -> `Unknown
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow
        ( extract (UnionFind.get x)
        , extract (UnionFind.get y)
        )

let rec occurs_check: reason -> int -> u_kind -> unit =
  fun reason n -> function
    | `Free m when n = m ->
        MuleErr.throw (`TypeError (reason, `OccursCheckKind))
    | `Free _ | `Type | `Row -> ()
    | `Arrow(x, y) ->
        occurs_check (`Cascade(reason, 1)) n (UnionFind.get x);
        occurs_check (`Cascade(reason, 2)) n (UnionFind.get y)

let rec unify reason l r = match l, r with
  | `Free n, _ -> occurs_check reason n r; r
  | _, `Free n -> occurs_check reason n l; l
  | `Type, `Type -> `Type
  | `Row, `Row -> `Row
  | `Arrow(x, y), `Arrow(x', y') ->
      UnionFind.merge (unify (`Cascade (reason, 1))) x x';
      UnionFind.merge (unify (`Cascade (reason, 2))) y y';
      `Arrow(x, y)

  | _ ->
      MuleErr.throw
        (`TypeError
           ( reason
           , `MismatchedKinds(extract l, extract r)
           )
        )
