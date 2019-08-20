open Ast.Desugared
open Typecheck_types

let rec extract: u_kind -> Kind.maybe_kind = function
  | `Free _ -> `Unknown
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow
        ( extract (UnionFind.get x)
        , extract (UnionFind.get y)
        )

let rec occurs_check: int -> u_kind -> unit =
  fun n -> function
    | `Free m when n = m ->
        MuleErr.(throw (TypeError OccursCheckKind))
    | `Free _ | `Type | `Row -> ()
    | `Arrow(x, y) ->
        occurs_check n (UnionFind.get x);
        occurs_check n (UnionFind.get y)

let rec unify l r = match l, r with
  | `Free n, _ -> occurs_check n r; r
  | _, `Free n -> occurs_check n l; l
  | `Type, `Type -> `Type
  | `Row, `Row -> `Row
  | `Arrow(x, y), `Arrow(x', y') ->
      UnionFind.merge unify x x';
      UnionFind.merge unify y y';
      `Arrow(x, y)

  | _ ->
      MuleErr.(
        throw (TypeError (MismatchedKinds(extract l, extract r)))
      )
