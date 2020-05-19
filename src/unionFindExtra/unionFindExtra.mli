
(* Unify two variables, given a function to merge their values. The variables
 * will not appear merged until the function returns.
 *
 * union_with is reentrancy-safe, in that no invariants are broken by passing a
 * variable to merge that is in use by an existing call to merge (higher up
 * in the stack), but note that the final value will follow a "last update
 * wins" rule. It is *not* concurrency safe.
 *
 * If the merge function throws an exception, the variables are not unified.
 *)
val union_with : f:('a -> 'a -> 'a) -> 'a UnionFind.elem -> 'a UnionFind.elem -> unit
