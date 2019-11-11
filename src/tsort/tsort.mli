
include module type of Tsort_t

(* Topologically sort the graph specified by [nodes] and [edges].
 *
 * The graph may have cycles. In the return value, nodes forming
 * a cycle will be grouped together. If there are no cycles,
 * the return value will contain only one-element lists.
 *
 * The result will be sorted with nodes that have no outgoing
 * edges first, followed by nodes that point to them.
 *)
val sort
  : 'n comparator
  -> nodes:('n list)
  -> edges:('n edge list)
  -> 'n list list
