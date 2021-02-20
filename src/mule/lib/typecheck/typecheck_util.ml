module GT = Graph_types

let rec g_for_q : Context.t -> GT.quant GT.var -> GT.g_node =
  fun ctx qv ->
    let q = Context.read_var ctx Context.quant qv in
    let b = Context.read_var ctx Context.bound q.GT.q_bound in
    match b.GT.b_target with
      | `G g -> g
      | `Q qv' -> g_for_q ctx qv'
