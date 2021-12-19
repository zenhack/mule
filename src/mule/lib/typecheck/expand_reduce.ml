(*
This module contains utility code common to the expand and
beta-reduction parts of the type checker. As discussed in
{Scherer2010}, the process of copying a lambda for the purposes
of beta reduction is very similar to the expand procedure used
in constraint solving.

They are not quite the same, and trying to do this goes badly,
but we *can* factor out some code that the two procedures share
in common. This module contains that common code.
*)

module GT = Graph_types


(* A group of Seen.t used during the copying process. *)
type seen = {
  (* Nodes we have already visited traversing the graph
     downwards. *)
  seen_q: (GT.Ids.Quant.t, GT.quant GT.var) Seen.t;
  seen_ty: (GT.Ids.Type.t, GT.typ GT.var) Seen.t;

  (* Nodes who's status in the constraints interior (ci)
     of the source subgraph is known. Note that this structure's
     lifetime is always bound to a particular invocation
     of the copy logic, so the node whose constraint interior is
     in question is implicit. *)
  seen_ci_g: (GT.Ids.G.t, bool) Seen.t;
  seen_ci_q: (GT.Ids.Quant.t, bool) Seen.t;
}


(* Make an empty [seen] record. *)
let make_seen () = {
  seen_q = Seen.make (module GT.Ids.Quant);
  seen_ty = Seen.make (module GT.Ids.Type);

  seen_ci_g = Seen.make (module GT.Ids.G);
  seen_ci_q = Seen.make (module GT.Ids.Quant);
}

let rec bound_under seen ctx g = function
  | `G g' ->
      let (g_id', g_id) = GT.GNode.(id g', id g) in
      Seen.get seen.seen_ci_g g_id' (fun () ->
        if GT.Ids.G.(g_id' < g_id) then
          (* We're above the target. *)
          false
        else if GT.Ids.G.(g_id' = g_id) then
          true
        else
          begin match GT.GNode.bound g' with
            | None -> false
            | Some v -> bound_under seen ctx g (`G v)
          end
      )
  | `Q qv ->
      let q = Context.read_var ctx Context.quant qv in
      Seen.get seen.seen_ci_q q.q_id (fun () ->
        bound_under seen ctx g
          (Context.read_var ctx Context.bound q.q_bound).b_target
      )
