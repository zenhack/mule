
module C = Constraint_t
module GT = Graph_types
module Util = Typecheck_util

let solve_has_kind ctx t k =
  let k' = Infer_kind.infer_kind ctx t in
  Unify.unify_kind ctx k k'

let solve_kind_constraint ctx = function
  | `UnifyKind c ->
      Unify.unify_kind ctx c.C.unify_kind_super c.C.unify_kind_sub
  | `HasKind c ->
      solve_has_kind ctx c.C.has_kind_type c.C.has_kind_kind

let solve_unify_constraint ctx c =
  Unify.unify_quant ctx c c.C.unify_super c.C.unify_sub
  (* TODO: rebind etc. *)

let propagate_instance_constraint ctx inst_c =
  let qv = Expand.expand ctx
    ~g:inst_c.C.inst_super
    ~at:(Util.g_for_q ctx inst_c.C.inst_sub)
    ~inst_c
  in
  Context.constrain ctx (`Unify C.{
      unify_why = `InstanceRoot inst_c;
      unify_sub = inst_c.inst_sub;
      unify_super = qv;
    })

module OrganizedConstraints = struct
  (* Organizes a list of constraints for processing *)

  type kind_constraint =
    [ `UnifyKind of C.unify_kind_constraint
    | `HasKind of C.has_kind_constraint
    ]

  type t = {
    kind: kind_constraint list;
    unify: C.unify_constraint list;
    instance: C.instance_constraint list;
  }

  let empty = { kind = []; unify = []; instance = []; }

  let rec of_list acc = function
    | [] ->
        acc
    | (`UnifyKind x :: xs) ->
        of_list { acc with kind = `UnifyKind x :: acc.kind } xs
    | (`HasKind x :: xs) ->
        of_list { acc with kind = `HasKind x :: acc.kind } xs
    | (`Unify x :: xs) ->
        of_list { acc with unify = x :: acc.unify } xs
    | (`Instance x :: xs) ->
        of_list { acc with instance = x :: acc.instance } xs
  let of_list =
    of_list { kind = []; unify = []; instance = [] }
  let of_list ctx cs =
    let cs = of_list cs in
    { cs with instance = Sort_instance_constraints.sort ctx cs.instance }

  let append x y =
      { kind = x.kind @ y.kind
      ; unify = x.unify @ y.unify
      ; instance = x.instance @ y.instance
      }

  let pop cs = match cs with
    | { kind = k :: ks; _} -> Some (`Kind k, { cs with kind = ks })
    | { unify = u :: us; _} -> Some (`Unify u, { cs with unify = us })
    | { instance = i :: is; _} -> Some (`Instance i, { cs with instance = is })
    | { kind = []; unify = []; instance = [] } -> None
end

let solve ctx =
  let module OCS = OrganizedConstraints in
  let render () =
    if Config.render_constraint_graph () then
      Context.DebugGraph.dump ctx
  in
  let rec go ocs =
    render ();
    let ocs' = OCS.append (OCS.of_list ctx (Context.take_constraints ctx)) ocs in
    match OCS.pop ocs' with
    | None -> ()
    | Some (`Kind c, cs) ->
        solve_kind_constraint ctx c; go cs
    | Some (`Instance c, cs) ->
        propagate_instance_constraint ctx c; go cs
    | Some (`Unify c, cs) ->
        solve_unify_constraint ctx c; go cs
    | Some _ ->
        failwith "TODO: other constraints"
  in
  go OCS.empty
