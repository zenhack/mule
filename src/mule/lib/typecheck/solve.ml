
module C = Constraint_t

let solve_has_kind ctx t k =
  let k' = Infer_kind.infer_kind ctx t in
  Unify.unify_kind ctx k k'

let solve_kind_constraint ctx = function
  | `UnifyKind c ->
      Unify.unify_kind ctx c.C.unify_kind_super c.C.unify_kind_sub
  | `HasKind c ->
      solve_has_kind ctx c.C.has_kind_type c.C.has_kind_kind

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
  let rec go ocs =
    match OCS.pop ocs with
    | None -> ()
    | Some (`Kind c, cs) ->
        solve_kind_constraint ctx c;
        let ocs' = OCS.append (OCS.of_list ctx (Context.take_constraints ctx)) cs in
        go ocs'
    | Some _ ->
        failwith "TODO: other constraints"
  in
  go (OCS.of_list ctx (Context.take_constraints ctx))
