
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
end

let solve ctx =
  let ocs = OrganizedConstraints.of_list (Context.get_constraints ctx) in
  List.iter ocs.kind ~f:(solve_kind_constraint ctx)
