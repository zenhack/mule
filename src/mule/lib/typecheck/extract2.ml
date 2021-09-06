(* This module is responsible for turning a graphical type
   into a syntactic one.

   We borrow and extend a trick from {QMLF}: the authors observe
   that type variables that are used only once, and are either flexible
   in positive position or rigid in negative position can be inlined,
   reducing the need to use the bounded-quantification syntax.

   Our extension is that, since mule also has existential quantifiers,
   we can use those for rigid variables in positive position or flexible
   variables in negative position -- so the bounded quantification syntax
   is only necessary when the type is truly inexpressible as a tree.

   The logic for this is surprisingly complex; there is a lot of bookkeeping
   to manage both because of the trick described above, and just because
   we're turning a possibly-cyclic graph into a syntactic tree, so this
   involves a lot more than just walking over and converting everything.

   Notably:

   - The trick above requires us to compute refcounts for the nodes.
   - We have to catch recursive types and add rec. binders.
*)

module GT = Graph_types
module DT = Desugared_ast_type_t
module Var = Common_ast.Var

(* The source of a binding edge. *)
type bind_src =
    [ `Q of GT.quant GT.var
    | `Ty of GT.typ GT.var
    ]

(* A binding edge, as (source, target). Note that for our purposes in this
   module, we don't need to process q-nodes that are themselves bound on
   g-nodes, we can assume the target is always q-node. *)
type binding = (bind_src * GT.Ids.Quant.t)

(* Information about a type needed for it to be used as a bound.
   TODO: move this to DT? *)
type quant_info = {
  (* Variable name to which to bind the type in the quantifier *)
  qi_var: Var.t;

  (* Quantifier with which to bind bs_var *)
  qi_quant: DT.quantifier;

  (* The actual bound on the quantifier. *)
  qi_bound: unit DT.t option;
}

(* State & info bundle needed to display a type. *)
type display_ctx = {
  ctx: Context.t; (* General type context, for reading variables *)

  (* Map from each q node to nodes bound on it. *)
  bindings: bind_src list GT.Ids.QuantMap.t;

  (* For q-nodes we have determined are recursive types, this contains
     variable names to use for those types. *)
  recursive_vars: Var.t GT.Ids.QuantMap.t ref;

  (* List of q-nodes that are structural parents of the node we are currently
     examining. Used to catch recursive types. *)
  parents: GT.Ids.QuantSet.t;

  (* memoized results for each node. *)
  seen: (quant_info, quant_info) GT.seen;
}

(**** Helpers for collecting binding edges. ***)

(* Return the quant for the variable's b_target, or None if it
   is bound on a G-node *)
let maybe_q_target ctx bv =
  let {GT.b_target; _} = Context.read_var ctx Context.bound bv in
  match b_target with
  | `G _ -> None
  | `Q qv -> Some (Context.read_var ctx Context.quant qv).q_id

(* enumerate_binidngs_* walk over the type graph, and (lazily)
   return a list of binding edges that target q-nodes. Each
   binding edge is a pair (node, target), where target is the
   GT.quant on which node is bound, and node is
   [ `Q quant var | `Ty typ var ]. *)
let rec enumerate_bindings_q seen ctx qv =
  let q = Context.read_var ctx Context.quant qv in
  Seen.get seen.GT.seen_q q.q_id (fun () ->
    let body = enumerate_bindings_ty seen ctx (Lazy.force q.q_body) in
    match maybe_q_target ctx q.q_bound with
    | None -> body
    | Some q' -> lazy ((`Q qv, q') :: Lazy.force body)
  )
and enumerate_bindings_ty seen ctx tv =
  let typ = Context.read_var ctx Context.typ tv in
  Seen.get seen.GT.seen_ty (GT.typ_id typ) (fun () ->
    let kids = lazy (
      GT.ty_q_kids typ
        |> List.map ~f:(fun q ->
            Lazy.force (enumerate_bindings_q seen ctx q)
          )
        |> List.concat
      )
    in
    match typ with
    | `Free {tv_bound; _} ->
        begin match maybe_q_target ctx tv_bound with
        | None -> kids
        | Some q -> lazy ((`Ty tv, q) :: Lazy.force kids)
        end
    | _ -> kids
  )

(* Turn the list of bindings returned by enumerate_bindings_* into a map
   from q -> nodes bound on q. *)
let accumulate_bindings : binding list -> bind_src list GT.Ids.QuantMap.t =
  fun binds ->
    List.fold
      binds
      ~init:(Map.empty (module GT.Ids.Quant))
      ~f:(fun m (child, q_id) ->
        Map.update m q_id ~f:(fun v ->
          child :: Option.value v ~default:[]
        )
      )

(* Generate the initial display context for printing the node. *)
let build_display_ctx : Context.t -> GT.quant GT.var -> display_ctx =
  fun ctx qv -> {
      bindings =
        enumerate_bindings_q (GT.empty_seen ()) ctx qv
        |> Lazy.force
        |> accumulate_bindings;
      ctx;
      recursive_vars = ref (Map.empty (module GT.Ids.Quant));
      parents = Set.empty (module GT.Ids.Quant);
      seen = GT.empty_seen ();
    }

(* Mark the node as recursive if it isn't already, and return the
   variable name to use for it. *)
let as_recursive_var : display_ctx -> GT.Ids.Quant.t -> Var.t =
  fun dc qid -> match Map.find !(dc.recursive_vars) qid with
    | Some v -> v
    | None ->
        begin
          let v = Gensym.anon_var (Context.get_ctr dc.ctx) in
          dc.recursive_vars := Map.set ~key:qid ~data:v !(dc.recursive_vars);
          v
        end
(* If the node is known to be a recursive type, wrap the type it in a rec.
   binder, with the appropriate variable name. Otherwise just return it as-is. *)
let maybe_with_recursive : display_ctx -> GT.Ids.Quant.t -> unit DT.t -> unit DT.t =
  fun dc qid body -> match Map.find !(dc.recursive_vars) qid with
    | None -> body
    | Some v -> DT.Recur {
        mu_info = ();
        mu_var = v;
        mu_body = body;
      }

(* convert a binding to a quantifier, based on its flag. This assumes the quantifier
   will be in positive position.

   The way we use it this is not actually true, but we go back over the type in a
   separate pass, fixing up the quantifiers based on their actual position. *)
let bv_to_tmp_quant ctx bv =
  match (Context.read_var ctx Context.bound bv).b_flag with
  | `Flex -> `All
  | `Rigid -> `Exist
  | `Explicit -> failwith "TODO"

let rec degraph_bind_src : display_ctx -> bind_src -> quant_info =
  fun dc -> function
    | `Q qv ->
        let q = Context.read_var dc.ctx Context.quant qv in
        let degraph_child = degraph_bind_src { dc with parents = Set.add dc.parents q.q_id } in
        Seen.get dc.seen.seen_q q.q_id (fun () ->
          (* TODO FIXME: check for recursive type. *)
          let bound_vars =
            Map.find dc.bindings q.q_id
              |> Option.value ~default:[]
              |> List.map ~f:degraph_child
          in
          let body = degraph_child (`Ty (Lazy.force q.q_body)) in
          {
            qi_var = Gensym.anon_var (Context.get_ctr dc.ctx);
            qi_quant = bv_to_tmp_quant dc.ctx q.q_bound;
            qi_bound = Some (List.fold_left
              bound_vars
              ~init:(Option.value body.qi_bound ~default:(DT.Var {
                  v_info = ();
                  v_src = `Generated;
                  v_var = body.qi_var;
                }))
              ~f:(fun q_body qi ->
                DT.Quant {
                  q_info = ();
                  q_quant = qi.qi_quant;
                  q_var = qi.qi_var;
                  q_bound = qi.qi_bound;
                  q_body;
                }
              ));
          }
        )
    | `Ty tv ->
        let ty = Context.read_var dc.ctx Context.typ tv in
        let ty_id = GT.typ_id ty in
        Seen.get dc.seen.seen_ty ty_id (fun () ->
          let get_q q = DT.Var {
              v_info = ();
              v_src = `Generated;
              v_var = (degraph_bind_src dc (`Q q)).qi_var;
            }
          in
          let v = Gensym.anon_var (Context.get_ctr dc.ctx) in
          match ty with
          | `Free tyvar -> {
                qi_var = v;
                qi_quant = bv_to_tmp_quant dc.ctx (tyvar.tv_bound);
                qi_bound = None;
              }
          | `Ctor (_, ctor) -> {
                qi_var = v;
                qi_quant = `All; (* Doesn't matter; node is inert. *)
                qi_bound =
                  Some begin match ctor with
                    | `Type(`Fn(p, r)) -> DT.Fn {
                        fn_info = ();
                        fn_pvar = None;
                        fn_param = get_q p;
                        fn_ret = get_q r;
                      }
                    | `Type(`Const c) -> DT.Named {
                        n_info = ();
                        n_name = match c with
                          | `Text -> `Text
                          | `Int -> `Int
                          | `Char -> `Char
                      }
                    | _ -> failwith "TODO"
                  end;
              }
          | _ -> failwith "TODO"
        )

let extract_type_ast : Context.t -> GT.quant GT.var -> unit DT.t =
  fun ctx qv ->
  let dc = build_display_ctx ctx qv in
  Option.value_exn (degraph_bind_src dc (`Q qv)).qi_bound
