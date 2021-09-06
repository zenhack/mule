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
  seen: (quant_info, unit DT.t) GT.seen;
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
let rec enumerate_bindings_q emit seen ctx qv =
  let q = Context.read_var ctx Context.quant qv in
  Seen.guard seen.GT.seen_q q.q_id (fun () ->
    enumerate_bindings_ty emit seen ctx (Lazy.force q.q_body);
    Option.iter (maybe_q_target ctx q.q_bound) ~f:(fun q' ->
      emit (`Q qv, q')
    )
  )
and enumerate_bindings_ty emit seen ctx tv =
  let typ = Context.read_var ctx Context.typ tv in
  Seen.guard seen.GT.seen_ty (GT.typ_id typ) (fun () ->
    List.iter (GT.ty_q_kids typ) ~f:(enumerate_bindings_q emit seen ctx);
    match typ with
    | `Free {tv_bound; _} ->
        Option.iter (maybe_q_target ctx tv_bound) ~f:(fun q ->
          emit (`Ty tv, q)
        )
    | _ -> ()
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
  fun ctx qv ->
  let bs = ref [] in
  enumerate_bindings_q (fun b -> bs := b :: !bs) (GT.empty_seen ()) ctx qv;
  {
    bindings = accumulate_bindings !bs;
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

let rec degraph_quant : display_ctx -> GT.quant GT.var -> quant_info =
  fun dc qv ->
    let q = Context.read_var dc.ctx Context.quant qv in
    let child_dc = { dc with parents = Set.add dc.parents q.q_id } in
    Seen.get dc.seen.seen_q q.q_id (fun () ->
      (* TODO FIXME: check for recursive type. *)
      let bound_vars =
        Map.find dc.bindings q.q_id
          |> Option.value ~default:[]
          |> List.map ~f:(degraph_bind_src child_dc)
      in
      let body = degraph_type child_dc (Lazy.force q.q_body) in
      {
        qi_var = Gensym.anon_var (Context.get_ctr dc.ctx);
        qi_quant = bv_to_tmp_quant dc.ctx q.q_bound;
        qi_bound =
          Some
            (maybe_with_recursive child_dc q.q_id
              (List.fold_left
                bound_vars
                ~init:body
                ~f:(fun q_body qi ->
                  DT.Quant {
                    q_info = ();
                    q_quant = qi.qi_quant;
                    q_var = qi.qi_var;
                    q_bound = qi.qi_bound;
                    q_body;
                  }
                )));
      }
    )
and degraph_type : display_ctx -> GT.typ GT.var -> unit DT.t =
  fun dc tv ->
    let ty = Context.read_var dc.ctx Context.typ tv in
    let ty_id = GT.typ_id ty in
    let get_q qv =
      let q = Context.read_var dc.ctx Context.quant qv in
      if Set.mem dc.parents q.q_id then
        DT.Var {
          v_info = ();
          v_src = `Generated;
          v_var = as_recursive_var dc q.q_id;
        }
      else
        begin
          let qi = degraph_quant dc qv in
          match qi.qi_bound with
          | None | Some (DT.Quant _) -> DT.Var {
              v_info = ();
              v_src = `Generated;
              v_var = qi.qi_var;
            }
          (* If there's nothing bound on the q node, just inline it. *)
          | Some t -> t
        end
    in
    Seen.get dc.seen.seen_ty ty_id (fun () ->
      let v = Gensym.anon_var (Context.get_ctr dc.ctx) in
      match ty with
      | `Free _ -> DT.Var {
            v_info = ();
            v_src = `Generated;
            v_var = v;
          }
      | `Ctor (_, ctor) ->
          begin match ctor with
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
          end
      | _ -> failwith "TODO"
    )
and degraph_bind_src : display_ctx -> bind_src -> quant_info =
  fun dc -> function
    | `Q q -> degraph_quant dc q
    | `Ty tv ->
        let ty = Context.read_var dc.ctx Context.typ tv in
        begin match ty with
        | `Free tyvar ->
            begin match degraph_type dc tv with
            | DT.Var {v_var; _} -> {
                  qi_var = v_var;
                  qi_quant = bv_to_tmp_quant dc.ctx (tyvar.tv_bound);
                  qi_bound = None;
                }
            | _ ->
                (* Should never happen; `Free always returns a var. *)
                failwith "Impossible"
            end
        | _ ->
            (* Should never happen; only `Free nodes have binding
               edges. *)
            failwith "Impossible"
        end

let extract_type_ast : Context.t -> GT.quant GT.var -> unit DT.t =
  fun ctx qv ->
  let dc = build_display_ctx ctx qv in
  Option.value_exn (degraph_bind_src dc (`Q qv)).qi_bound
  |> Relabel.relabel_type ()
