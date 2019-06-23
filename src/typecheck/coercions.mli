open Ast.Desugared
open Typecheck_types

open Build_constraint_t

(* Generate coercion types from type annotations.
 *
 * This is based on {MLF-Graph-Infer} section 6, but we do one important
 * thing differently: Instead of *sharing* existential types between the
 * coercion's parameter and result, we map them to flexibly bound bottom
 * nodes in the parameter (as in the paper), but in the result we generate
 * fresh "constant" constructors.
 *
 * The idea is that when we supply a type annotation with an existential
 * in it, we want to *hide* the type from the outside -- this maps closely
 * to sealing in ML module systems. By contrast, the treatment of
 * existentials in the paper is more like "type holes" in some systems --
 * they allow you to specify some of a type annotation, but let the compiler
 * work out the rest. As a concrete example:
 *
 * (fn x. 4) : exist t. t -> t
 *
 * The algorithm in the paper will infer (int -> int), but this code
 * will invent a new constant type t and infer (t -> t).
*)

(* [gen_type cops b_at env sign ty] generates a graphic type based on [ty].
 *
 * - [cops] is used to generate unification constraints.
 * - monomorphic nodes are bound on [b_at].
 * - [env] is a mapping from type variable names to unification variables; free
 *   variables will be replaced with their values in the map. All free variables
 *   _must_ be contained within the map.
 * - [sign] indicates whether we are in positive or negative position. This is
 *   used to determine the binding flag to use when we see a quantifier. [sign]
 *   is flipped each time we go down the parameter side of a function node.
 *
 * The return value is a unification variable for the root of the type.
 *
 * TODO: this probably doesn't belong in coercions per se. It used to just be
 * a helper function for [make_coercion_type], but it's now used elsewhere as
 * well.
 *)
val gen_type
  : constraint_ops
  -> bound_target
  -> u_var VarMap.t
  -> sign
  -> Kind.t Type.t
  -> u_var

(* Actually make the coercion. *)
val make_coercion_type : u_var VarMap.t -> g_node -> 'i Type.t -> constraint_ops -> u_var
