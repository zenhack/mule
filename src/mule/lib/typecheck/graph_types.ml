(* Internal representation of types, used by the type checker.

   This is based on the graph presentation of MLF. The reader is assumed
   to be familiar with that body of work. Otherwise, see {Scherer 2010}
   for an introduction.
*)

open Common_ast

module type Id = sig
  (* An opaque identifier *)
  type t

  val compare : t -> t -> int
  val fresh : Gensym.counter -> t
  val to_string : t -> string
end

module IdImpl : Id = struct
  include Int
  let fresh ctr = Gensym.gensym ctr
end

module Ids = struct
  module G : Id = IdImpl
  module Type : Id = IdImpl
  module Kind : Id = IdImpl
  module Quant : Id = IdImpl
end

type 'a var = 'a Union_find.rref

module GNode : sig
  type 'a t

  val id : 'a t -> Ids.G.t
  val make_child : 'a t -> 'a -> 'a t
  val make_root : Gensym.counter -> 'a -> 'a t

  val get : 'a t -> 'a
end = struct
  type 'a t = {
    g_id: Ids.G.t;
    g_bound: 'a t option; (* None means this is the root. *)
    g_ctr: Gensym.counter;
    g_value: 'a;
  }

  let id g = g.g_id
  let make_child g value = {
    g_id = Ids.G.fresh g.g_ctr;
    g_bound = Some g;
    g_ctr = g.g_ctr;
    g_value = value;
  }

  let make_root ctr value = {
    g_id = Ids.G.fresh ctr;
    g_bound = None;
    g_ctr = ctr;
    g_value = value;
  }

  let get g = g.g_value
end

type guard =
  [ `Free
  | `Guarded
  | `Unguarded
  ]

type prekind =
  [ `Free of Ids.Kind.t
  | `Row
  | `Type
  | `Arrow of kind var * kind var
  ]
and kind = {
  k_prekind: prekind var;
  k_guard: guard var;
}

type typ =
  [ `Free of tyvar
  | `Ctor of ctor
  | `Lambda of (quant var * quant var)
  | `Apply of (quant var * quant var)

  (* `Posion is not a real type; it is used as part of our error handling
     strategy. TODO: write docs about error handling *)
  | `Poison
  ]
and tyvar = {
  tv_id: Ids.Type.t;
  tv_bound: bound var;
  tv_kind: kind var;
}
and ctor =
  [ `Type of type_ctor
  | `Row of row_ctor
  ]
and type_ctor =
  [ `Fn of (quant var * quant var)
  | `Record of (quant var * quant var)
  | `Union of (quant var)
  | `Const of const
  ]
and row_ctor =
  [ `Extend of (Label.t * quant var * quant var)
  | `Empty
  ]
and const = [ `Text | `Int | `Char ]
and quant = {
  q_id: Ids.Quant.t;
  q_bound: bound var;
  q_body: typ var Lazy.t;
}
and bound_target =
  [ `G of g_node
  | `Q of quant var
  ]
and g_node = quant var Lazy.t GNode.t
and bound = {
  b_target: bound_target;
  b_flag: bound_flag;
}
and bound_flag =
  [ `Flex | `Rigid | `Explicit ]
