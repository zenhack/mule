(* Internal representation of types, used by the type checker.

   This is based on the graph presentation of MLF. The reader is assumed
   to be familiar with that body of work. Otherwise, see {Scherer 2010}
   for an introduction.
*)

open Common_ast

module type Id = sig
  (* An opaque identifier *)
  include Comparable.S

  val fresh : Gensym.counter -> t
  val to_string : t -> string
  val to_int : t -> int

  val equal : t -> t -> bool
  val t_of_sexp : Sexp.t -> t
  val sexp_of_t : t -> Sexp.t

  val min : t -> t -> t
  val max : t -> t -> t

  val (<) : t -> t -> bool
  val (>) : t -> t -> bool
  val (>=) : t -> t -> bool
  val (<=) : t -> t -> bool
  val (=) : t -> t -> bool
end

module IdImpl : Id = struct
  include Int
  let fresh ctr = Gensym.gensym ctr
  let to_int n = n
end

module Ids = struct
  module G : Id = IdImpl
  module Type : Id = IdImpl
  module Kind : Id = IdImpl
  module Quant : Id = IdImpl

  module GMap = MapSet.MkMap(G)
  module TypeMap = MapSet.MkMap(Type)
  module KindMap = MapSet.MkMap(Kind)
  module QuantMap = MapSet.MkMap(Quant)

  module GSet = MapSet.MkSet(G)
  module TypeSet = MapSet.MkSet(Type)
  module KindSet = MapSet.MkSet(Kind)
  module QuantSet = MapSet.MkSet(Quant)
end

type 'a var = 'a Union_find.rref

module GNode : sig
  type 'a t

  val id : 'a t -> Ids.G.t
  val bound : 'a t -> 'a t option
  val get : 'a t -> 'a

  val make_child : 'a t -> 'a -> 'a t
  val make_root : Gensym.counter -> 'a -> 'a t
end = struct
  type 'a t = {
    g_id: Ids.G.t;
    g_bound: 'a t option; (* None means this is the root. *)
    g_ctr: Gensym.counter;
    g_value: 'a;
  }

  let id g = g.g_id
  let bound g = g.g_bound
  let get g = g.g_value

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
end

type guard =
  [ `Free
  | `Guarded
  | `Unguarded

  | `Poison
  ]

type prekind =
  [ `Free of Ids.Kind.t
  | `Row
  | `Type
  | `Arrow of kind var * kind var
  | `Poison
  ]
and kind = {
  k_prekind: prekind var;
  k_guard: guard var;
}

type typ =
  [ `Free of tyvar
  | `Ctor of (Ids.Type.t * ctor)
  | `Lambda of (Ids.Type.t * quant var * quant var)
  | `Apply of (Ids.Type.t * quant var * quant var)

  (* `Posion is not a real type; it is used as part of our error handling
     strategy. TODO: write docs about error handling *)
  | `Poison of Ids.Type.t
  ]
and tyvar = {
  tv_id: Ids.Type.t;
  tv_merged: Ids.TypeSet.t;
  tv_bound: bound var;
  tv_kind: kind var;
}
and ctor =
  [ `Type of type_ctor
  | `Row of row_ctor
  ]
and type_ctor =
  [ `Fn of (quant var * quant var)
  | `Record of
        ( quant var (* types *)
          * quant var (* values *)
        )
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
  q_merged: Ids.QuantSet.t;
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

let typ_id = function
  | `Free {tv_id; _} -> tv_id
  | `Ctor (id, _) -> id
  | `Lambda (id, _, _) -> id
  | `Apply (id, _, _) -> id
  | `Poison id -> id

type ('q, 'ty) seen = {
  seen_q: (Ids.Quant.t, 'q) Seen.t;
  seen_ty: (Ids.Type.t, 'ty) Seen.t;
}

let empty_seen () = {
  seen_q = Seen.make (module Ids.Quant);
  seen_ty = Seen.make (module Ids.Type);
}


let ty_q_kids = function
  | `Ctor (_, `Type (`Fn (a, b)))
  | `Ctor (_, `Type (`Record (a, b)))
  | `Ctor (_, `Row (`Extend (_, a, b)))
  | `Lambda (_, a, b)
  | `Apply (_, a, b) ->
      [a; b]

  | `Ctor (_, `Type (`Union a)) ->
      [a]

  | `Free _
  | `Ctor (_, `Type (`Const _))
  | `Ctor (_, `Row `Empty)
  | `Poison _ ->
      []
