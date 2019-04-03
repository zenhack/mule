module MkMap(Key:Comparator.S) = struct
  type 'a t = (Key.t, 'a, Key.comparator_witness) Map.t
  let empty = Map.empty (module Key)
  let singleton k v = Map.singleton (module Key) k v
end

module MkSet(Elt:Comparator.S) = struct
  type t = (Elt.t, Elt.comparator_witness) Set.t
  let empty = Set.empty (module Elt)
  let singleton e = Set.singleton (module Elt) e
end
