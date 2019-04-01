module MkMap(Key:Comparator.S) = struct
  type 'a t = (Key.t, 'a, Key.comparator_witness) Map.t
end

module MkSet(Elt:Comparator.S) = struct
  type t = (Elt.t, Elt.comparator_witness) Set.t
end
