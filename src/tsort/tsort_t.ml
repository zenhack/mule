type 'n comparator = (module Comparator.S with type t = 'n)

type 'n edge = {
  to_: 'n;
  from: 'n;
}

type 'n result =
  [ `Single of 'n | `Cycle of ('n * 'n list) ] list
