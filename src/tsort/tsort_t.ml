type 'n comparator = (module Comparator.S with type t = 'n)

type 'n edge = {
  to_: 'n;
  from: 'n;
}
