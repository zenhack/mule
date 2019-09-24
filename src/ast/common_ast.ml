module Name = struct
  module type S = sig
    include Comparable.S

    val sexp_of_t : t -> Sexp.t
    val t_of_sexp : Sexp.t -> t

    val of_string : string -> t
    val to_string : t -> string
  end

  module Impl : S = struct
    module T = struct
      type t = string
      let sexp_of_t = sexp_of_string
      let t_of_sexp = string_of_sexp
      let compare = String.compare
    end

    include T
    include Comparable.Make(T)

    let of_string s = s
    let to_string s = s


    let equal = String.equal
  end
end

module Var : Name.S = Name.Impl
module Label : Name.S = Name.Impl


let var_to_label v = Var.to_string v |> Label.of_string
let var_of_label l = Label.to_string l |> Var.of_string

module Const = struct
  module T = struct
    type t =
      | Text of string
      | Integer of Bigint.t
      | Char of char
    [@@deriving sexp]
    let compare x y =
      let tag_no = function
        | Text _ -> 1
        | Integer _ -> 2
        | Char _ -> 3
      in
      match x, y with
      | Text x, Text y -> String.compare x y
      | Integer x, Integer y -> Bigint.compare x y
      | Char x, Char y -> Char.compare x y
      | _ -> Int.compare (tag_no x) (tag_no y)
  end

  include T
  include Comparator.Make(T)
end

module Loc = struct
  (* This is the same as MParser.pos, but by defining it inline,
   * we can get the deriving magic to work correctly: *)
  type pos = (int * int * int)
  [@@deriving sexp]

  type t = {
    start: pos;
    stop: pos;
  }
  [@@deriving sexp]

  let spanning l r = {
    start = l.start;
    stop = r.stop;
  }

  type 'a located = {
    l_value : 'a;
    l_loc : t;
  }
end
