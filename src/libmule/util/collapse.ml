
module type Nested = sig
  type 'a t

  val apply_kids : 'a t -> f:('a t -> 'a t) -> 'a t
end

module Make(E:Nested) = struct
  let rec bottom_up_desc e ~f =
    E.apply_kids e ~f:(fun e -> f (bottom_up_desc e ~f))

  let rec top_down_desc e ~f =
    E.apply_kids e ~f:(fun e -> top_down_desc (f e) ~f)

  let bottom_up e ~f =
    f (bottom_up_desc e ~f)

  let top_down e ~f =
    top_down_desc (f e) ~f
end

