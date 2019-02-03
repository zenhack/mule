include module type of OrErr_t

val map : ('a -> 'b) -> ('e, 'a) t -> ('e, 'b) t

val join : ('e, ('e, 'a) t) t -> ('e, 'a) t

val (>>=) : ('e, 'a) t -> ('a -> ('e, 'b) t) -> ('e, 'b) t
val (>>) : ('e, 'a) t -> ('e, 'b) t -> ('e, 'b) t
val (|>>) : ('e, 'a) t -> ('a -> 'b) -> ('e, 'b) t
