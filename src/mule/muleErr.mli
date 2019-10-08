include module type of MuleErr_t

val show: t -> string
val throw: t -> 'a
val bug : string -> 'a
