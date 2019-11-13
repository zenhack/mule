include module type of MuleErr_t

val throw: t -> 'a
val bug : string -> 'a
