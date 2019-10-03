include module type of MuleErr_t

val show_ctor: ctor -> string
val show_op: op -> string
val show_kind: kind -> string
val show_type_error: (Types.reason * type_error) -> string
val show_path_error: path_error -> string
val show: t -> string

val throw: t -> 'a
val bug : string -> 'a
