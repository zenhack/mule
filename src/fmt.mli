type t

val to_string : t -> string

val s : string -> t
val c : char -> t
val concat : t list -> t

val (^) : t -> t -> t

val empty : t

val between : t -> t -> t -> t

val parens : t -> t
val brackets : t -> t
val braces : t -> t

val sep_by : t -> t list -> t
val end_by : t -> t list -> t

val comma_sep : t list -> t
