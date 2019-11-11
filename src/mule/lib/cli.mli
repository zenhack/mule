include module type of Cli_t

val parse_cmd : unit -> t Cmdliner.Term.result
