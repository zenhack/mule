(* Misc. helpers for reporting error messages to the user.
 *
 * The names of some of these could use improvement.
 *)

(* Wrappers around the standard versions of these functions which also
 * flush stdout. *)
val print_string : string -> unit
val print_endline : string -> unit

(* Helpers for displaying error messages; the first argument is used
 * as a label, and the second is the message. The message is indented
 * by one tab.
 *
 * [display] only displays anything if --debug-steps was passed on the
 * command line, whereas [display_always] always displays.
 *)
val display : string -> string -> unit
val display_always : string -> string -> unit
