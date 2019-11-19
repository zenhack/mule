open Common_ast

type import = {
  i_orig_path: string;
  i_resolved_path: Paths_t.t;
  i_loc : Loc.t option;
}
[@@deriving sexp_of]

let import_abs path = {
  i_orig_path = path;
  i_resolved_path = `Absolute path;
  i_loc = None;
}
