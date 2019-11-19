open Common_ast

type import = {
  i_orig_path: string;
  i_resolved_path: Paths_t.t;
  i_loc : Loc.t option;
}
[@@deriving sexp_of]
