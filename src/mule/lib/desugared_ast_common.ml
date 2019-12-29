open Common_ast

type import_src =
  [ `Generated
  | `SurfaceImport of Surface_ast.Import.lt
  ]
[@@deriving sexp_of]

type import = {
  i_orig_path: string;
  i_resolved_path: Paths_t.t;
  i_loc : Loc.t option;
  i_src : import_src;
}
[@@deriving sexp_of]

let import_abs i_src path = {
  i_orig_path = path;
  i_resolved_path = `Absolute path;
  i_loc = None;
  i_src;
}
