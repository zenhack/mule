
include Paths_t

let mule_root = match Caml.Sys.getenv_opt "MULE_ROOT" with
  | Some p -> p
  | None ->
      try
        Findlib.package_directory "mule-stdlib"
        ^ "/../../share/mule-stdlib"
      with Findlib.No_such_package _ ->
        failwith (String.concat [
            "ERROR: the environment variable $MULE_ROOT is not set, ";
            "and the mule standard library is not installed. Please ";
            "either install the mule-stdlib ocaml package or set ";
            "$MULE_ROOT to the directory containing the mule standard ";
            "library, and try again.";
          ])

let sexp_of_t = function
  | `Relative s -> Sexp.List [Sexp.Atom "Relative"; Sexp.Atom s]
  | `Absolute s -> Sexp.List [Sexp.Atom "Absolute"; Sexp.Atom s]

let base_filepath = function
  | `Relative p -> p
  | `Absolute p ->
      (* If the first path segment contains a dot, then it's a url-ish
       * path like gitlab.com/user/repo, and we should look in $MULE_PATH
       * for a third-party package. Otherwise, it's part of the stdlib,
       * and we should look in $MULE_ROOT.
      *)
      begin match String.find p ~f:(fun c -> Char.equal c '/' || Char.equal c '.') with
        | Some '.' ->
            let mule_path =
              match Caml.Sys.getenv_opt "MULE_PATH" with
              | Some p -> p
              | None ->
                  Caml.Sys.getenv "HOME" ^ "/mule-src"
            in
            mule_path ^ "/" ^ p
        | _ ->
            mule_root ^ "/" ^ p
      end

let validate_parts ~loc parts =
  let path = String.concat ~sep:"/" parts in
  List.iter parts ~f:(fun part -> match part with
    | "" | "." | ".." -> MuleErr.(
        throw
          (`PathError {
                pe_loc = loc;
                pe_path = path;
                pe_problem = `BadPathPart part;
              })
      )
    | _ -> String.iter part ~f:(fun c ->
        if not (Char.is_alphanum c ) then
          begin match c with
            | '-' | '_' | '.' -> ()
            | _ -> MuleErr.(
                throw
                  (`PathError {
                        pe_loc = loc;
                        pe_path = path;
                        pe_problem = `IllegalChar c;
                      })
              )
          end
      )
  )

let resolve_path ~here ~loc ~target =
  let parts = String.split ~on:'/' target in
  begin match parts with
    | ("." :: rest) ->
        validate_parts rest ~loc;
        `Relative (String.concat ~sep:"/" (Caml.Filename.dirname here :: rest))
    | _ ->
        validate_parts ~loc parts;
        `Absolute target
  end

let resolve_embed ~here ~loc ~target =
  match resolve_path ~loc ~here ~target with
  | `Absolute path -> MuleErr.(
      throw (`PathError {
          pe_loc = loc;
          pe_path = path;
          pe_problem = `AbsoluteEmbed;
        })
    )
  | `Relative path ->
      Stdio.In_channel.read_all path
