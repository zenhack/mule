

let validate_parts parts =
  let path = String.concat ~sep:"/" parts in
  List.iter parts ~f:(fun part -> match part with
      | "" | "." | ".." -> MuleErr.(
          throw
            (PathError {
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
                    (PathError {
                        pe_path = path;
                        pe_problem = `IllegalChar c;
                      })
                )
            end
        )
    )

let resolve_path ~here ~target =
  let parts = String.split ~on:'/' target in
  begin match parts with
    | ("." :: rest) ->
        validate_parts rest;
        `Relative (String.concat ~sep:"/" (dirname here :: rest))
    | _ ->
        validate_parts parts;
        `Absolute target
  end

let resolve_embed ~here ~target =
  match resolve_path ~here ~target with
  | `Absolute path -> MuleErr.(
      throw (PathError {
          pe_path = path;
          pe_problem = `AbsoluteEmbed;
        })
    )
  | `Relative path ->
      Util.IO.slurp_file path
