
include Paths_t

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
