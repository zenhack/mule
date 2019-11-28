include PPrint

module Prec = struct
  type t =
    | Binder
    | AppArg
    | AppFn
    | ArrowLeft
    | ArrowRight
    | Pipe
    | Colon
    | TopLevel
  [@@deriving compare]

  let tighter_than l r = compare l r < 0

  let parens_if_tighter_than parent_prec child_prec doc =
    if tighter_than parent_prec child_prec then
      parens doc
    else
      doc
end

let indent doc = nest 2 (group doc)

let opt_fst sep = function
  | [] -> empty
  | (doc :: docs) ->
      ifflat empty (break 0)
      ^^ List.fold_left
        docs
        ~init:(ifflat (indent doc) (indent (sep ^/^ indent doc)))
        ~f:(fun docs doc -> docs ^^ break 0 ^^ indent (sep ^/^ indent doc))
      ^^ break 0

let text s =
  group (char '"' ^^ string (String.escaped s) ^^ char '"')

let binder prec bname args body =
  group (
    Prec.parens_if_tighter_than prec Prec.Binder (
      group (separate (break 1) (string bname :: args) ^^ dot)
      ^/^ indent (group body)
    )
  )

let build_string doc =
  let buf = Buffer.create 1 in
  ToBuffer.pretty 1.0 80 buf (indent doc);
  Buffer.contents buf
