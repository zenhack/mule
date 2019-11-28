include PPrint

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

let binder bname args body =
  group (
    group (separate (break 1) (string bname :: args) ^^ dot)
    ^/^ indent (group body)
  )
