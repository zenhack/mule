include OrErr_t

let map f = function
  | Ok v -> Ok (f v)
  | Err e -> Err e

let join = function
  | Ok v -> v
  | Err e -> Err e

let (>>=) = fun x f -> join (map f x)

let (>>) = fun x y -> x >>= fun _ -> y

let (|>>) = fun x f -> x >>= fun y -> Ok (f y)

let rec sequence = function
  | [] -> Ok []
  | (x :: xs) ->
      x
      >>= fun v -> sequence xs
      >>= fun vs -> Ok (v :: vs)
