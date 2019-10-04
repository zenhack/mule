
module T = Typecheck_types
open Common_ast

type t = T.sign -> T.bound_target -> T.u_var

type row = (Label.t * t) list * t option

let build sign b_at builder =
  builder sign b_at

let return v _sign _b_at =
  v

let quant: T.quantifier -> T.k_var -> (t -> t) -> t =
  fun q k f sign b_at ->
  fst
    ( Util.fix
      (fun arg ->
        UnionFind.make
          (`Quant
            ( Gen_t.ty_var_at b_at
            , Lazy.force arg
            )
          )
      )
      (fun binder ->
         let uv =
           UnionFind.make
             (`Free
                ( T.{
                      ty_id = Gensym.gensym ();
                      ty_bound =
                        ref {
                          b_at = `Ty binder;
                          b_ty = T.get_flag q sign;
                        };
                    }
                , k
                )
             )
         in
         f (return uv) sign b_at
      )
    )


let all f =
  quant `All f

let exist f =
  quant `Exist f


let ( **> ) f x sign b_at =
  T.fn (Gen_t.ty_var_at b_at)
    (f (T.flip_sign sign) b_at)
    (x sign b_at)
  |> UnionFind.make

let row sign b_at (fs, rest) =
  let default x f = match x with
    | Some y -> y
    | None -> f ()
  in
  let rest =
    default
      rest
      (fun () ->
         return (UnionFind.make (T.empty (Gen_t.ty_var_at b_at))))
  in
  let r =
    List.fold_right fs ~init:(rest sign b_at) ~f:(fun (lbl, hd) tl ->
        T.extend (Gen_t.ty_var_at b_at) lbl (hd sign b_at) tl
        |> UnionFind.make
      )
  in
  r

let record (t: row) (v: row) (sign: T.sign) (b_at: T.bound_target): T.u_var =
  let row = row sign b_at in
  UnionFind.make (T.record (Gen_t.ty_var_at b_at) (row t) (row v))

let record_v v = record ([], None) v
let record_t t = record t ([], None)

let union r sign b_at =
  T.union (Gen_t.ty_var_at b_at) (row sign b_at r)
  |> UnionFind.make

let prim: (T.tyvar -> T.u_type) -> t = fun f _sign b_at ->
  UnionFind.make (f (Gen_t.ty_var_at b_at))

let int = prim T.int
let text = prim T.text
let char = prim T.char

let witness: t -> t = fun f sign b_at ->
  let uv = f sign b_at in
  T.witness (Gen_t.ty_var_at b_at) (T.get_kind uv) uv
  |> UnionFind.make
