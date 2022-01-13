
module C = Constraint_t
module GT = Graph_types
module DT = Desugared_ast_type

module Let_syntax = struct
  type 'a t =
    Context.t -> C.polarity -> GT.bound_target -> 'a

  let return x =
    fun _c _p _bt -> x

  let bind x ~f =
    fun c p bt ->
      f (x c p bt) c p bt

  let map x ~f =
    bind x ~f:(fun y -> return (f y))
end

let build c p bt x =
  x c p bt

include Let_syntax

type 'a vt = 'a GT.var t
type qt = GT.quant vt
type tt = GT.typ vt
type pt = GT.prekind vt
type gt = GT.guard vt
type kt = GT.kind vt

let flip_polarity : C.polarity -> C.polarity = function
  | `Pos -> `Neg
  | `Neg -> `Pos

let negate x =
  fun c p bt ->
    x c (flip_polarity p) bt

let type_id =
  fun c _p _bt ->
    GT.Ids.Type.fresh (Context.get_ctr c)

(*
let quant_id =
  fun c _p _bt ->
    GT.Ids.Quant.fresh (Context.get_ctr c)
*)

let new_var vtype value =
  fun c _p _bt ->
    Context.make_var c vtype value

let fn qp qr =
  let%bind id = type_id in
  let%bind p = negate qp in
  let%bind r = qr in
  new_var Context.typ (`Ctor(id, `Type(`Fn(p, r))))

let ( **> ) = fn

let bottom flag k =
  let%bind tv_kind = k in
  let%bind tv_id = type_id in
  fun c _p bt ->
    let tv_bound = Context.make_var c Context.bound {
        b_target = bt;
        b_flag = flag;
      }
    in
    Context.make_var c Context.typ (`Free {
      tv_id;
      tv_merged = Set.singleton (module GT.Ids.Type) tv_id;
      tv_bound;
      tv_kind;
    })

let get_flag q p = match q, p with
  | `All, `Pos | `Exist, `Neg -> `Flex
  | `All, `Neg | `Exist, `Pos -> `Rigid

let quant (q : DT.quantifier) (mkvar : tt) (mkbody : qt -> tt) =
  fun c p bt ->
    let flag = get_flag q p in
    (* XXX: this feels dubious to me *)
    Context.with_quant c {b_target = bt; b_flag = `Flex} (fun q ->
      let qv =
        Context.with_quant c { b_target = `Q q; b_flag = flag; } (fun q' ->
          mkvar c p (`Q q')
        )
      in
      mkbody (return qv) c p bt
    )

let all v b =
  quant `All v b

let exist v b =
  quant `Exist v b

(*

val guard : GT.guard -> gt
val kind : gt -> pt -> kt

val karrow : kt -> kt -> pt
val ktype : pt
val krow : pt
val kfree : pt

val with_kind : kt -> qt -> qt
*)
