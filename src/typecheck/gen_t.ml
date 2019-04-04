open Typecheck_types
open Gensym

let ty_var_at: bound_target -> tyvar = fun b_at ->
  { ty_id = gensym ()
  ; ty_bound = UnionFind.make
    { b_ty = `Flex
    ; b_at = b_at
    }
  }

let tv_pair_at: bound_target -> (tyvar * tyvar) = fun b_at ->
  let x = ty_var_at b_at in
  ( x
  , { ty_id = gensym ()
    ; ty_bound = x.ty_bound
    }
  )

let gen_ty_var: g_node -> tyvar = fun g -> ty_var_at (`G g)


let gen_u: bound_target -> [> `Free of tyvar ] UnionFind.var = fun targ ->
  UnionFind.make (`Free
    { ty_id = gensym ()
    ; ty_bound = UnionFind.make { b_ty = `Flex; b_at = targ }
    })