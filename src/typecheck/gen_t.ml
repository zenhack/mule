open Typecheck_types
open Gensym

let ty_var_at: bound_target -> tyvar = fun b_at ->
  { ty_id = gensym ()
  ; ty_bound = ref
        { b_ty = `Flex
        ; b_at = b_at
        }
  }

let gen_ty_var: g_node -> tyvar = fun g -> ty_var_at (`G g)

let gen_u: u_kind -> bound_target -> u_type UnionFind.var =
  fun kind targ -> UnionFind.make
      (`Free
         ( { ty_id = gensym ()
           ; ty_bound = ref { b_ty = `Flex; b_at = targ }
           }
         , kind
         ))
