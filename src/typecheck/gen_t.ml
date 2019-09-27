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

let gen_u: k_var -> bound_target -> u_var =
  fun kind targ -> UnionFind.make
      (`Free
         ( { ty_id = gensym ()
           ; ty_bound = ref { b_ty = `Flex; b_at = targ }
           }
         , kind
         ))

let clone_ty_var: tyvar -> tyvar =
  fun tv ->
    { ty_id = gensym ()
    ; ty_bound = ref (!(tv.ty_bound))
    }

let lambda: tyvar -> k_var -> k_var -> (bound_target -> u_var -> u_var) -> u_var =
  fun tv kparam kret f ->
  fst (
    Util.fix
      (fun kids ->
         let param, ret = Lazy.force kids in
         UnionFind.make (
           `Const
             ( tv
             , `Named "<lambda>"
             , [param, kparam; ret, kret]
             , UnionFind.make (`Arrow (kparam, kret))
             )
         )
      )
      (fun lam ->
         let param = UnionFind.make (
             `Free
               ( { ty_id = gensym ()
                 ; ty_bound = ref { b_ty = `Explicit; b_at = `Ty lam }
                 }
               , kparam
               )
           )
         in
         let tv =
           { ty_id = gensym ()
           ; ty_bound = ref { b_ty = `Explicit; b_at = `Ty lam }
           }
         in
         let ret = fst (
             Util.fix
               (fun ret -> UnionFind.make (`Quant(tv, Lazy.force ret)))
               (fun q -> f (`Ty q) param)
           )
         in
         (param, ret)
      )
  )
