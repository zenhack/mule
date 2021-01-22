module GT = Graph_types

let rec infer_kind : Context.t -> GT.typ GT.var -> GT.kind GT.var =
  fun ctx t ->
    let t = Context.read_var ctx Context.typ t in
    match t with
    | `Free tv -> tv.GT.tv_kind
    | `Ctor (_, ctor) -> infer_kind_ctor ctx ctor
    | `Poison _ -> Context.make_var ctx Context.kind GT.{
        k_prekind = Context.make_var ctx Context.prekind `Poison;
        k_guard = Context.make_var ctx Context.guard `Poison;
      }
    | `Lambda _ -> failwith "TODO: infer kinds for type lambdas"
    | `Apply _ -> failwith "TODO: infer kinds for type application"
and infer_kind_ctor : Context.t -> GT.ctor -> GT.kind GT.var =
  fun ctx ctor ->
    let pk = infer_prekind_ctor ctx ctor in
    Context.make_var ctx Context.kind GT.{
      k_prekind = pk;
      k_guard = Context.make_var ctx Context.guard `Free;
    }
and infer_prekind_ctor : Context.t -> GT.ctor -> GT.prekind GT.var =
  fun ctx ctor ->
    match ctor with
      (* TODO(perf): maybe have a single shared variable for these
         defined on the context *)
      | `Type _ -> Context.make_var ctx Context.prekind `Type
      | `Row _ -> Context.make_var ctx Context.prekind `Row
