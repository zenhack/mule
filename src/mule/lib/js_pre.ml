
open Common_ast
module Js = Js_ast

type expr =
  | Var of Var.t
  | Null
  | Const of Const.t
  | Lam1 of (Var.t * expr)
  | Lam2 of (Var.t * Var.t * expr)
  | Switch of switch
  | Call1 of (expr * expr)
  | Call2 of (expr * expr * expr)
  | Object of (Label.t * expr) list
  | Tagged of (Label.t * expr)
  | GetTag of expr
  | GetTagArg of expr
  | Lazy of expr
  | Index of (expr * expr)
  | Update of (expr * Label.t * expr)
  | Continue of expr
  | LetRec of ((Var.t * expr) list * expr)
[@@deriving sexp_of]
and switch = {
  sw_arg: expr;
  sw_cases: (Const.t * branch) list;
  sw_default: expr option;
}
[@@deriving sexp_of]
and branch =
  | BLeaf of expr
  | BBranch of switch
[@@deriving sexp_of]

let lam1 f =
  let v = Gensym.anon_var () in
  Lam1(v, f (Var v))

let return k v =
  Js.Return (Js.Lam([], `E (Js.Call(k, [v]))))

let rec cps k e = match e with
  | Var _ | Null | Const _ -> k e
  | Lam1(p, body) ->
      let kv = Gensym.anon_var () in
      let k' v = Continue (Call1(Var kv, v)) in
      k (Lam2(p, kv, cps k' body))
  | Call1(f, x) ->
      f |> cps (fun f' ->
        x |> cps (fun x' ->
          Continue(Call2(f', x', lam1 k))))
  | Switch {sw_arg; sw_cases; sw_default} ->
      sw_arg |> cps (fun e ->
        Switch (cps_switch k {sw_arg = e; sw_cases; sw_default})
      )
  | LetRec(binds, body) ->
      let binds' =
        List.map binds ~f:(fun (v, e) -> (v, cps (fun x -> x) e))
      in
      LetRec(binds', cps k body)
  | Lazy e ->
      let k' = Gensym.anon_var () in
      k (Lazy(Lam1(k', e |> cps (fun e -> Call1(Var k', e)))))
  | Object props ->
      []
      |> List.fold
        props
        ~init:(fun ls -> k (Object ls))
        ~f:(fun acc (l, e) ->
          fun ls -> e |> cps (fun e -> acc ((l, e) :: ls))
        )
  | Tagged(l, e) ->
      e |> cps (fun e -> k (Tagged(l, e)))
  | Index (e, i) -> e |> cps (fun e -> i |> cps (fun i -> k (Index (e, i))))
  | GetTag    e -> e |> cps (fun e -> k (GetTag    e))
  | GetTagArg e -> e |> cps (fun e -> k (GetTagArg e))
  | Update(old, lbl, value) ->
      old |> cps (fun old ->
        value |> cps (fun value ->
          k (Update(old, lbl, value))
        )
      )
  | Continue _ | Lam2 _ | Call2 _ ->
      (* We shouldn't see these, since we only generate them via cps itself,
       * which we only call once. *)
      failwith "BUG"
and cps_switch k {sw_arg; sw_cases; sw_default} = {
  sw_arg;
  sw_cases = List.map sw_cases ~f:(fun (c, b) -> (c, cps_branch k b));
  sw_default = Option.map sw_default ~f:(cps k)
}
and cps_branch k = function
  | BLeaf e -> BLeaf (cps k e)
  | BBranch sw -> BBranch (cps_switch k sw)

let const_to_js = function
  | Const.Integer n -> Js.BigInt n
  | Const.Text s -> Js.String s
  | Const.Char c -> Js.String (String.make 1 c)

let rec to_js = function
  | Var v -> Js.Var (Var.to_string v)
  | Null -> Js.Null
  | Const c -> const_to_js c
  | Lam1(v, body) ->
      Js.Lam([Var.to_string v], `E (to_js body))
  | Lam2(v, k, body) ->
      Js.Lam([Var.to_string v; Var.to_string k], `E (to_js body))
  | Switch sw ->
      Js.Call
        ( Js.Lam
            ([], `S [switch_to_js sw])
        , []
        )
  | LetRec(binds, body) ->
      let binds =
        List.map binds ~f:(fun (v, e) -> Js.VarDecl(Var.to_string v, to_js e))
      in
      let body = Js.Return (to_js body) in
      Js.Call(Js.Lam([], `S (binds @ [body])), [])
  | Lazy e ->
      Js.Call(Js.Var "$lazy", [to_js e])
  | Call1(f, x) ->
      Js.Call(to_js f, [to_js x])
  | Call2(f, x, y) ->
      Js.Call(to_js f, [to_js x; to_js y])
  | Object props ->
      Js.Object (List.map props ~f:(fun (lbl, v) -> (Label.to_string lbl, to_js v)))
  | Tagged(lbl, e) ->
      Js.Array [Js.String(Label.to_string lbl); to_js e]
  | Index (e, i) ->
      Js.Index(to_js e, to_js i)
  | GetTag e ->
      Js.Index(to_js e, Js.Int 0)
  | GetTagArg e ->
      Js.Index(to_js e, Js.Int 1)
  | Update(old, lbl, value) ->
      Js.Call(Js.Var "$update", [
          to_js old;
          Js.String (Label.to_string lbl);
          to_js value;
        ])
  | Continue(e) ->
      Js.Lam([], `E (to_js e))
and switch_to_js {sw_arg; sw_cases; sw_default} =
  Js.Switch {
    sw_scrutinee = to_js sw_arg;
    sw_cases =
      List.map sw_cases
        ~f:(fun (k, v) ->
          ( const_to_js k
          , [branch_to_js v]
          )
        );
    sw_default = Option.map sw_default ~f:(fun e ->
        [Js.Return (to_js e)]
      )
  }
and branch_to_js = function
  | BLeaf e -> Js.Return (to_js e)
  | BBranch sw -> switch_to_js sw
