
open Common_ast
module Js = Js_ast

type expr =
  | Var of Var.t
  | Null
  | Const of Const.t
  | Lam1 of (Var.t * expr)
  | Lam2 of (Var.t * Var.t * expr)
  | Switch of (expr * (Const.t * expr) list * expr option)
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
  | Let of (Var.t * expr * expr)

let lam1 f =
  let v = Gensym.anon_var () in
  Lam1(v, f (Var v))

let return k v =
  Js.Return (Js.Lam([], `E (Js.Call(k, [v]))))

let rec cps k e = match e with
  | Var _ | Null | Const _ -> k e
  | Let(v, e, body) ->
      cps k (Call1(Lam1(v, body), e))
  | Lam1(p, body) ->
      let kv = Gensym.anon_var () in
      let k' v = Continue (Call1(Var kv, v)) in
      k (Lam2(p, kv, cps k' body))
  | Call1(f, x) ->
      f |> cps (fun f' ->
        x |> cps (fun x' ->
          Continue(Call2(f', x', lam1 k))))
  | Switch(e, arms, def) ->
      e |> cps (fun e ->
        Switch
          ( e
          , List.map arms ~f:(fun (l, v) -> (l, cps k v))
          , Option.map def ~f:(cps k)
          )
      )
  | Lazy e ->
      let k' = Gensym.anon_var () in
      Lazy(Lam1(k', e |> cps (fun e -> Call1(Var k', e))))
  | Object props ->
      []
      |> List.fold
        props
        ~init:(fun ls -> k (Object ls))
        ~f:(fun acc (l, e) ->
          fun ls -> e |> cps (fun e -> acc ((l, e) :: ls))
        )
  | Tagged(l, e) ->
      e |> cps (fun e -> Tagged(l, e))
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

let const_to_js = function
  | Const.Integer n -> Js.BigInt n
  | Const.Text s -> Js.String s
  | Const.Char c -> Js.String (String.make 1 c)

let rec to_js = function
  | Let _ -> MuleErr.bug "let should have been eliminated before converting to js"
  | Var v -> Js.Var (Var.to_string v)
  | Null -> Js.Null
  | Const c -> const_to_js c
  | Lam1(v, body) ->
      Js.Lam([Var.to_string v], `E (to_js body))
  | Lam2(v, k, body) ->
      Js.Lam([Var.to_string v; Var.to_string k], `E (to_js body))
  | Switch(e, cases, default) ->
      Js.Call
        ( Js.Lam
            ( []
            , `S [
              Js.Switch {
                sw_scrutinee = to_js e;
                sw_cases =
                  List.map cases
                    ~f:(fun (k, v) ->
                      ( const_to_js k
                      , [Js.Return (to_js v)]
                      )
                    );
                sw_default = Option.map default ~f:(fun e ->
                    [Js.Return (to_js e)]
                  );
              }
            ]
            )
        , []
        )
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
