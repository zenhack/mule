open Common_ast

module D = Desugared_ast.Expr
module R = Runtime_ast.Expr

type binding = [ `Index of int | `Term of R.t ]

let rec translate: int -> binding VarMap.t -> 'i D.t -> (int * R.t) =
  fun depth env -> function
    | D.Embed {e_value; _} ->
        (0, R.Const (Const.Text e_value))
    | D.LetRec {letrec_vals = []; letrec_body; _} ->
        translate depth env letrec_body
    | D.LetRec {letrec_vals; letrec_body; _} ->
        translate_letrec depth env letrec_vals letrec_body
    | D.Const {const_val = c} -> (0, R.Const c)
    | D.Var {v_var = v; _} ->
        begin match Util.find_exn env v with
          | `Index m ->
              let n = depth - m in
              (n+1, R.Var n)
          | `Term t -> (0, t)
        end
    | D.Lam {l_param; l_body} ->
        let (ncap, body') =
          translate (depth + 1) (Map.set env ~key:l_param ~data:(`Index (depth + 1))) l_body
        in
        let ncap = Int.max 0 (ncap - 1) in
        (ncap, R.Lam(ncap, [], body'))
    | D.App {app_fn = f; app_arg = x} ->
        let (fcap, f') = translate depth env f in
        let (xcap, x') = translate depth env x in
        (max fcap xcap, R.App(f', x'))
    | D.WithType {wt_expr = e; _} ->
        translate depth env e
    | D.EmptyRecord -> (0, R.Record LabelMap.empty)
    | D.GetField {gf_lbl} -> (0, R.GetField gf_lbl)
    | D.UpdateVal {uv_lbl = label } ->
        ( 0
        , R.Lam(0, [], R.Lam(1, [], R.Update { old = R.Var 1; label; field = R.Var 0 }))
        )
    | D.UpdateType {ut_record; _} ->
        translate depth env ut_record
    | D.Ctor { c_lbl = label; c_arg = e } ->
        let (ncap, e') = translate depth env e in
        (ncap, R.Ctor(label, e'))
    | D.Match b ->
        let (n, b) = translate_branch depth env b in
        (n, R.Match b)
    | D.Let {let_v = v; let_e = e; let_body = body} ->
        translate depth env (D.App {
            app_fn = D.Lam {
                l_param = v;
                l_body = body;
              };
            app_arg = e;
          })
and translate_branch depth env b =
  match b with
  | D.BLeaf lf ->
      let (n, lf) = translate_leaf depth env lf in
      (n, R.BLeaf lf)
  | D.BLabel {lm_cases; lm_default} ->
      let cases' = Map.map
          lm_cases
          ~f:(translate_branch depth env)
      in
      let (defcaps, default') = translate_opt_leaf depth env lm_default in
      let ncaps = Map.fold
          ~init:defcaps
          ~f:(fun ~key:_ ~data -> max data)
          (Map.map cases' ~f:fst)
      in
      ( ncaps
      , R.BLabel {
          lm_cases = Map.map ~f:snd cases';
          lm_default = default';
        }
      )
  | D.BConst {cm_cases; cm_default} ->
      let cases = Map.map cm_cases ~f:(translate depth env) in
      let (n, def) = translate_opt_leaf depth env cm_default in
      let ncaps = Map.fold
          cases
          ~init:n
          ~f:(fun ~key:_ ~data:(next, _) prev -> max next prev)
      in
      ( ncaps
      , R.BConst {
          cm_cases = Map.map cases ~f:snd;
          cm_default = def;
        }
      )
and translate_opt_leaf depth env lf =
  match lf with
  | None -> (0, None)
  | Some lf ->
      let (ncaps, body) = translate_leaf depth env lf in
      (ncaps, Some body)
and translate_leaf: int -> binding VarMap.t -> 'i D.leaf -> (int * R.t) =
  fun depth env lf ->
  let l_param =
    match lf.lf_var with
    | Some v -> v
    | None -> Gensym.anon_var ()
  in
  translate depth env (D.Lam{l_param; l_body = lf.lf_body})
and translate_letrec depth env bindings body =
  let env' =
    bindings
    |> List.rev
    |> List.mapi ~f:(fun i (var, _) -> (var, `Index (depth + i + 1)))
    |> List.fold ~init:env ~f:(fun env (key, data) -> Map.set env ~key ~data)
  in
  let len = List.length bindings in
  let depth' = depth + len in
  let binds = List.map bindings ~f:(fun (_, v) -> translate depth' env' v) in
  let (bcap, body) = translate depth' env' body in
  let cap =
    List.fold ~init:0 ~f:Int.max (bcap - len :: List.map binds ~f:(fun (cap, _) -> cap - len))
  in
  (cap, R.LetRec(binds, body))

let translate: 'i D.t -> R.t =
  fun exp ->
  let env = Map.map Intrinsics.values ~f:(fun x -> `Term (snd x)) in
  snd (translate 0 env exp)
