open Common_ast

module D = Desugared_ast.Expr
module R = Runtime_ast.Expr

type binding = [ `Index of int | `Term of R.t ]

let translate
  : get_import:(Paths_t.t -> R.t)
    -> int
    -> (Var.t, binding, 'cmp) Map.t
    -> 'i D.t
    -> (int * R.t) =
  fun ~get_import ->
  let rec go_expr =
    fun depth env -> function
      | D.Embed {e_value; _} ->
          (0, R.Const (Const.Text e_value))
      | D.Import{i_resolved_path; _} ->
          (0, get_import i_resolved_path)
      | D.LetRec {letrec_binds = {rec_vals = []; _}; letrec_body; _} ->
          go_expr depth env letrec_body
      | D.LetRec {letrec_binds = {rec_vals; _}; letrec_body; _} ->
          go_letrec depth env rec_vals ~mkbody:(fun depth env ->
            go_expr depth env letrec_body
          )
      | D.Record {rec_vals; _} ->
          go_letrec depth env rec_vals ~mkbody:(fun depth env ->
            List.map rec_vals ~f:(fun (v, _) ->
              (var_to_label v, go_var depth env v)
            )
            |> List.map ~f:(fun (v, (d, e)) -> (d, (v, e)))
            |> List.fold
              ~init:(0, Map.empty (module Label))
              ~f:(fun (d, m) (d', (v, e)) ->
                (Int.max d d', Map.set m ~key:v ~data:e)
              )
            |> (fun (d, m) -> (d, R.Record m))
          )
      | D.Const {const_val = c} -> (0, R.Const c)
      | D.Var {v_var = v; _} -> go_var depth env v
      | D.Lam {l_param; l_body} ->
          let (ncap, body') =
            go_expr (depth + 1) (Map.set env ~key:l_param ~data:(`Index (depth + 1))) l_body
          in
          let ncap = Int.max 0 (ncap - 1) in
          (ncap, R.Lam(ncap, [], body'))
      | D.App {app_fn = f; app_arg = x} ->
          let (fcap, f') = go_expr depth env f in
          let (xcap, x') = go_expr depth env x in
          (max fcap xcap, R.App(f', x'))
      | D.WithType {wt_expr = e; _} ->
          go_expr depth env e
      | D.EmptyRecord -> (0, R.Record (Map.empty(module Label)))
      | D.GetField {gf_lbl; gf_record} ->
          let (n, record) = go_expr depth env gf_record in
          (n, R.App(R.GetField gf_lbl, record))
      | D.UpdateVal {uv_lbl = label; uv_val; uv_record} ->
          let (n, old) = go_expr depth env uv_record in
          let (m, field)  = go_expr depth env uv_val in
          ( max n m
          , R.Update {old; label; field}
          )
      | D.UpdateType {ut_record; _} ->
          go_expr depth env ut_record
      | D.Ctor { c_lbl = label; c_arg = e } ->
          let (ncap, e') = go_expr depth env e in
          (ncap, R.Ctor(label, e'))
      | D.Match b ->
          let (n, b) = go_branch depth env b in
          (n, R.Match b)
      | D.Let {let_v = v; let_e = e; let_body = body} ->
          go_expr depth env (D.App {
              app_fn = D.Lam {
                  l_param = v;
                  l_body = body;
                };
              app_arg = e;
            })
  and go_var depth env v =
    begin match Util.find_exn env v with
      | `Index m ->
          let n = depth - m in
          (n+1, R.Var n)
      | `Term t -> (0, t)
    end
  and go_branch depth env b =
    match b with
    | D.BLeaf lf ->
        let (n, lf) = go_leaf depth env lf in
        (n, R.BLeaf lf)
    | D.BLabel {lm_cases; lm_default} ->
        let cases' = Map.map
            lm_cases
            ~f:(go_branch depth env)
        in
        let (defcaps, default') = go_opt_leaf depth env lm_default in
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
        let cases = Map.map cm_cases ~f:(go_expr depth env) in
        let (n, def) = go_opt_leaf depth env cm_default in
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
  and go_opt_leaf depth env lf =
    match lf with
    | None -> (0, None)
    | Some lf ->
        let (ncaps, body) = go_leaf depth env lf in
        (ncaps, Some body)
  and go_leaf: int -> (Var.t, binding, 'cmp) Map.t -> 'i D.leaf -> (int * R.t) =
    fun depth env lf ->
      let l_param =
        match lf.lf_var with
        | Some v -> v
        | None -> Gensym.anon_var ()
      in
      go_expr depth env (D.Lam{l_param; l_body = lf.lf_body})
  and go_letrec depth env bindings ~mkbody =
    let env' =
      bindings
      |> List.rev
      |> List.mapi ~f:(fun i (var, _) -> (var, `Index (depth + i + 1)))
      |> List.fold ~init:env ~f:(fun env (key, data) -> Map.set env ~key ~data)
    in
    let len = List.length bindings in
    let depth' = depth + len in
    let binds = List.map bindings ~f:(fun (_, v) -> go_expr depth' env' v) in
    let (bcap, body) = mkbody depth' env' in
    let cap =
      List.fold ~init:0 ~f:Int.max (bcap - len :: List.map binds ~f:(fun (cap, _) -> cap - len))
    in
    match binds with
    | [] -> (cap, body)
    | _ -> (cap, R.LetRec(binds, body))
  in
  go_expr

let translate: get_import:(Paths_t.t -> R.t) -> 'i D.t -> R.t =
  fun ~get_import exp ->
  let env = Map.map Intrinsics.values ~f:(fun x -> `Term (snd x)) in
  snd (translate ~get_import 0 env exp)
