open Runtime_ast.Expr

let bug msg term =
  MuleErr.bug (msg ^ ": " ^ Pretty.runtime_expr term)

let report step stack expr =
  if Config.print_eval_steps () then
    begin
      Stdio.print_endline ("evaluation: " ^ step ^ ": " ^ Pretty.runtime_expr expr);
      Stdio.print_endline ("stack:");
      List.iter stack ~f:(fun e -> Stdio.print_endline ("  + " ^ Pretty.runtime_expr e))
    end

let rec eval_letrec stack binds body =
  let
    rec stack' = lazy (Lazy.force binds' @ stack)
  and binds' =
    lazy (List.map binds ~f:(fun (cap, expr) ->
        Lazy (lazy (ref (Delayed (List.take (Lazy.force stack') cap, expr))))
      ))
  in
  let binds' = Lazy.force binds' in
  let _ = Lazy.force stack' in
  let binds' = List.map binds' ~f:(eval stack) in
  eval (binds' @ stack) body
and eval stack expr =
  report "eval" stack expr;
  begin match expr with (* whnf stack expr with *)
    | Var v ->
        eval stack (List.nth_exn stack v)
    | App(f, x) ->
        apply stack (eval stack f) (eval stack x)
    | Lam (n, env, body) ->
        Lam (0, List.take stack n @ env, body)
    | PrimIO io -> PrimIO io
    | Prim p -> Prim p
    | Const c -> Const c
    | LetRec (binds, body) ->
        eval_letrec stack binds body
    | Lazy thunk ->
        let r = Lazy.force thunk in
        begin match !r with
          | Ready ret ->
              ret
          | InProgress ->
              MuleErr.throw `LazyLoop
          | Delayed (env, e) ->
              r := InProgress;
              let ret = eval (env @ stack) e in
              r := Ready ret;
              ret
        end

    | Vec arr ->
        (* XXX: this is O(n) even for already-evaluated
         * arrays; should avoid re-scanning.
        *)
        Vec (Array.map arr ~f:(eval stack))
    | Match b -> Match (eval_branch stack b)
    | GetField l -> GetField l
    | Ctor (c, arg) -> Ctor (c, eval stack arg)
    | Record r ->
        Record (Map.map r ~f:(eval stack))
    | Update {old; label; field} ->
        begin match eval stack old with
          | Record r -> Record (Map.set ~key:label ~data:(eval stack field) r)
          | e -> bug "Tried to set field on non-record" e
        end
  end
and eval_branch stack = function
  | BLeaf l -> BLeaf (eval stack l)
  | BLabel {lm_cases; lm_default} -> BLabel {
      lm_cases = Map.map lm_cases ~f:(eval_branch stack);
      lm_default = Option.map lm_default ~f:(eval stack);
    }
  | BConst {cm_cases; cm_default} ->
      (* TODO/XXX: we definitely don't want to evaluate cm_cases here,
       * but we probably still need to do something about embedded free
       * variables. *)
      BConst {
        cm_cases;
        cm_default = Option.map cm_default ~f:(eval stack);
      }
and apply stack f arg =
  report "apply" stack (App(f, arg));
  begin match f with
    | Prim prim ->
        prim arg
    | Lam (_, env, body) ->
        eval (arg :: (env @ stack)) body
    | Match b ->
        begin match apply_branch stack b arg with
          | Some v -> v ()
          | None -> MuleErr.bug "Incomplete match"
        end
    | GetField label ->
        begin match arg with
          | Record r ->
              Util.find_exn r label
          | e ->
              bug "Tried to get field of non-record" e
        end
    | e ->
        bug "Tried to call non-function" e
  end
and apply_branch stack b arg = match b, arg with
  | BLabel {lm_cases; lm_default}, Ctor (lbl, value) ->
      begin match Map.find lm_cases lbl with
        | Some f ->
            apply_branch stack f value
        | None ->
            Option.map lm_default ~f:(fun f ->
              (fun () -> eval stack (App(f, Ctor(lbl, value))))
            )
      end
  | BLabel _, _ ->
      MuleErr.bug "Matched label pattern against non-union."
  | BConst {cm_cases; cm_default}, Const c ->
      begin match Map.find cm_cases c with
        | Some v -> Some (fun () -> eval stack v)
        | None -> Option.map cm_default ~f:(fun f ->
            (fun () -> eval stack (App(f, arg)))
          )
      end
  | BConst _, _ ->
      MuleErr.bug "Matched literal pattern against non-literal."
  | BLeaf f, _ -> Some (fun () -> eval stack (App (f, arg)))
let eval e = eval [] e
