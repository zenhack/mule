open Ast.Runtime.Expr

module Var = Ast.Var
module Label = Ast.Label

let bug msg term =
  MuleErr.bug (msg ^ ": " ^ Pretty.runtime_expr term)

let report step stack expr =
  if Config.print_eval_steps then
    begin
      Stdio.print_endline ("evaluation: " ^ step ^ ": " ^ Pretty.runtime_expr expr);
      Stdio.print_endline ("stack:");
      List.iter stack ~f:(fun e -> Stdio.print_endline ("  + " ^ Pretty.runtime_expr e))
    end

let rec whnf stack expr =
  report "whnf" stack expr;
  begin match expr with
    | Var v ->
        whnf stack (List.nth_exn stack v)
    | App (f, x) ->
        apply stack (whnf stack f) x
    | Lam (n, env, body) ->
        Lam (0, List.take stack n @ env, body)
    | Lazy thunk ->
        let (env, e) = Lazy.force thunk in
        e := whnf (env @ stack) !e;
        !e
    | LetRec (binds, body) ->
        do_letrec whnf stack binds body
    | e ->
        e
  end
and do_letrec do_ev stack binds body =
  let
    rec stack' = lazy (Lazy.force binds' @ stack)
    and binds' =
    lazy (List.map binds ~f:(fun (cap, expr) ->
        let e = ref expr in
        Lazy (lazy (List.take (Lazy.force stack') cap, e))
      ))
  in
  let binds' = Lazy.force binds' in
  let stack' = Lazy.force stack' in
  let binds' = List.map binds' ~f:(eval stack) in
  do_ev (binds' @ stack') body
and eval stack expr =
  report "eval" stack expr;
  begin match whnf stack expr with
    | PrimIO io -> PrimIO io
    | Prim p -> Prim p
    | Const c -> Const c
    | LetRec (binds, body) ->
        do_letrec eval stack binds body
    | Lazy thunk ->
        let (env, e) = Lazy.force thunk in
        e := eval (env @ stack) !e;
        !e

    | Vec arr ->
        (* XXX: this is O(n) even for already-evaluated
         * arrays; should avoid re-scanning.
        *)
        Vec (Array.map arr ~f:(eval stack))
    | Lam lam -> Lam lam
    | Match {cases; default} ->
        Match
          { cases = Map.map cases ~f:(eval stack)
          ; default = Option.map default ~f:(eval stack)
          }
    | ConstMatch {cm_cases; cm_default} ->
        (* TODO/XXX: we definitely don't want to evaluate cm_cases here,
         * but we probably still need to do something about embedded free
         * variables. *)
        ConstMatch
          { cm_cases
          ; cm_default = eval stack cm_default
          }
    | GetField l -> GetField l
    | Ctor (c, arg) -> Ctor (c, eval stack arg)
    | App (f, x) ->
        bug "App should never appear after whnf." (App (f, x))
    | Var v ->
        bug "Var should never appear after whnf." (Var v)
    | Record r ->
        Record (Map.map r ~f:(eval stack))
    | Update {old; label; field} ->
        begin match eval stack old with
          | Record r -> Record (Map.set ~key:label ~data:(eval stack field) r)
          | e -> bug "Tried to set field on non-record" e
        end
  end
and apply stack f arg =
  report "apply" stack (App(f, arg));
  let f' = eval stack f in
  begin match f' with
    | Prim prim ->
        prim (eval stack arg)
    | Lam (_, env, body) ->
        eval (eval stack arg :: (env @ stack)) body
    | Match {cases; default} ->
        eval_match stack cases default (eval stack arg)
    | ConstMatch {cm_cases; cm_default} ->
        begin match eval stack arg with
          | Const c ->
              eval_const_match stack cm_cases cm_default c
          | e ->
              bug "ConstMatch matched against non constant" e
        end
    | GetField label ->
        begin match eval stack arg with
          | Record r ->
              Util.find_exn r label
          | e ->
              bug "Tried to get field of non-record" e
        end
    | e ->
        bug "Tried to call non-function" e
  end
and eval_match stack cases default =
  function
  | Ctor (lbl, value) ->
      begin match Map.find cases lbl with
        | Some f ->
            eval stack (App(f, value))
        | None ->
            begin match default with
              | Some f ->
                  eval stack (App(f, Ctor(lbl, value)))
              | None ->
                  bug "Match failed" (Match{cases; default})
            end
      end
  | value ->
      begin match default with
        | Some f ->
            eval stack (App(f, value))
        | None ->
            bug "Match failed" (Match{cases; default})
      end
and eval_const_match stack cases default c =
  begin match Map.find cases c with
    | Some v -> eval stack v
    | None -> eval stack (App(default, Const c))
  end
let eval e = eval [] e
