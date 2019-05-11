open Ast.Runtime.Expr

module Var = Ast.Var
module Label = Ast.Label

let bug msg term =
  failwith ("BUG: " ^ msg ^ ": " ^ Pretty.runtime_expr term)

let report step expr =
  if Config.print_eval_steps then
    Stdio.print_endline ("evaluation: " ^ step ^ ": " ^ Pretty.runtime_expr expr)
  else
    ()

let rec whnf stack expr =
  report "whnf" expr;
  begin match expr with
  | Var v ->
      whnf stack (List.nth_exn stack v)
  | App (f, x) ->
      apply stack (whnf stack f) x
  | Lam (n, env, body) ->
      Lam (0, List.take stack n @ env, body)
  | e ->
      e
  end
and eval stack expr =
  report "eval" expr;
  begin match whnf stack expr with
  | Lazy e ->
      e := eval stack !e;
      !e
  | Fix flag -> Fix flag
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
      report "apply" (App(f, arg));
      let f' = eval stack f in
      begin match f' with
      | Lam (_, env, body) ->
          eval (eval stack arg :: (env @ stack)) body
      | Match {cases; default} ->
          eval_match stack cases default (eval stack arg)
      | GetField label ->
          begin match eval stack arg with
            | Record r ->
                Map.find_exn r label
            | e ->
                bug "Tried to get field of non-record" e
          end
      | Fix `Let ->
          begin match whnf stack arg with
          | Lam(_, env, body) ->
              eval (Lazy(ref (App(Fix `Let, arg))) :: (env @ stack)) body
          | e ->
              bug "fix/let given a non-lambda." e
          end
      | Fix `Record ->
          begin match whnf stack arg with
          | Lam(_, env, body) ->
              let result = ref arg in
              let new_stack = Lazy result :: (env @ stack) in
              let record = record_whnf new_stack body in
              result := record;
              eval stack (Lazy result)
          | e ->
            bug "BUG: fix/record given a non-lambda." e
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
and record_whnf stack arg =
  report "record_whnf" arg;
  match whnf stack arg with
  | Record r ->
      Record r
  | Update{old; label; field} ->
      begin match record_whnf stack old with
      | Record r ->
          Record (Map.set r ~key:label ~data:(Lazy (ref field)))
      | e ->
          bug "Non-record returned by record_whnf" e
      end
  | e ->
      bug "Non-record passed to record_whnf" e

let eval e = eval [] e
