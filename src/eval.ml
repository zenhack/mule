open Ast.Runtime.Expr

module Var = Ast.Var
module Label = Ast.Label

let rec eval stack = function
  | Lazy e ->
      e := eval stack !e;
      !e
  | LetRec(vars, body) ->
      let vars' = List.map vars ~f:(eval stack) in
      eval (vars' @ stack) body
  | Vec arr ->
      (* XXX: this is O(n) even for already-evaluated
       * arrays; should avoid re-scanning.
       *)
      Vec (Array.map arr ~f:(eval stack))
  | Var v ->
      List.nth_exn stack v
  | Lam (n, env, lam) -> Lam
     ( 0
     , List.take stack n @ env
     , lam
     )
  | Match {cases; default} ->
      Match
        { cases = Map.map cases ~f:(eval stack)
        ; default = Option.map default ~f:(eval stack)
        }
  | GetField l -> GetField l
  | Ctor (c, arg) -> Ctor (c, eval stack arg)
  | App (f, arg) ->
      let f' = eval stack f in
      let arg' = eval stack arg in
      begin match f' with
      | Lam (_, env, body) ->
          eval (arg' :: (env @ stack)) body
      | Match {cases; default} ->
          eval_match stack cases default arg'
      | GetField label ->
          begin match arg' with
            | Record r ->
                Map.find_exn r label
            | _ ->
                failwith "Tried to get field of non-record"
          end
      | _ ->
        failwith "Tried to call non-function"
      end
  | Record r ->
      Record (Map.map r ~f:(eval stack))
  | Update {old; label; field} ->
      begin match eval stack old with
        | Record r -> Record (Map.set ~key:label ~data:(eval stack field) r)
        | _ -> failwith "Tried to set field on non-record"
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
              failwith "Match failed"
        end
     end
  | value ->
     begin match default with
       | Some f ->
           eval stack (App(f, value))
       | None ->
           failwith "Match failed"
     end

let eval e = eval [] e
