open Common_ast

module RowMap = struct
  type 'v t = (Label.t, 'v, Label.comparator_witness) Map.t
end

module Type = struct
  type quantifier = [ `All | `Exist ]

  type 'i t =
    | Fn of ('i * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Record of ('i * (Label.t * 'i t) list * Var.t option)
    | Union of ('i * (Label.t * 'i t) list * Var.t option)
    | Quant of ('i * quantifier * Var.t * 'i t)

  (* Alpha-rename the type variables in a type, such that all of them are
   * distinct (nothing is shadowed). leaves free type variables alone. *)
  let rec alpha_rename env = function
    | Fn(i, l, r) ->
        Fn(i, alpha_rename env l, alpha_rename env r)
    | Recur (i, v, body) ->
        let v' = Gensym.anon_var () in
        Recur(i, v', alpha_rename (Map.set ~key:v ~data:v' env) body)
    | Var (i, v) ->
        begin match Map.find env v with
          | None -> Var(i, v)
          | Some v' -> Var(i, v')
        end
    | Record row -> Record (alpha_rename_row env row)
    | Union row -> Union (alpha_rename_row env row)
    | Quant(i, q, v, body) ->
        let v' = Gensym.anon_var () in
        Quant(i, q, v', alpha_rename (Map.set ~key:v ~data:v' env) body)
  and alpha_rename_row env (i, parts, rest) =
    ( i
    , List.map parts ~f:(fun (l, v) -> (l, alpha_rename env v))
    , Option.map rest ~f:(fun _ -> Gensym.anon_var ())
    )
end

module Expr = struct
  type t =
    | Var of Var.t
    | Lam of (Var.t * t)
    | App of (t * t)
    | EmptyRecord
    | GetField of (t * Label.t)
    | Update of Label.t
    | Ctor of (Label.t * t)
    | Match of {
        cases: (Var.t * t) RowMap.t;
        default: (Var.t option * t) option;
      }
    | WithType of (t * unit Type.t)
    | Let of (Var.t * t * t)
end
