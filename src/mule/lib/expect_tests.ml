
(* Change directory to the root of the source tree, run f (),
 * then change back. *)
let in_root_dir f =
  let cwd = Caml.Sys.getcwd () in
  let root_dir =
    (* We assume the root dir is the directory containing the "_build"
     * dir. *)
    cwd
    |> String.split ~on:'/'
    |> List.rev
    |> List.drop_while ~f:(fun s -> not (String.equal s "_build"))
    |> Fn.flip List.drop 1
    |> List.rev
    |> String.concat ~sep:"/"
  in
  Caml.Sys.chdir root_dir;
  let result = f () in
  Caml.Sys.chdir cwd;
  result

let tst name =
  in_root_dir (fun () ->
    ignore (Caml.Sys.command (
        String.concat [
          "./_build/default/src/mule/mule.exe eval --debug-steps tests/";
          name; ".mule > tests/"; name; ".actual";
        ]
      ));
    let status = Caml.Sys.command (
        String.concat ["diff -u tests/"; name; ".expected tests/"; name; ".actual"]
      )
    in
    status = 0
  )

let xfail = not

let%test _ = tst "annotated-type"
let%test _ = tst "associated-type"
let%test _ = tst "bad-rank2"
let%test _ = tst "check-record"
let%test _ = tst "choice-annotated"
let%test _ = tst "choice-inferred"
let%test _ = tst "double-type-annotation"
let%test _ = tst "empty-record"
let%test _ = tst "existential"
let%test _ = tst "exist-int"
let%test _ = tst "explicit-nodes-bug"
let%test _ = tst "extend-rule"
let%test _ = tst "factorial"
let%test _ = tst "fixpoint-annotated"
let%test _ = tst "fixpoint"
let%test _ = tst "fn-var-shadowing"
let%test _ = tst "generalized-pattern"
(* This one actually hangs right now, so we don't run it so it
 * doesn't block the rest of the tests. *)
(* let%test _ = tst "hang-rec-all" *)
let%test _ = tst "hang-regression"
let%test _ = tst "higher-rank-record"
let%test _ = tst "id-function"
let%test _ = tst "incomplete-match"
let%test _ = tst "int-match"
let%test _ = tst "int-type"
let%test _ = tst "issue-22"
let%test _ = tst "kind-mismatch-regression"
let%test _ = tst "let-generalization"
let%test _ = tst "let-generalization-row"
let%test _ = tst "let-type"
let%test _ = tst "let-type-recur"
let%test _ = tst "let-type-regression"
let%test _ = tst "lists"
let%test _ = tst "multi-const-pattern"
let%test _ = tst "multi-let"
let%test _ = tst "multi-type-bindings"
let%test _ = tst "nested-default-match"
let%test _ = tst "odd-even"
let%test _ = tst "opaque-all"
let%test _ = tst "opaque-exist"
let%test _ = tst "project-fn"
let%test _ = tst "raise-err"
let%test _ = tst "rank3"
let%test _ = tst "record-projection"
let%test _ = tst "record-update-fn"
let%test _ = tst "record-update"
let%test _ = tst "recursive-type"
let%test _ = tst "recursive-types-regression"
let%test _ = tst "return"
let%test _ = tst "row-graft-regression"
let%test _ = tst "sig-error"
let%test _ = tst "singleton-record"
let%test _ = tst "text-patterns"
let%test _ = tst "top-down-merge"
let%test _ = tst "type-field"
let%test _ = tst "type-field-order"
let%test _ = tst "type-lambda"
let%test _ = tst "type-member-ref"
let%test _ = tst "type-operators"
let%test _ = tst "unbound-type-param"
let%test _ = tst "unbound_type_var"
let%test _ = tst "unguarded-rec"
let%test _ = tst "union"
let%test _ = tst "unreachable-match"
let%test _ = tst "quantifier-flip-regression"
