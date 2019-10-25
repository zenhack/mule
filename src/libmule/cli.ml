
include Cli_t

open Cmdliner

let with_debug_flags : cmd Term.t -> t Term.t =
  fun term ->
    Term.(const (fun eval_steps stack_trace trace_require_subtype steps c -> object
        method debug_flags = object
          method print_eval_steps = eval_steps
          method always_print_stack_trace = stack_trace
          method trace_require_subtype = trace_require_subtype
          method debug_steps = steps
        end
        method cmd = c
    end)
    $ Arg.(value & flag & info ["debug-print-eval-steps"])
    $ Arg.(value & flag & info ["debug-always-print-stack-trace"])
    $ Arg.(value & flag & info ["debug-trace-require-subtype"])
    $ Arg.(value & flag & info ["debug-steps"])
    $ term
    )

let eval_term =
  Term.(const (fun p -> `Eval p) $
        Arg.(required
             & pos 0 (some non_dir_file) None
             & info []
               ~docv:"FILE"
               ~doc:"Evaluate the expression in the file $(docv)"
            )
       )
  |> with_debug_flags

let run_term =
  Term.(const (fun r f -> `Run (object
                  method runner = r
                  method file = f
                end))
          $ Arg.(required
                  & pos 0 (some string) None
                  & info []
                    ~docv:"RUNNER"
                    ~doc:"Use the runner $(docv)"
                 )
          $ Arg.(required
                  & pos 1 (some non_dir_file) None
                  & info []
                    ~docv:"FILE"
                    ~doc:"Run the file $(docv)"
                 )
        )
  |> with_debug_flags

let build_js_term =
  Term.(const (fun p -> `Build_js p) $
        Arg.(required
              & pos 0 (some non_dir_file) None
              & info []
                ~docv:"FILE"
                ~doc:"Compile the file $(docv)"
             )
       )
  |> with_debug_flags

let repl_term =
  Term.(const `Repl)
  |> with_debug_flags

let parse_cmd () =
  Term.eval_choice
    ( repl_term
    , Term.info "mule"
    )
    [
      ( repl_term
      , Term.info "repl"
          ~doc:"Start an interactive repl"
      );
      ( eval_term
      , Term.info "eval"
          ~doc:"Evaluate an expression in a file"
      );
      run_term, Term.info "run";
      ( build_js_term
      , Term.info "build-js"
          ~doc:"Compile to javascript."
      )
    ]
