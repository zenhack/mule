
include Cli_t

open Cmdliner

let repl_term =
  Term.(const `Repl, info "repl")


let test_term =
  Term.(const (fun p -> `Test p) $
        Arg.(required
             & pos 0 (some non_dir_file) None
             & info []
               ~docv:"FILE"
               ~doc:"Test the file $(docv)"
            )
       , info "test"
       )

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
        , info "run"
        )

let build_js_term =
  Term.(const (fun p -> `Build_js p) $
        Arg.(required
              & pos 0 (some non_dir_file) None
              & info []
                ~docv:"FILE"
                ~doc:"Compile the file $(docv)"
             )
       , info "build-js"
       )

let parse_cmd () =
    Term.eval_choice repl_term [repl_term; test_term; run_term; build_js_term]
