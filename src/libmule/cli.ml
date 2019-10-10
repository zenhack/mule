
include Cli_t

open Cmdliner

let repl_term =
  Term.(const `Repl)


let test_term =
  Term.(const (fun p -> `Test p) $
        Arg.(required
             & pos 0 (some non_dir_file) None
             & info []
               ~docv:"FILE"
               ~doc:"Test the file $(docv)"
            )
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
        )

let build_js_term =
  Term.(const (fun p -> `Build_js p) $
        Arg.(required
              & pos 0 (some non_dir_file) None
              & info []
                ~docv:"FILE"
                ~doc:"Compile the file $(docv)"
             )
       )

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
        test_term, Term.info "test";
        run_term, Term.info "run";
        build_js_term, Term.info "build-js";
      ]
