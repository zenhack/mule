
include Cli_t

(*
open Cmdliner

let repl_term =
  Term.const `Repl

let test_term =
  Term.(const (fun p -> `Text p) $
        Arg.(required
             & some
             & pos 0 non_dir_file ""
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
                  & some
                  & pos 0 string ""
                  & info []
                    ~docv:"RUNNER"
                    ~doc:"Use the runner $(docv)"
                 )
          $ Arg.(required
                  & some
                  & pos 1 non_dir_file ""
                  & info []
                    ~docv:"FILE"
                    ~doc:"Run the file $(docv)"
                 )
         )

let build_js_term =
  Term.(const (fun p -> `Build_js p) $
        Arg.(required
              & some
              & pos 0 non_dir_file ""
              & info []
                ~docv:"FILE"
                ~doc:"Compile the file $(docv)"
             )
       )

let parse_cmd () =
    Term.eval_choice repl_term [repl_term; test_term; run_term; build_js_term]
   *)
