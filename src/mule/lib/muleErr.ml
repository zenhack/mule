include MuleErr_t

let throw e =
  if Config.always_print_stack_trace () then
    begin
      Caml.Printexc.print_raw_backtrace
        Caml.stdout
        (Caml.Printexc.get_callstack 25);
    end;
  raise (MuleExn e)

let bug msg =
  throw (`Bug msg)
