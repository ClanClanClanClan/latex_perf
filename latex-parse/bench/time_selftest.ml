open Latex_parse_lib.Clock

let () =
  let t0 = now () in
  Unix.sleepf 0.010;
  let t1 = now () in
  let dt_ms = ms_of_ns Int64.(sub t1 t0) in
  Printf.printf "Sleep(10ms) measured = %.3f ms\n%!" dt_ms;
  assert (dt_ms > 7.0 && dt_ms < 30.0);
  print_endline "OK"
