(* bench_readiness_kernel — in-process microbench isolating the components of
   the compile-readiness kernel, so the numbers exclude OS process-startup and
   rule-registry construction (both are one-time, amortised in a long-running
   editor session). Reports, per input file:
     parse_ms   : one Parser_l2.parse_located
     fastrun_ms : run_compile_blocking (shared parse) — the ~37 rules,
                  INCLUDING the shared parse (i.e. the true fast-kernel compute)
     rules_ms   : fastrun_ms - parse_ms — the 37-rule execution alone
   run_all is intentionally NOT benched in-process: it memoises on the source
   (Cache_key), so reps 2..N would be cache hits and lie. The full-path numbers
   come from the fresh-process CLI benchmark (bench_compile_check.sh) instead.
   Usage: bench_readiness_kernel <reps> <file.tex>... *)

let read_file p =
  let ic = open_in_bin p in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let median xs =
  let a = Array.of_list xs in
  Array.sort compare a;
  let n = Array.length a in
  if n = 0 then 0.0
  else if n mod 2 = 1 then a.(n / 2)
  else (a.((n / 2) - 1) +. a.(n / 2)) /. 2.0

let time_ms f =
  let t0 = Unix.gettimeofday () in
  ignore (f ());
  (Unix.gettimeofday () -. t0) *. 1000.0

let bench reps f = median (List.init reps (fun _ -> time_ms f))

let () =
  let reps = int_of_string Sys.argv.(1) in
  Printf.printf "%-10s %-12s %-12s %-12s\n" "size" "parse_ms" "fastrun_ms"
    "rules_ms";
  for i = 2 to Array.length Sys.argv - 1 do
    let path = Sys.argv.(i) in
    let src = read_file path in
    (* warm *)
    ignore (Latex_parse_lib.Parser_l2.parse_located src);
    ignore (Latex_parse_lib.Validators.run_compile_blocking src);
    let parse =
      bench reps (fun () -> Latex_parse_lib.Parser_l2.parse_located src)
    in
    let fastrun =
      bench reps (fun () ->
          let _n, errs = Latex_parse_lib.Parser_l2.parse_located src in
          Latex_parse_lib.Validators.run_compile_blocking ~parse_errors:errs src)
    in
    Printf.printf "%-10d %-12.1f %-12.1f %-12.1f\n" (String.length src) parse
      fastrun (fastrun -. parse)
  done
