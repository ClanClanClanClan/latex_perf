(* Main service entry point *)

let usage_msg = "latex-parse [options] <file>"
let input_file = ref ""
let test_iterations = ref 1000

let spec_list =
  [
    ( "--test",
      Arg.Set_int test_iterations,
      " Run performance test with N iterations" );
  ]

let anon_fun filename = input_file := filename

let setup_service () =
  L0_lexer.Qos.init_for_worker ~core:0;
  L0_lexer.Pretouch.enable_memory_locking ();
  (let _ = L0_lexer.Gc_prep.prepare_gc () in
   ());
  L0_lexer.Alloc_guard.enabled := true

let read_file_to_bytes filename =
  let ic = open_in_bin filename in
  let len = in_channel_length ic in
  let content = Bytes.create len in
  really_input ic content 0 len;
  close_in ic;
  content

let process_single_file filename =
  setup_service ();

  let doc_content = read_file_to_bytes filename in
  let broker =
    L0_lexer.Broker.create_broker "/tmp/l0_primary.sock"
      "/tmp/l0_secondary.sock"
  in

  let timing = L0_lexer.Service_bracket.create_timing () in
  let request =
    { L0_lexer.Ipc.doc_len = Bytes.length doc_content; doc_content }
  in
  let response = L0_lexer.Broker.process_with_hedging broker request in
  let timing_complete = L0_lexer.Service_bracket.complete_timing timing in

  let measurement =
    L0_lexer.Service_bracket.create_measurement timing_complete
      response.token_count response.digest "in-process"
  in

  Printf.printf "{\n";
  Printf.printf "  \"file\": \"%s\",\n" filename;
  Printf.printf "  \"tokens\": %d,\n" response.token_count;
  Printf.printf "  \"process_ms\": %.3f,\n"
    (L0_lexer.Service_bracket.ns_to_ms response.process_ns);
  Printf.printf "  \"service_ms\": %.3f,\n"
    (L0_lexer.Service_bracket.ns_to_ms measurement.service_ns);
  Printf.printf "  \"path\": \"%s\",\n" measurement.path;
  Printf.printf "  \"hedge_rate\": \"%.1f%%\"\n"
    (L0_lexer.Broker.get_hedge_rate broker);
  Printf.printf "}\n"

let run_performance_test iterations =
  setup_service ();

  (* Use a test document - could be hardcoded or read from a file *)
  let test_doc =
    "\\documentclass{article}\n\
     \\begin{document}\n\
     Hello, World!\n\
     \\end{document}\n"
  in
  let doc_content = Bytes.of_string test_doc in
  let broker =
    L0_lexer.Broker.create_broker "/tmp/l0_primary.sock"
      "/tmp/l0_secondary.sock"
  in

  let measurements = Array.make iterations 0.0 in

  Printf.printf "Running %d iterations...\n%!" iterations;

  for i = 0 to iterations - 1 do
    let timing = L0_lexer.Service_bracket.create_timing () in
    let request =
      { L0_lexer.Ipc.doc_len = Bytes.length doc_content; doc_content }
    in
    let _response = L0_lexer.Broker.process_with_hedging broker request in
    let timing_complete = L0_lexer.Service_bracket.complete_timing timing in

    measurements.(i) <-
      L0_lexer.Service_bracket.ns_to_ms timing_complete.reply_ready_ns
      -. L0_lexer.Service_bracket.ns_to_ms timing_complete.bytes_in_ns;

    if (i + 1) mod 1000 = 0 then
      Printf.printf "Completed %d/%d\n%!" (i + 1) iterations
  done;

  (* Calculate percentiles *)
  Array.sort Float.compare measurements;
  let p99 =
    L0_lexer.Percentiles.exact (Array.map (fun x -> x) measurements) 0.99
  in
  let p999 =
    L0_lexer.Percentiles.exact (Array.map (fun x -> x) measurements) 0.999
  in
  let mean =
    Array.fold_left ( +. ) 0.0 measurements /. float_of_int iterations
  in

  Printf.printf "\n=== Performance Results ===\n";
  Printf.printf "Iterations: %d\n" iterations;
  Printf.printf "Mean: %.3fms\n" mean;
  Printf.printf "P99: %.3fms\n" p99;
  Printf.printf "P99.9: %.3fms\n" p999;
  Printf.printf "Hedge rate: %.1f%%\n" (L0_lexer.Broker.get_hedge_rate broker)

let main () =
  Arg.parse spec_list anon_fun usage_msg;

  if !test_iterations > 1 && !input_file = "" then
    run_performance_test !test_iterations
  else if !input_file <> "" then process_single_file !input_file
  else (
    Printf.eprintf "Usage: %s [--test N] <file>\n" Sys.argv.(0);
    exit 1)

let () = main ()
