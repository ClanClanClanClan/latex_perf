(* Fault Injection Testing for SIMD v2 Service *)

open Printf
open Latex_parse_lib

let socket_path = "/tmp/l0_lex_svc.sock"

(* Get worker PIDs from service *)
let get_worker_pids () =
  (* In a real implementation, this would query the service for worker PIDs *)
  (* For now, return empty list - workers will be discovered during testing *)
  []

(* Run a specific fault injection test *)
let run_test test_name =
  printf "=== Running Fault Injection Test: %s ===\n%!" test_name;

  let worker_pids = get_worker_pids () in

  (* Execute the fault scenario *)
  Fault_injection.run_scenario test_name worker_pids socket_path;

  (* Wait a bit for system to stabilize *)
  Thread.delay 2.0;

  (* Check if service recovered *)
  let recovered = Fault_injection.check_recovery socket_path in

  printf "Test %s: %s\n%!"
    test_name
    (if recovered then "PASSED ✓" else "FAILED ✗");

  recovered

(* Run all fault injection tests *)
let run_all_tests () =
  let tests = [
    "worker_chaos";
    "network_issues";
    "resource_stress";
    "broker_flood";
    "combined_chaos";
  ] in

  let results = List.map (fun test ->
    let passed = run_test test in
    Thread.delay 3.0;  (* Give time between tests *)
    (test, passed)
  ) tests in

  (* Print summary *)
  printf "\n=== Fault Injection Test Summary ===\n";
  List.iter (fun (test, passed) ->
    printf "  %s: %s\n"
      test
      (if passed then "✓ PASSED" else "✗ FAILED")
  ) results;

  let passed_count = List.length (List.filter snd results) in
  let total_count = List.length results in

  printf "\nTotal: %d/%d tests passed\n%!" passed_count total_count;

  if passed_count = total_count then
    printf "✓ All fault injection tests passed!\n%!"
  else
    printf "✗ Some tests failed - service needs hardening\n%!"

(* Interactive fault injection mode *)
let interactive_mode () =
  printf "=== Interactive Fault Injection Mode ===\n";
  printf "Commands:\n";
  printf "  1 - Worker crash\n";
  printf "  2 - Network delay\n";
  printf "  3 - Memory pressure\n";
  printf "  4 - CPU spike\n";
  printf "  5 - I/O block\n";
  printf "  6 - Broker flood\n";
  printf "  7 - Random fault\n";
  printf "  8 - Check recovery\n";
  printf "  9 - Run all tests\n";
  printf "  0 - Exit\n\n";

  (* Enable fault injection *)
  Fault_injection.configure
    ~enabled:true
    ~probability:1.0
    ~faults:[]
    ~seed:None;

  let rec loop () =
    printf "> %!";
    try
      let line = input_line stdin in
      match line with
      | "0" -> printf "Exiting...\n%!"
      | "1" ->
        printf "Enter worker PID: %!";
        let pid = int_of_string (input_line stdin) in
        Fault_injection.inject_fault (WorkerCrash pid);
        loop ()
      | "2" ->
        printf "Enter delay (seconds): %!";
        let delay = float_of_string (input_line stdin) in
        Fault_injection.inject_fault (NetworkDelay delay);
        loop ()
      | "3" ->
        printf "Enter memory (MB): %!";
        let mb = int_of_string (input_line stdin) in
        Fault_injection.inject_fault (MemoryPressure mb);
        loop ()
      | "4" ->
        printf "Enter duration (seconds): %!";
        let duration = float_of_string (input_line stdin) in
        Fault_injection.inject_fault (CPUSpike duration);
        loop ()
      | "5" ->
        printf "Enter duration (seconds): %!";
        let duration = float_of_string (input_line stdin) in
        Fault_injection.inject_fault (IOBlock duration);
        loop ()
      | "6" ->
        printf "Enter request count: %!";
        let count = int_of_string (input_line stdin) in
        Fault_injection.inject_broker_overload socket_path count;
        loop ()
      | "7" ->
        Fault_injection.trigger_random_fault ();
        loop ()
      | "8" ->
        let recovered = Fault_injection.check_recovery socket_path in
        printf "Service %s\n%!"
          (if recovered then "is healthy ✓" else "is not responding ✗");
        loop ()
      | "9" ->
        run_all_tests ();
        loop ()
      | _ ->
        printf "Unknown command\n%!";
        loop ()
    with
    | End_of_file -> printf "\nExiting...\n%!"
    | exn ->
      printf "Error: %s\n%!" (Printexc.to_string exn);
      loop ()
  in
  loop ()

(* Main entry point *)
let () =
  let args = Array.to_list Sys.argv in

  match args with
  | _ :: "--all" :: _ ->
    run_all_tests ()
  | _ :: "--test" :: test_name :: _ ->
    ignore (run_test test_name)
  | _ :: "--interactive" :: _ ->
    interactive_mode ()
  | _ ->
    printf "Usage: %s [OPTIONS]\n" Sys.argv.(0);
    printf "Options:\n";
    printf "  --all              Run all fault injection tests\n";
    printf "  --test <name>      Run specific test\n";
    printf "  --interactive      Interactive fault injection mode\n";
    printf "\nAvailable tests:\n";
    printf "  worker_chaos       Random worker crashes\n";
    printf "  network_issues     Network delays and failures\n";
    printf "  resource_stress    Memory and CPU pressure\n";
    printf "  broker_flood       Overwhelm broker with requests\n";
    printf "  combined_chaos     All faults combined\n"