(* Standalone L0 Performance Test - Minimal Dependencies *)

(* Create a simple 1.1MB test *)
let test_doc = String.make 1_100_000 'x'

(* Simple timer *)
let time_it f =
  let start = Sys.time () in
  let result = f () in
  let stop = Sys.time () in
  let elapsed_ms = (stop -. start) *. 1000.0 in
  (result, elapsed_ms)

let () =
  Printf.printf "\n=== STANDALONE L0 PERFORMANCE TEST ===\n";
  Printf.printf "Testing with %d byte document\n\n" (String.length test_doc);
  
  (* First, let's check what lexer we can access *)
  try
    (* Try to use L0_lexer module *)
    let module L = Core.L0_lexer in
    Printf.printf "✅ Found Core.L0_lexer module\n";
    
    (* Warm-up *)
    Printf.printf "Warming up...\n";
    let _ = L.tokenize test_doc in
    
    (* Run 5 timed tests *)
    Printf.printf "\nRunning timed tests:\n";
    let times = ref [] in
    
    for i = 1 to 5 do
      let (tokens, elapsed) = time_it (fun () -> L.tokenize test_doc) in
      Printf.printf "  Run %d: %.2f ms (%d tokens)\n" i elapsed (List.length tokens);
      times := elapsed :: !times
    done;
    
    (* Calculate stats *)
    let sorted_times = List.sort compare !times in
    let p95 = List.nth sorted_times 4 in
    let avg = (List.fold_left (+.) 0.0 !times) /. 5.0 in
    
    Printf.printf "\nResults:\n";
    Printf.printf "  Average: %.2f ms\n" avg;
    Printf.printf "  P95: %.2f ms\n" p95;
    Printf.printf "  Target: ≤20ms\n\n";
    
    if p95 <= 20.0 then
      Printf.printf "✅ PERFORMANCE TARGET MET! (%.1fx better)\n" (20.0 /. p95)
    else
      Printf.printf "❌ Performance: %.2f ms (need %.1fx improvement)\n" p95 (p95 /. 20.0)
      
  with exn ->
    Printf.printf "❌ Error: %s\n" (Printexc.to_string exn);
    Printf.printf "\nTrying alternate module names...\n";
    
    (* Try L0_lexer_track_a_arena *)
    try
      Printf.printf "Testing L0_lexer_track_a_arena...\n";
      let _ = L0_lexer_track_a_arena.tokenize test_doc in
      Printf.printf "✅ L0_lexer_track_a_arena works!\n"
    with e ->
      Printf.printf "❌ L0_lexer_track_a_arena failed: %s\n" (Printexc.to_string e)