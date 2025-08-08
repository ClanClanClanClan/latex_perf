(* Simple L0 Arena Performance Test *)

let test_arena_performance () =
  Printf.printf "=== L0 ARENA PERFORMANCE TEST ===\n";
  
  (* Create 1.1MB test string *)
  let size = 1_100_000 in
  let test_doc = String.make size 'a' in
  
  (* Initialize if needed *)
  if not !L0_lexer_track_a_arena.initialized then (
    L0_lexer_track_a_arena.StringOps.initialize_builtin_macros ();
    L0_lexer_track_a_arena.initialized := true
  );
  
  (* Time the tokenization *)
  let start = Unix.gettimeofday () in
  let packed_tokens = L0_lexer_track_a_arena.tokenize_arena test_doc in
  let stop = Unix.gettimeofday () in
  
  let elapsed_ms = (stop -. start) *. 1000.0 in
  
  Printf.printf "Document size: %d bytes\n" size;
  Printf.printf "Tokens produced: %d\n" (Array.length packed_tokens);
  Printf.printf "Time: %.2f ms\n" elapsed_ms;
  Printf.printf "Target: ≤20ms\n";
  
  if elapsed_ms <= 20.0 then
    Printf.printf "✅ PASS: Performance target achieved\n"
  else
    Printf.printf "❌ FAIL: Performance target not met\n";
    
  (* Test macro table *)
  Printf.printf "\nMacro table test:\n";
  let has_display_begin = Hashtbl.mem L0_lexer_track_a_arena.StringOps.macro_table "[" in
  let has_display_end = Hashtbl.mem L0_lexer_track_a_arena.StringOps.macro_table "]" in
  Printf.printf "Has '[' macro: %b\n" has_display_begin;
  Printf.printf "Has ']' macro: %b\n" has_display_end;
  Printf.printf "Total macros: %d\n" (Hashtbl.length L0_lexer_track_a_arena.StringOps.macro_table);
  
  if has_display_begin && has_display_end then
    Printf.printf "✅ Display math macros present\n"
  else
    Printf.printf "❌ Display math macros missing\n"

let () = test_arena_performance ()