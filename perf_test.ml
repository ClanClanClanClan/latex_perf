let load_file filename =
  let ic = open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  content

let test_perf () =
  (* Load test file *)
  let content = load_file "corpora/perf/perf_smoke_big.tex" in
  Printf.printf "File size: %d bytes\n" (String.length content);
  
  (* Warm up *)
  for _ = 1 to 5 do
    ignore (L0_lexer.tokenize content)
  done;
  
  (* Test THE production L0 lexer *)
  let times = ref [] in
  for _ = 1 to 50 do
    let start = Unix.gettimeofday () in
    let tokens = L0_lexer.tokenize content in
    let stop = Unix.gettimeofday () in
    times := (stop -. start) :: !times;
    ignore tokens
  done;
  
  let sorted = List.sort compare !times in
  let median = List.nth sorted 25 in
  let best = List.hd sorted in
  let worst = List.nth sorted 49 in
  
  Printf.printf "\nL0 Lexer Performance (Track A Perfect):\n";
  Printf.printf "  Best: %.2fms\n" (best *. 1000.0);
  Printf.printf "  Median: %.2fms\n" (median *. 1000.0);
  Printf.printf "  Worst: %.2fms\n" (worst *. 1000.0);
  Printf.printf "  Target: ≤20ms\n";
  Printf.printf "  Status: %s\n" 
    (if median *. 1000.0 <= 20.0 then "✅ PASS" else "❌ FAIL")

let () = test_perf ()