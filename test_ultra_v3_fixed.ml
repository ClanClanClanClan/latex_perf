(* Test Ultra V3 Fixed Implementation *)

let test_correctness () =
  print_endline "=== ULTRA V3 FIXED CORRECTNESS TEST ===";
  
  let test_cases = [
    ("\\[", "Single-char macro");
    ("\\textbf", "Multi-char macro");
    ("\\[E = mc^2\\]", "Complex expression with display math");
    ("hello", "Plain text");
  ] in
  
  List.iteri (fun i (input, description) ->
    Printf.printf "\n--- Test %d: %s ---\n" (i+1) description;
    Printf.printf "Input: '%s'\n" input;
    
    try
      (* Test tokenization *)
      let tokens = L0_lexer_track_a_ultra_v3_fixed.tokenize input in
      Printf.printf "Tokens: %d\n" (Array.length tokens);
      
      (* Display tokens using PackedToken.to_string *)
      Array.iteri (fun j token ->
        let token_str = L0_lexer_track_a_ultra_v3_fixed.PackedToken.to_string token in
        Printf.printf "  [%d] %s\n" j token_str
      ) tokens;
      
      Printf.printf "✅ SUCCESS\n"
      
    with exn ->
      Printf.printf "❌ ERROR: %s\n" (Printexc.to_string exn)
  ) test_cases

let test_performance () =
  print_endline "\n=== ULTRA V3 FIXED PERFORMANCE TEST ===";
  
  (* Create a test input *)
  let input = String.concat "" [
    "\\documentclass{article}\n";
    "\\begin{document}\n"; 
    "\\section{Introduction}\n";
    "This is a test with \\textbf{bold text} and \\[E = mc^2\\] display math.\n";
    "\\end{document}\n"
  ] in
  
  Printf.printf "Input size: %d bytes\n" (String.length input);
  
  (* Warm up *)
  for _ = 1 to 3 do
    ignore (L0_lexer_track_a_ultra_v3_fixed.tokenize input)
  done;
  
  (* Performance test *)
  let times = ref [] in
  for i = 1 to 10 do
    let start = Sys.time () in
    let tokens = L0_lexer_track_a_ultra_v3_fixed.tokenize input in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    times := elapsed :: !times;
    if i = 1 then
      Printf.printf "Tokens produced: %d\n" (Array.length tokens);
    Printf.printf "Run %d: %.3f ms\n" i elapsed
  done;
  
  let sorted = List.sort compare !times in
  let median = List.nth sorted 5 in
  let p95 = List.nth sorted 9 in
  let avg = (List.fold_left (+.) 0.0 !times) /. 10.0 in
  
  Printf.printf "\nResults:\n";
  Printf.printf "  Median: %.2f ms\n" median;
  Printf.printf "  Average: %.2f ms\n" avg;  
  Printf.printf "  P95: %.2f ms\n" p95;
  
  if p95 <= 20.0 then
    Printf.printf "🎯 TARGET MET! (≤20ms)\n"
  else
    Printf.printf "⚠️  Still over target by %.1fx\n" (p95 /. 20.0)

let () =
  test_correctness ();
  test_performance ();
  print_endline "\n=== ULTRA V3 FIXED TEST COMPLETE ==="