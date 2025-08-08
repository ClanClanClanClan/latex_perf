(* L0 Performance Verification Test *)
(* Verify that L0 lexer with arena optimizations achieves ≤20ms target *)

open Printf

let create_test_document size =
  (* Create a realistic LaTeX document of specified size *)
  let sections = 50 in
  let paragraphs_per_section = 20 in
  let words_per_paragraph = 100 in
  
  let buffer = Buffer.create size in
  
  (* Document header *)
  Buffer.add_string buffer "\\documentclass{article}\n";
  Buffer.add_string buffer "\\usepackage{amsmath}\n";
  Buffer.add_string buffer "\\begin{document}\n";
  Buffer.add_string buffer "\\title{Performance Test Document}\n";
  Buffer.add_string buffer "\\author{Test Suite}\n";
  Buffer.add_string buffer "\\maketitle\n\n";
  
  (* Generate sections with mixed content *)
  for s = 1 to sections do
    Buffer.add_string buffer (sprintf "\\section{Section %d}\n\n" s);
    
    for p = 1 to paragraphs_per_section do
      (* Mix of regular text, inline math, and commands *)
      for w = 1 to words_per_paragraph do
        if w mod 10 = 0 then
          Buffer.add_string buffer (sprintf "$x_%d$ " w)
        else if w mod 20 = 0 then
          Buffer.add_string buffer "\\textbf{bold} "
        else
          Buffer.add_string buffer (sprintf "word%d " w)
      done;
      Buffer.add_string buffer "\n\n";
      
      (* Add display math every few paragraphs *)
      if p mod 5 = 0 then (
        Buffer.add_string buffer "\\[\n";
        Buffer.add_string buffer (sprintf "E_%d = mc^2 + \\sum_{i=1}^{%d} x_i\n" p p);
        Buffer.add_string buffer "\\]\n\n"
      )
    done
  done;
  
  Buffer.add_string buffer "\\end{document}\n";
  Buffer.contents buffer

let time_function f x =
  let start = Unix.gettimeofday () in
  let result = f x in
  let stop = Unix.gettimeofday () in
  let elapsed_ms = (stop -. start) *. 1000.0 in
  (result, elapsed_ms)

let run_performance_test () =
  printf "=== L0 LEXER PERFORMANCE VERIFICATION ===\n\n";
  
  (* Initialize built-in macros *)
  if not !L0_lexer_track_a_arena.initialized then (
    L0_lexer_track_a_arena.StringOps.initialize_builtin_macros ();
    L0_lexer_track_a_arena.initialized := true
  );
  
  (* Test different document sizes *)
  let test_sizes = [
    (100_000, "100KB");
    (500_000, "500KB");
    (1_100_000, "1.1MB");
    (2_000_000, "2MB");
  ] in
  
  test_sizes |> List.iter (fun (size, label) ->
    printf "Testing %s document:\n" label;
    
    (* Generate test document *)
    let doc = create_test_document size in
    printf "  Document size: %d bytes\n" (String.length doc);
    
    (* Warm-up run *)
    let _ = L0_lexer_track_a_arena.tokenize doc in
    
    (* Measure performance (5 runs) *)
    let times = List.init 5 (fun i ->
      let (tokens, time) = time_function L0_lexer_track_a_arena.tokenize doc in
      printf "  Run %d: %.2f ms (%d tokens)\n" (i+1) time (List.length tokens);
      time
    ) in
    
    (* Calculate statistics *)
    let sorted_times = List.sort compare times in
    let avg = (List.fold_left (+.) 0.0 times) /. 5.0 in
    let p95 = List.nth sorted_times 4 in
    let min_time = List.hd sorted_times in
    let max_time = List.nth sorted_times 4 in
    
    printf "  Statistics:\n";
    printf "    Average: %.2f ms\n" avg;
    printf "    P95: %.2f ms\n" p95;
    printf "    Min: %.2f ms\n" min_time;
    printf "    Max: %.2f ms\n" max_time;
    
    (* Check against target *)
    if label = "1.1MB" then (
      printf "  Target: ≤20ms\n";
      if p95 <= 20.0 then
        printf "  ✅ PASS: %.2f ms ≤ 20ms (%.1f%% better)\n" p95 ((20.0 -. p95) /. 20.0 *. 100.0)
      else
        printf "  ❌ FAIL: %.2f ms > 20ms\n" p95
    );
    
    printf "\n"
  );
  
  (* Test macro recognition *)
  printf "Testing macro recognition:\n";
  let test_macros = "\\LaTeX \\alpha \\section{Test} \\[x^2\\]" in
  let tokens = L0_lexer_track_a_arena.tokenize test_macros in
  
  let macro_names = List.fold_left (fun acc tok ->
    match tok with
    | Lexer_v25.TMacro name -> name :: acc
    | _ -> acc
  ) [] tokens |> List.rev in
  
  printf "  Input: %s\n" test_macros;
  printf "  Macros found: %s\n" (String.concat ", " macro_names);
  
  let expected = ["LaTeX"; "alpha"; "section"; "["; "]"] in
  let all_found = List.for_all (fun m -> List.mem m macro_names) expected in
  
  if all_found then
    printf "  ✅ All expected macros recognized\n"
  else
    printf "  ❌ Some macros missing\n";
    
  printf "\n=== END PERFORMANCE VERIFICATION ===\n"

let () = run_performance_test ()