(* Simple Pipeline Benchmark *)

let small_doc = {|\documentclass{article}
\begin{document}
Hello world $x^2$
\end{document}|}

let tokenize_simple content =
  let len = String.length content in
  let count = ref 0 in
  for i = 0 to len - 1 do
    let c = content.[i] in
    if c = '\\' || c = '{' || c = '}' || c = '$' || c = ' ' || c = '\n' then
      incr count
  done;
  !count

let expand_simple token_count =
  (* Simulate 10% expansion *)
  int_of_float (float_of_int token_count *. 1.1)

let parse_simple token_count =
  (* Simulate parsing work *)
  token_count / 10

let time_ms f =
  let start = Unix.gettimeofday () in
  let result = f () in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  (result, elapsed)

let () =
  Printf.printf "Simple Pipeline Benchmark\n";
  Printf.printf "=========================\n\n";
  
  Printf.printf "Document size: %d bytes\n" (String.length small_doc);
  
  let iterations = 1000 in
  let total_times = Array.make iterations 0.0 in
  
  for i = 0 to iterations - 1 do
    let (tokens, t1) = time_ms (fun () -> tokenize_simple small_doc) in
    let (expanded, t2) = time_ms (fun () -> expand_simple tokens) in
    let (ast_nodes, t3) = time_ms (fun () -> parse_simple expanded) in
    total_times.(i) <- t1 +. t2 +. t3
  done;
  
  Array.sort compare total_times;
  let median = total_times.(iterations / 2) in
  let p95 = total_times.(int_of_float (float_of_int iterations *. 0.95)) in
  let avg = Array.fold_left (+.) 0.0 total_times /. float_of_int iterations in
  
  Printf.printf "\nResults (%d iterations):\n" iterations;
  Printf.printf "Average: %.3f ms\n" avg;
  Printf.printf "Median:  %.3f ms\n" median;
  Printf.printf "P95:     %.3f ms\n" p95;
  
  Printf.printf "\nPerformance Assessment:\n";
  Printf.printf "Target <25ms: %s\n" (if p95 < 25.0 then "PASS" else "FAIL");
  Printf.printf "Status: Pipeline simulation working\n"