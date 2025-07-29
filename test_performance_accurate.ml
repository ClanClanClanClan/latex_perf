(** Accurate performance test for v25 *)

module L0_v25 = Layer0.L0_v25
module L1_v25 = Layer1.L1_v25
module Orchestrator = Orchestrator_lib.Orchestrator
module Types = Latex_perfectionist_core.Types

let measure_performance () =
  (* Initialize *)
  Orchestrator.init ();
  
  (* Create a more realistic document *)
  let doc = String.concat "\n" [
    "\\documentclass{article}";
    "\\usepackage{amsmath}";
    "\\begin{document}";
    "\\title{Performance Test Document}";
    "\\author{Test Suite}";
    "\\maketitle";
    "";
    "\\section{Introduction}";
    "This is a test document to measure the performance of the \\LaTeX{} ";
    "perfectionist v25 system. We include various \\textbf{formatting} and ";
    "\\emph{emphasis} commands to test macro expansion.";
    "";
    "\\section{Mathematics}";
    "Here is some inline math: $x^2 + y^2 = z^2$. And display math:";
    "\\begin{equation}";
    "  \\int_0^\\infty e^{-x^2} dx = \\frac{\\sqrt{\\pi}}{2}";
    "\\end{equation}";
    "";
    "\\section{Lists}";
    "\\begin{itemize}";
    "  \\item First item with \\textit{italic text}";
    "  \\item Second item with \\textbf{bold text}";
    "  \\item Third item with \\emph{emphasized text}";
    "\\end{itemize}";
    "";
    "\\section{Conclusion}";
    "The \\TeX{} and \\LaTeX{} systems are powerful tools for typesetting.";
    "\\end{document}";
  ] in
  
  let bytes = Bytes.of_string doc in
  
  (* Warm up - 10 iterations *)
  Printf.printf "Warming up...\n";
  for _i = 1 to 10 do
    let _ = Lwt_main.run (Orchestrator.process_edit bytes) in
    ()
  done;
  
  (* Actual measurement - 1000 iterations *)
  let iterations = 1000 in
  Printf.printf "Running %d iterations...\n" iterations;
  
  let times = Array.make iterations 0.0 in
  
  for i = 0 to iterations - 1 do
    let start = Unix.gettimeofday () in
    let _ = Lwt_main.run (Orchestrator.process_edit bytes) in
    let elapsed = Unix.gettimeofday () -. start in
    times.(i) <- elapsed *. 1000.0  (* Convert to ms *)
  done;
  
  (* Calculate statistics *)
  Array.sort compare times;
  let sum = Array.fold_left (+.) 0.0 times in
  let avg = sum /. float iterations in
  let p50 = times.(iterations / 2) in
  let p90 = times.(iterations * 9 / 10) in
  let p95 = times.(iterations * 95 / 100) in
  let p99 = times.(iterations * 99 / 100) in
  let min = times.(0) in
  let max = times.(iterations - 1) in
  
  Printf.printf "\nPerformance Results (%d iterations):\n" iterations;
  Printf.printf "  Document size: %d bytes\n" (Bytes.length bytes);
  Printf.printf "  Min: %.3f ms\n" min;
  Printf.printf "  Avg: %.3f ms\n" avg;
  Printf.printf "  P50: %.3f ms\n" p50;
  Printf.printf "  P90: %.3f ms\n" p90;
  Printf.printf "  P95: %.3f ms\n" p95;
  Printf.printf "  P99: %.3f ms\n" p99;
  Printf.printf "  Max: %.3f ms\n" max;
  Printf.printf "\n";
  Printf.printf "  Target: <1ms for P95\n";
  Printf.printf "  Status: %s\n" (if p95 < 1.0 then "PASS ✅" else "FAIL ❌")

let () = measure_performance ()