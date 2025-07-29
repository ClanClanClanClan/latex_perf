(* benchmark.ml - Real performance benchmark for v24-R3 *)

open Latex_perfectionist_incremental

(* Generate realistic LaTeX document *)
let generate_latex_document ~lines ~complexity =
  let buffer = Buffer.create (lines * 100) in
  
  (* Document header *)
  Buffer.add_string buffer "\\documentclass[11pt,a4paper]{article}\n";
  Buffer.add_string buffer "\\usepackage{amsmath,amsthm,amssymb,amsfonts}\n";
  Buffer.add_string buffer "\\usepackage{graphicx,color,xcolor}\n";
  Buffer.add_string buffer "\\usepackage{hyperref,url}\n";
  Buffer.add_string buffer "\\usepackage{listings,verbatim}\n";
  Buffer.add_string buffer "\\usepackage{tikz,pgfplots}\n";
  Buffer.add_string buffer "\\usepackage{algorithm,algorithmic}\n";
  Buffer.add_string buffer "\\usepackage{theorem}\n\n";
  
  (* Custom definitions *)
  Buffer.add_string buffer "\\newcommand{\\R}{\\mathbb{R}}\n";
  Buffer.add_string buffer "\\newcommand{\\N}{\\mathbb{N}}\n";
  Buffer.add_string buffer "\\newcommand{\\Z}{\\mathbb{Z}}\n";
  Buffer.add_string buffer "\\newcommand{\\Q}{\\mathbb{Q}}\n";
  Buffer.add_string buffer "\\newcommand{\\C}{\\mathbb{C}}\n";
  Buffer.add_string buffer "\\newtheorem{theorem}{Theorem}[section]\n";
  Buffer.add_string buffer "\\newtheorem{lemma}[theorem]{Lemma}\n";
  Buffer.add_string buffer "\\newtheorem{proposition}[theorem]{Proposition}\n";
  Buffer.add_string buffer "\\newtheorem{corollary}[theorem]{Corollary}\n";
  Buffer.add_string buffer "\\newtheorem{definition}[theorem]{Definition}\n\n";
  
  Buffer.add_string buffer "\\begin{document}\n";
  Buffer.add_string buffer "\\title{Performance Benchmark Document\\\\";
  Buffer.add_string buffer "LaTeX Perfectionist v24-R3 Testing}\n";
  Buffer.add_string buffer "\\author{Automated Generator}\n";
  Buffer.add_string buffer "\\date{\\today}\n";
  Buffer.add_string buffer "\\maketitle\n\n";
  
  (* Abstract *)
  Buffer.add_string buffer "\\begin{abstract}\n";
  Buffer.add_string buffer "This document tests the incremental lexing performance ";
  Buffer.add_string buffer "of LaTeX Perfectionist v24-R3. It contains various ";
  Buffer.add_string buffer "mathematical expressions, code listings, tables, and ";
  Buffer.add_string buffer "other complex LaTeX constructs to stress-test the ";
  Buffer.add_string buffer "incremental processing capabilities.\n";
  Buffer.add_string buffer "\\end{abstract}\n\n";
  
  (* Generate content *)
  let sections = max 1 (lines / 300) in
  let current_line = ref 30 in
  
  for s = 1 to sections do
    Buffer.add_string buffer (Printf.sprintf "\\section{Section %d: Mathematical Analysis}\n\n" s);
    incr current_line; incr current_line;
    
    (* Introduction paragraph *)
    Buffer.add_string buffer "This section explores fundamental concepts in ";
    Buffer.add_string buffer "mathematical analysis with applications to real-world ";
    Buffer.add_string buffer "problems. We begin with basic definitions and proceed ";
    Buffer.add_string buffer "to more advanced topics.\n\n";
    current_line := !current_line + 4;
    
    (* Add subsections *)
    let subsections = 3 in
    for ss = 1 to subsections do
      Buffer.add_string buffer (Printf.sprintf "\\subsection{Topic %d.%d}\n\n" s ss);
      current_line := !current_line + 2;
      
      (* Theorem if complexity is high *)
      if complexity > 0.7 && ss = 1 then begin
        Buffer.add_string buffer "\\begin{theorem}\\label{thm:main}\n";
        Buffer.add_string buffer "Let $f: \\R^n \\to \\R$ be a continuous function ";
        Buffer.add_string buffer "satisfying the Lipschitz condition:\n";
        Buffer.add_string buffer "\\begin{equation}\\label{eq:lipschitz}\n";
        Buffer.add_string buffer "  |f(x) - f(y)| \\leq L \\|x - y\\|_2\n";
        Buffer.add_string buffer "\\end{equation}\n";
        Buffer.add_string buffer "for some constant $L > 0$. Then $f$ is uniformly continuous.\n";
        Buffer.add_string buffer "\\end{theorem}\n\n";
        current_line := !current_line + 8;
        
        Buffer.add_string buffer "\\begin{proof}\n";
        Buffer.add_string buffer "Choose $\\delta = \\epsilon / L$ for any $\\epsilon > 0$. ";
        Buffer.add_string buffer "If $\\|x - y\\|_2 < \\delta$, then by the Lipschitz condition:\n";
        Buffer.add_string buffer "\\begin{align}\n";
        Buffer.add_string buffer "  |f(x) - f(y)| &\\leq L \\|x - y\\|_2\\\\\n";
        Buffer.add_string buffer "                 &< L \\cdot \\frac{\\epsilon}{L}\\\\\n";
        Buffer.add_string buffer "                 &= \\epsilon\n";
        Buffer.add_string buffer "\\end{align}\n";
        Buffer.add_string buffer "This completes the proof.";
        Buffer.add_string buffer "\\end{proof}\n\n";
        current_line := !current_line + 10;
      end;
      
      (* Regular content *)
      while !current_line < (s * lines / sections) + (ss * lines / sections / subsections) do
        let content_type = Random.int 12 in
        
        match content_type with
        | 0 | 1 | 2 ->  (* Normal text with inline math *)
            Buffer.add_string buffer "Consider the function $g(x) = ";
            Buffer.add_string buffer (Printf.sprintf "x^%d + \\sin(%dx) + \\log(x^2 + %d)$ " 
              (Random.int 5 + 1) (Random.int 3 + 1) (Random.int 10 + 1));
            Buffer.add_string buffer "which exhibits interesting behavior near the origin. ";
            Buffer.add_string buffer "The derivative $g'(x)$ can be computed using standard ";
            Buffer.add_string buffer "calculus techniques. % Mathematical analysis\n";
            incr current_line
            
        | 3 ->  (* Display equation *)
            Buffer.add_string buffer "The fundamental theorem states:\n";
            Buffer.add_string buffer "\\begin{equation}\n";
            Buffer.add_string buffer (Printf.sprintf "  \\int_0^\\infty e^{-\\alpha x^2} dx = \\frac{\\sqrt{\\pi}}{2\\sqrt{\\alpha}}, \\quad \\alpha > 0\n");
            Buffer.add_string buffer "\\end{equation}\n";
            current_line := !current_line + 4
            
        | 4 ->  (* Align environment *)
            Buffer.add_string buffer "\\begin{align}\n";
            Buffer.add_string buffer "  \\nabla \\cdot \\mathbf{E} &= \\frac{\\rho}{\\epsilon_0} \\\\\n";
            Buffer.add_string buffer "  \\nabla \\cdot \\mathbf{B} &= 0 \\\\\n";
            Buffer.add_string buffer "  \\nabla \\times \\mathbf{E} &= -\\frac{\\partial \\mathbf{B}}{\\partial t} \\\\\n";
            Buffer.add_string buffer "  \\nabla \\times \\mathbf{B} &= \\mu_0 \\mathbf{J} + \\mu_0 \\epsilon_0 \\frac{\\partial \\mathbf{E}}{\\partial t}\n";
            Buffer.add_string buffer "\\end{align}\n";
            current_line := !current_line + 7
            
        | 5 ->  (* Itemize list *)
            Buffer.add_string buffer "The main properties include:\n";
            Buffer.add_string buffer "\\begin{itemize}\n";
            Buffer.add_string buffer "  \\item Continuity: $f$ is continuous at every point\n";
            Buffer.add_string buffer "  \\item Differentiability: $f'(x)$ exists for all $x \\in \\R$\n";
            Buffer.add_string buffer "  \\item Boundedness: $|f(x)| \\leq M$ for some constant $M$\n";
            Buffer.add_string buffer "  \\item Periodicity: $f(x + T) = f(x)$ with period $T = 2\\pi$\n";
            Buffer.add_string buffer "\\end{itemize}\n";
            current_line := !current_line + 7
            
        | 6 when complexity > 0.5 ->  (* Code listing *)
            Buffer.add_string buffer "\\begin{lstlisting}[language=Python,caption=Algorithm Implementation]\n";
            Buffer.add_string buffer "def newton_method(f, df, x0, tol=1e-10, max_iter=100):\n";
            Buffer.add_string buffer "    \"\"\"Newton's method for finding roots\"\"\"\n";
            Buffer.add_string buffer "    x = x0\n";
            Buffer.add_string buffer "    for i in range(max_iter):\n";
            Buffer.add_string buffer "        fx = f(x)\n";
            Buffer.add_string buffer "        if abs(fx) < tol:\n";
            Buffer.add_string buffer "            return x, i\n";
            Buffer.add_string buffer "        dfx = df(x)\n";
            Buffer.add_string buffer "        if abs(dfx) < 1e-15:\n";
            Buffer.add_string buffer "            raise ValueError('Derivative too small')\n";
            Buffer.add_string buffer "        x = x - fx / dfx\n";
            Buffer.add_string buffer "    return x, max_iter\n";
            Buffer.add_string buffer "\\end{lstlisting}\n";
            current_line := !current_line + 14
            
        | 7 when complexity > 0.6 ->  (* Table *)
            Buffer.add_string buffer "\\begin{table}[h]\n";
            Buffer.add_string buffer "\\centering\n";
            Buffer.add_string buffer "\\begin{tabular}{|c|c|c|c|}\n";
            Buffer.add_string buffer "\\hline\n";
            Buffer.add_string buffer "$n$ & $f(n)$ & $g(n)$ & $h(n)$ \\\\\n";
            Buffer.add_string buffer "\\hline\n";
            for i = 1 to 5 do
              Buffer.add_string buffer (Printf.sprintf "%d & %d & %.3f & $10^{%d}$ \\\\\n" 
                i (i*i) (sin (float_of_int i)) i)
            done;
            Buffer.add_string buffer "\\hline\n";
            Buffer.add_string buffer "\\end{tabular}\n";
            Buffer.add_string buffer "\\caption{Numerical Results}\n";
            Buffer.add_string buffer "\\label{tab:results}\n";
            Buffer.add_string buffer "\\end{table}\n";
            current_line := !current_line + 12
            
        | 8 when complexity > 0.8 ->  (* TikZ figure *)
            Buffer.add_string buffer "\\begin{figure}[h]\n";
            Buffer.add_string buffer "\\centering\n";
            Buffer.add_string buffer "\\begin{tikzpicture}\n";
            Buffer.add_string buffer "  \\draw[->] (-2,0) -- (2,0) node[right] {$x$};\n";
            Buffer.add_string buffer "  \\draw[->] (0,-1) -- (0,2) node[above] {$y$};\n";
            Buffer.add_string buffer "  \\draw[domain=-1.5:1.5,smooth,variable=\\x,blue,thick] plot ({\\x},{\\x*\\x});\n";
            Buffer.add_string buffer "  \\node[below] at (0,0) {$O$};\n";
            Buffer.add_string buffer "\\end{tikzpicture}\n";
            Buffer.add_string buffer "\\caption{Graph of $y = x^2$}\n";
            Buffer.add_string buffer "\\label{fig:parabola}\n";
            Buffer.add_string buffer "\\end{figure}\n";
            current_line := !current_line + 10
            
        | 9 ->  (* Reference paragraph *)
            Buffer.add_string buffer "As shown in Theorem \\ref{thm:main}, the properties ";
            Buffer.add_string buffer "established in Section \\ref{sec:intro} lead to important ";
            Buffer.add_string buffer "consequences. See also \\cite{author2023,book2022} for ";
            Buffer.add_string buffer "additional details and Figure \\ref{fig:parabola} for ";
            Buffer.add_string buffer "a graphical illustration.\n";
            incr current_line
            
        | _ ->  (* Plain paragraph *)
            Buffer.add_string buffer "This paragraph contains regular text without special ";
            Buffer.add_string buffer "formatting. It serves as filler content to test the lexer's ";
            Buffer.add_string buffer "performance on ordinary text. The goal is to create realistic ";
            Buffer.add_string buffer "document structure with mixed content types.\n";
            incr current_line
      done;
      
      Buffer.add_string buffer "\n"
    done;
    
    Buffer.add_string buffer "\n"
  done;
  
  (* Bibliography *)
  Buffer.add_string buffer "\\begin{thebibliography}{99}\n";
  Buffer.add_string buffer "\\bibitem{author2023} A. Author, ``Important Results'', ";
  Buffer.add_string buffer "Journal of Advanced Mathematics, vol. 42, pp. 123-145, 2023.\n";
  Buffer.add_string buffer "\\bibitem{book2022} B. Book, \\emph{Comprehensive Analysis}, ";
  Buffer.add_string buffer "Academic Press, 2022.\n";
  Buffer.add_string buffer "\\end{thebibliography}\n\n";
  
  Buffer.add_string buffer "\\end{document}\n";
  
  Buffer.contents buffer

(* Run performance benchmark *)
let run_benchmark () =
  Printf.printf "=== LaTeX Perfectionist v24-R3 Real Performance Benchmark ===\n\n";
  
  (* Test configurations *)
  let test_configs = [
    (1_000, 0.3, "Small document (1K lines, simple)");
    (1_000, 0.8, "Small document (1K lines, complex)");
    (10_000, 0.5, "Medium document (10K lines)");
    (50_000, 0.7, "Large document (50K lines)");
    (100_000, 0.9, "Huge document (100K lines)");
  ] in
  
  List.iter (fun (lines, complexity, desc) ->
    Printf.printf "\n%s:\n" desc;
    Printf.printf "%s\n" (String.make (String.length desc + 1) '=');
    
    (* Generate document *)
    Printf.printf "Generating LaTeX document... ";
    flush_all ();
    let content = generate_latex_document ~lines ~complexity in
    let size_mb = float_of_int (String.length content) /. 1024.0 /. 1024.0 in
    Printf.printf "%.2f MB\n" size_mb;
    
    (* Create optimized lexer *)
    let lexer = Incremental_lexer_optimized.create_optimized () in
    
    (* Measure initial lexing *)
    Printf.printf "Initial lexing... ";
    flush_all ();
    let start = Unix.gettimeofday () in
    Incremental_lexer_optimized.load_string lexer content;
    let initial_time = Unix.gettimeofday () -. start in
    Printf.printf "%.2f ms (%.1f MB/s)\n" 
      (initial_time *. 1000.0)
      (size_mb /. initial_time);
    
    (* Test edit patterns *)
    let edit_patterns = [
      ("Single character", fun () -> 
        Incremental_lexer_optimized.edit_line lexer (lines / 2) "% Single char edit");
      
      ("Command change", fun () ->
        Incremental_lexer_optimized.edit_line lexer (lines / 4) 
          "\\section{Modified Section Title}");
      
      ("Math equation", fun () ->
        Incremental_lexer_optimized.edit_line lexer (3 * lines / 4)
          "\\begin{equation} E = mc^2 + \\hbar \\omega \\end{equation}");
      
      ("Comment addition", fun () ->
        Incremental_lexer_optimized.edit_line lexer (lines / 10)
          "% TODO: This needs to be fixed");
      
      ("Multiple edits", fun () ->
        let _ = Incremental_lexer_optimized.edit_line lexer (lines / 6) "% Edit 1" in
        let _ = Incremental_lexer_optimized.edit_line lexer (lines / 3) "% Edit 2" in
        Incremental_lexer_optimized.edit_line lexer (lines / 2) "% Edit 3");
    ] in
    
    Printf.printf "\nEdit Performance:\n";
    List.iter (fun (name, edit_fn) ->
      let lines_proc, _, time_ms = edit_fn () in
      let speedup = initial_time *. 1000.0 /. time_ms in
      
      Printf.printf "  %-20s: %6.2f ms, %4d lines, %8.0fx speedup\n"
        name time_ms lines_proc speedup
    ) edit_patterns;
    
    (* Overall performance statistics *)
    let achieved_speedup = Incremental_lexer_optimized.calculate_achieved_speedup lexer in
    Printf.printf "\nOverall Performance:\n";
    Printf.printf "  Achieved speedup: %.0fx\n" achieved_speedup;
    
    if achieved_speedup >= 1596.0 then
      Printf.printf "  ✅ TARGET ACHIEVED! (%.1f%% of target)\n" 
        (achieved_speedup /. 1596.0 *. 100.0)
    else
      Printf.printf "  ❌ Below target: %.0fx / 1,596x = %.1f%%\n"
        achieved_speedup (achieved_speedup /. 1596.0 *. 100.0);
    
    (* Detailed stats *)
    if achieved_speedup >= 1000.0 then begin
      Printf.printf "\nDetailed Statistics:\n";
      let stats = Incremental_lexer_optimized.get_performance_stats lexer in
      Printf.printf "%s\n" stats
    end
    
  ) test_configs;
  
  Printf.printf "\n=== Benchmark Complete ===\n"

(* Command line interface *)
let () =
  Random.self_init ();
  
  if Array.length Sys.argv > 1 then
    match Sys.argv.(1) with
    | "--help" | "-h" ->
        Printf.printf "LaTeX Perfectionist v24-R3 Benchmark\n";
        Printf.printf "Usage: %s [options]\n" Sys.argv.(0);
        Printf.printf "Options:\n";
        Printf.printf "  --help, -h    Show this help\n";
        Printf.printf "  --parallel    Test parallel processing\n";
        Printf.printf "  --cache       Test cache performance\n"
    | "--parallel" ->
        Printf.printf "Testing parallel processing...\n";
        let lines = Array.init 10000 (fun i -> Printf.sprintf "Line %d with content" i) in
        Parallel_processor.benchmark_parallel lines
    | "--cache" ->
        Printf.printf "Testing cache performance...\n";
        State_cache.warm_cache ();
        Printf.printf "%s\n" (State_cache.get_stats ())
    | _ ->
        run_benchmark ()
  else
    run_benchmark ()