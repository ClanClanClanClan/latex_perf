(* real_performance_test.ml - Actual performance measurements *)

open Line_processor_real

(* Generate realistic LaTeX document *)
let generate_latex_document ~lines ~complexity =
  let buffer = Buffer.create (lines * 100) in
  
  (* Document preamble *)
  Buffer.add_string buffer "\\documentclass[11pt,a4paper]{article}\n";
  Buffer.add_string buffer "\\usepackage{amsmath,amsthm,amssymb}\n";
  Buffer.add_string buffer "\\usepackage{graphicx}\n";
  Buffer.add_string buffer "\\usepackage{hyperref}\n";
  Buffer.add_string buffer "\\usepackage{listings}\n";
  Buffer.add_string buffer "\\usepackage{tikz}\n";
  Buffer.add_string buffer "\n";
  
  (* Custom commands *)
  Buffer.add_string buffer "\\newcommand{\\R}{\\mathbb{R}}\n";
  Buffer.add_string buffer "\\newcommand{\\N}{\\mathbb{N}}\n";
  Buffer.add_string buffer "\\newtheorem{theorem}{Theorem}\n";
  Buffer.add_string buffer "\\newtheorem{lemma}[theorem]{Lemma}\n";
  Buffer.add_string buffer "\n";
  
  Buffer.add_string buffer "\\begin{document}\n";
  Buffer.add_string buffer "\\title{Performance Benchmark Document}\n";
  Buffer.add_string buffer "\\author{LaTeX Perfectionist v24-R3}\n";
  Buffer.add_string buffer "\\maketitle\n\n";
  
  (* Generate content *)
  let sections = lines / 200 in
  let current_line = ref 20 in
  
  for s = 1 to sections do
    Buffer.add_string buffer (Printf.sprintf "\\section{Section %d}\n\n" s);
    incr current_line;
    
    (* Add some theorems *)
    if complexity > 0.5 then begin
      Buffer.add_string buffer "\\begin{theorem}\n";
      Buffer.add_string buffer "Let $f: \\R \\to \\R$ be a continuous function. ";
      Buffer.add_string buffer "If $\\int_0^1 |f(x)|^2 dx < \\infty$, then\n";
      Buffer.add_string buffer "\\begin{equation}\n";
      Buffer.add_string buffer "  \\sum_{n=1}^\\infty \\frac{1}{n^2} |\\hat{f}(n)|^2 \\leq ";
      Buffer.add_string buffer "\\int_0^1 |f(x)|^2 dx\n";
      Buffer.add_string buffer "\\end{equation}\n";
      Buffer.add_string buffer "\\end{theorem}\n\n";
      current_line := !current_line + 7;
    end;
    
    (* Regular paragraphs *)
    while !current_line < (s + 1) * (lines / sections) do
      let para_type = Random.int 10 in
      
      match para_type with
      | 0 | 1 ->  (* Text with inline math *)
          Buffer.add_string buffer "This is a paragraph with inline mathematics ";
          Buffer.add_string buffer (Printf.sprintf "$x_%d + y_%d = z_%d$ " s !current_line s);
          Buffer.add_string buffer "and some \\textbf{bold} and \\emph{emphasized} text. ";
          Buffer.add_string buffer "% This is a comment\n";
          incr current_line
          
      | 2 ->  (* Display math *)
          Buffer.add_string buffer "Consider the following integral:\n";
          Buffer.add_string buffer "\\begin{equation}\n";
          Buffer.add_string buffer (Printf.sprintf "  I_%d = \\int_0^\\infty e^{-x^2} dx = \\frac{\\sqrt{\\pi}}{2}\n" !current_line);
          Buffer.add_string buffer "\\end{equation}\n";
          current_line := !current_line + 4
          
      | 3 ->  (* Itemize *)
          Buffer.add_string buffer "\\begin{itemize}\n";
          for i = 1 to 3 do
            Buffer.add_string buffer (Printf.sprintf "  \\item Item %d with math $a_%d$\n" i i);
          done;
          Buffer.add_string buffer "\\end{itemize}\n";
          current_line := !current_line + 5
          
      | 4 when complexity > 0.7 ->  (* Code listing *)
          Buffer.add_string buffer "\\begin{lstlisting}[language=Python]\n";
          Buffer.add_string buffer "def factorial(n):\n";
          Buffer.add_string buffer "    return 1 if n <= 1 else n * factorial(n-1)\n";
          Buffer.add_string buffer "\\end{lstlisting}\n";
          current_line := !current_line + 4
          
      | 5 when complexity > 0.8 ->  (* TikZ diagram *)
          Buffer.add_string buffer "\\begin{tikzpicture}\n";
          Buffer.add_string buffer "  \\draw (0,0) circle (1cm);\n";
          Buffer.add_string buffer "  \\draw (0,0) -- (1,0);\n";
          Buffer.add_string buffer "\\end{tikzpicture}\n";
          current_line := !current_line + 4
          
      | _ ->  (* Plain text *)
          Buffer.add_string buffer (Printf.sprintf "This is line %d of the document. " !current_line);
          Buffer.add_string buffer "It contains regular text without special formatting.\n";
          incr current_line
    done;
    
    Buffer.add_string buffer "\n"
  done;
  
  Buffer.add_string buffer "\\end{document}\n";
  
  (* Convert to lines *)
  Buffer.contents buffer |> String.split_on_char '\n' |> Array.of_list

(* Benchmark edit patterns *)
type edit_pattern =
  | SingleChar of int * string
  | MultiLine of (int * string) list
  | InsertSection of int * string
  | DeleteLines of int * int
  | ModifyPreamble of string

let apply_edit_pattern doc pattern =
  match pattern with
  | SingleChar (line, text) ->
      apply_edit doc line text
  | MultiLine edits ->
      let total_lines = ref 0 in
      let total_bytes = ref 0 in
      let total_time = ref 0 in
      List.iter (fun (line, text) ->
        let lines, bytes, time = apply_edit doc line text in
        total_lines := !total_lines + lines;
        total_bytes := !total_bytes + bytes;
        total_time := !total_time + time;
      ) edits;
      (!total_lines, !total_bytes, !total_time)
  | InsertSection (line, name) ->
      let text = Printf.sprintf "\\section{%s}" name in
      apply_edit doc line text
  | DeleteLines (start, count) ->
      (* Simulate by replacing with empty *)
      let total_lines = ref 0 in
      let total_bytes = ref 0 in
      let total_time = ref 0 in
      for i = start to min (start + count - 1) (Array.length doc.lines - 1) do
        let lines, bytes, time = apply_edit doc i "" in
        total_lines := !total_lines + lines;
        total_bytes := !total_bytes + bytes;
        total_time := !total_time + time;
      done;
      (!total_lines, !total_bytes, !total_time)
  | ModifyPreamble new_cmd ->
      (* Find and modify preamble *)
      let preamble_line = ref None in
      for i = 0 to min 50 (Array.length doc.lines - 1) do
        if String.contains doc.lines.(i) "\\begin{document}" then begin
          preamble_line := Some (i - 1);
        end
      done;
      match !preamble_line with
      | Some line -> apply_edit doc line new_cmd
      | None -> (0, 0, 0)

(* Run benchmark *)
let run_benchmark () =
  Printf.printf "=== LaTeX Perfectionist v24-R3 Real Performance Benchmark ===\n\n";
  
  (* Test configurations *)
  let configs = [
    (1_000, 0.5, "Small document (1K lines)");
    (10_000, 0.7, "Medium document (10K lines)");
    (50_000, 0.8, "Large document (50K lines)");
    (100_000, 0.9, "Huge document (100K lines)");
  ] in
  
  List.iter (fun (lines, complexity, desc) ->
    Printf.printf "Testing: %s\n" desc;
    Printf.printf "Generating document...\n";
    
    let doc_lines = generate_latex_document ~lines ~complexity in
    let doc_size = Array.fold_left (fun acc l -> acc + String.length l + 1) 0 doc_lines in
    Printf.printf "  Size: %.2f MB (%d lines)\n" 
      (float_of_int doc_size /. 1024.0 /. 1024.0) lines;
    
    (* Create document and measure initial lex *)
    let start = Unix.gettimeofday () in
    let doc = create_document doc_lines in
    let initial_time = Unix.gettimeofday () -. start in
    Printf.printf "  Initial lexing: %.2f ms (%.2f MB/s)\n" 
      (initial_time *. 1000.0)
      (float_of_int doc_size /. 1024.0 /. 1024.0 /. initial_time);
    
    (* Test edit patterns *)
    let patterns = [
      ("Single character edit", SingleChar (lines / 2, "% Modified"));
      ("Multiple small edits", MultiLine [
        (lines / 4, "% Edit 1");
        (lines / 2, "% Edit 2"); 
        (3 * lines / 4, "% Edit 3")
      ]);
      ("Insert section", InsertSection (lines / 3, "New Section"));
      ("Modify preamble", ModifyPreamble "\\newcommand{\\test}{TEST}");
    ] in
    
    Printf.printf "\nEdit performance:\n";
    List.iter (fun (name, pattern) ->
      let lines_proc, bytes_proc, time_us = apply_edit_pattern doc pattern in
      let time_ms = float_of_int time_us /. 1000.0 in
      let speedup = initial_time *. 1000.0 /. time_ms in
      
      Printf.printf "  %s:\n" name;
      Printf.printf "    Time: %.2f ms\n" time_ms;
      Printf.printf "    Lines processed: %d (%.1f%%)\n" 
        lines_proc (float_of_int lines_proc /. float_of_int lines *. 100.0);
      Printf.printf "    Speedup: %.0fx\n" speedup;
    ) patterns;
    
    (* Overall statistics *)
    Printf.printf "\nOverall statistics:\n";
    Printf.printf "  Total lines lexed: %d\n" doc.stats.lines_lexed;
    Printf.printf "  Lines reused: %d\n" doc.stats.lines_reused;
    Printf.printf "  Convergence saves: %d\n" doc.stats.convergence_saves;
    Printf.printf "  Cache efficiency: %.1f%%\n"
      (float_of_int doc.stats.lines_reused /. 
       float_of_int (doc.stats.lines_lexed + doc.stats.lines_reused) *. 100.0);
    
    let avg_speedup = calculate_speedup doc in
    Printf.printf "  Average speedup: %.0fx\n" avg_speedup;
    
    if avg_speedup >= 1596.0 then
      Printf.printf "  ✓ TARGET ACHIEVED: 1,596x speedup!\n"
    else
      Printf.printf "  ✗ Below target: %.0fx / 1,596x = %.1f%%\n"
        avg_speedup (avg_speedup /. 1596.0 *. 100.0);
    
    Printf.printf "\n";
  ) configs

let () =
  Random.self_init ();
  run_benchmark ()