let () = 
  Printf.printf "=== Simple Test ===
";
  let lexer = Incremental_lexer_optimized.create_optimized () in
  let simple_doc = "\section{Test}
Hello \textbf{world}\!
\end{document}" in
  Printf.printf "Loading: %s
" simple_doc;
  Incremental_lexer_optimized.load_string lexer simple_doc;
  Printf.printf "Document loaded successfully
";
  let result = Incremental_lexer_optimized.edit_line lexer 1 "Hello \emph{world}\!" in
  Printf.printf "Edit result: %d lines, %d bytes, %.2f ms
" (let (a,b,c) = result in a) (let (a,b,c) = result in b) (let (a,b,c) = result in c);
  let speedup = Incremental_lexer_optimized.calculate_achieved_speedup lexer in
  Printf.printf "Achieved speedup: %.1fx
" speedup
