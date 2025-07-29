let () = 
  let content = Benchmark.generate_latex_document ~lines:100 ~complexity:0.5 in
  let lines = String.split_on_char n content in
  Printf.printf "Line 25: %s
" (List.nth lines 24);
  Printf.printf "Line 50: %s
" (List.nth lines 49);
  Printf.printf "Line 75: %s
" (List.nth lines 74)
