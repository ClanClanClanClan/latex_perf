(* Debug Ultra V3 Correctness Issues *)

let debug_tokenization input =
  Printf.printf "=== DEBUGGING TOKENIZATION: %s ===\n" input;
  
  Printf.printf "\n🔍 ORIGINAL ARENA TOKENIZATION:\n";
  let orig_tokens = L0_lexer_track_a_arena.tokenize input in
  Array.iteri (fun i token ->
    let catcode = L0_lexer_track_a_arena.TokenPacking.unpack_catcode token in
    let data = L0_lexer_track_a_arena.TokenPacking.unpack_data token in
    Printf.printf "  [%d] catcode=%d data=%d (0x%08lx)\n" i catcode data token
  ) orig_tokens;
  
  Printf.printf "\n🚀 ULTRA V3 TOKENIZATION:\n";  
  let ultra_tokens = L0_lexer_track_a_ultra_v3.tokenize input in
  Array.iteri (fun i token ->
    let catcode = L0_lexer_track_a_ultra_v3.TokenPacking.unpack_catcode token in
    let data = L0_lexer_track_a_ultra_v3.TokenPacking.unpack_data token in
    Printf.printf "  [%d] catcode=%d data=%d (0x%08lx)\n" i catcode data token
  ) ultra_tokens;
  
  Printf.printf "\n📊 COMPARISON:\n";
  Printf.printf "  Original: %d tokens\n" (Array.length orig_tokens);
  Printf.printf "  Ultra V3: %d tokens\n" (Array.length ultra_tokens);
  
  Printf.printf "\n🔍 TOKEN-BY-TOKEN ANALYSIS:\n";
  let max_len = max (Array.length orig_tokens) (Array.length ultra_tokens) in
  for i = 0 to max_len - 1 do
    let orig_str = if i < Array.length orig_tokens then
      L0_lexer_track_a_arena.PackedToken.to_string orig_tokens.(i)
    else "MISSING" in
    let ultra_str = if i < Array.length ultra_tokens then
      L0_lexer_track_a_ultra_v3.PackedToken.to_string ultra_tokens.(i)
    else "MISSING" in
    
    if orig_str = ultra_str then
      Printf.printf "  [%d] ✅ %s\n" i orig_str
    else
      Printf.printf "  [%d] ❌ ORIG: %s | ULTRA: %s\n" i orig_str ultra_str
  done

let () =
  print_endline "=== ULTRA V3 CORRECTNESS DEBUG ===\n";
  
  (* Test simple input *)
  debug_tokenization "hello";
  print_endline "";
  
  (* Test macro input *)
  debug_tokenization "\\textbf";
  print_endline "";
  
  (* Test single-char macro *)
  debug_tokenization "\\[";
  print_endline "";
  
  (* Test complex input *)
  debug_tokenization "\\[E = mc^2\\]";
  print_endline "";
  
  (* Test the failing case *)
  debug_tokenization "\\[E = mc^2\\] and \\textbf{bold}";
  
  print_endline "\n=== DEBUG COMPLETE ==="