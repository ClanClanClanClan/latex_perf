(* Minimal L0 test - just check if it works *)

let () =
  print_endline "=== MINIMAL L0 TEST ===";
  
  (* Test 1: Simple string *)
  print_string "Test 1 - Simple text: ";
  (try
    let tokens = L0_lexer_track_a_arena.tokenize "hello" in
    Printf.printf "✅ %d tokens\n" (List.length tokens)
  with e ->
    Printf.printf "❌ %s\n" (Printexc.to_string e));
    
  (* Test 2: Display math *)  
  print_string "Test 2 - Display math \\[x\\]: ";
  (try
    let tokens = L0_lexer_track_a_arena.tokenize "\\[x\\]" in
    let macros = List.fold_left (fun acc tok ->
      match tok with
      | Lexer_v25.TMacro name -> name :: acc
      | _ -> acc
    ) [] tokens in
    if List.mem "[" macros && List.mem "]" macros then
      print_endline "✅ Display math macros found!"
    else
      Printf.printf "❌ Macros: [%s]\n" (String.concat ", " macros)
  with e ->
    Printf.printf "❌ %s\n" (Printexc.to_string e));
    
  (* Test 3: Performance on 100KB *)
  print_string "Test 3 - Performance (100KB): ";
  (try
    let doc = String.make 100_000 'a' in
    let start = Sys.time () in
    let _ = L0_lexer_track_a_arena.tokenize doc in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    Printf.printf "%.2f ms (extrapolated to 1.1MB: ~%.2f ms)\n" 
      elapsed (elapsed *. 11.0)
  with e ->
    Printf.printf "❌ %s\n" (Printexc.to_string e));
    
  print_endline "\n=== END TEST ==="