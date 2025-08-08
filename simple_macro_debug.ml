let test_single_macro () =
  print_endline "=== SIMPLE MACRO DEBUG ===";
  
  let input = "\\[" in
  Printf.printf "Input: %s\n" input;
  Printf.printf "Length: %d\n" (String.length input);
  
  Printf.printf "\n--- Tracing Manual Parse ---\n";
  let len = String.length input in
  let pos = ref 0 in
  
  (* Simulate Ultra V3 logic *)
  let c = String.unsafe_get input !pos in
  Printf.printf "pos=%d: char='%c' code=%d\n" !pos c (Char.code c);
  
  if Char.code c = 92 then ( (* backslash *)
    Printf.printf "Found backslash, incrementing pos\n";
    incr pos;
    
    if !pos < len then (
      let macro_start = !pos in
      Printf.printf "macro_start=%d (points to '%c')\n" macro_start (String.unsafe_get input macro_start);
      
      (* Check if it's a letter *)
      let char_at_start = String.unsafe_get input macro_start in
      let is_letter = 
        let code = Char.code char_at_start in
        (code >= 65 && code <= 90) || (code >= 97 && code <= 122) in
      Printf.printf "is_letter('%c') = %b\n" char_at_start is_letter;
      
      (* Simulate the while loop *)
      Printf.printf "Starting while loop...\n";
      let original_pos = !pos in
      while !pos < len && (
        let code = Char.code (String.unsafe_get input !pos) in
        (code >= 65 && code <= 90) || (code >= 97 && code <= 122)
      ) do
        Printf.printf "  Loop: pos=%d, char='%c'\n" !pos (String.unsafe_get input !pos);
        incr pos
      done;
      
      let macro_len = !pos - macro_start in
      Printf.printf "After loop: pos=%d, macro_len=%d\n" !pos macro_len;
      
      if macro_len > 0 then (
        Printf.printf "Multi-char macro path: start=%d len=%d\n" macro_start macro_len;
        let macro_name = String.sub input macro_start macro_len in
        Printf.printf "Macro name: '%s'\n" macro_name
      ) else if !pos < len then (
        Printf.printf "Single-char macro path\n";
        let sc = String.unsafe_get input !pos in
        Printf.printf "Single char: '%c'\n" sc;
        Printf.printf "Will increment pos from %d to %d\n" !pos (!pos + 1);
      ) else (
        Printf.printf "No more characters\n"
      )
    )
  );
  
  print_endline "=== DEBUG COMPLETE ==="

let () = test_single_macro ()