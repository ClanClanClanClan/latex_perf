let test_full_tokenization () =
  print_endline "=== FULL TOKENIZATION TRACE ===";
  
  let input = "\\[E = mc^2\\]" in
  Printf.printf "Input: '%s'\n" input;
  Printf.printf "Length: %d\n" (String.length input);
  
  let len = String.length input in
  let pos = ref 0 in
  let token_count = ref 0 in
  
  (* Simulate catcode table *)
  let catcode_table = Bytes.create 256 in
  Bytes.fill catcode_table 0 256 (Char.chr 12); (* other by default *)
  Bytes.set_uint8 catcode_table 92 0;    (* backslash = escape *)
  for i = 97 to 122 do Bytes.set_uint8 catcode_table i 11 done;  (* a-z = letter *)
  for i = 65 to 90 do Bytes.set_uint8 catcode_table i 11 done;   (* A-Z = letter *)
  Bytes.set_uint8 catcode_table 32 10;   (* space *)
  Bytes.set_uint8 catcode_table 61 12;   (* = other *)
  Bytes.set_uint8 catcode_table 94 7;    (* ^ superscript *)
  
  let is_letter_ultra_fast c =
    let code = Char.code c in
    (code >= 65 && code <= 90) || (code >= 97 && code <= 122) in
  
  print_endline "\n--- Character-by-character trace ---";
  
  while !pos < len do
    let c = String.unsafe_get input !pos in
    let code = Char.code c in
    let catcode = Bytes.get_uint8 catcode_table code in
    
    Printf.printf "\n[TOKEN %d] pos=%d: char='%c' code=%d catcode=%d\n" !token_count !pos c code catcode;
    
    match catcode with
    | 0 -> begin (* ESCAPE *)
        Printf.printf "  ESCAPE detected, incrementing pos\n";
        incr pos;
        if !pos < len then (
          let macro_start = !pos in
          Printf.printf "  macro_start=%d (points to '%c')\n" macro_start (String.unsafe_get input macro_start);
          
          Printf.printf "  Starting letter scan loop...\n";
          while !pos < len && is_letter_ultra_fast (String.unsafe_get input !pos) do
            Printf.printf "    Loop: pos=%d, char='%c' is letter\n" !pos (String.unsafe_get input !pos);
            incr pos
          done;
          
          let macro_len = !pos - macro_start in
          Printf.printf "  After loop: pos=%d, macro_len=%d\n" !pos macro_len;
          
          if macro_len > 0 then (
            Printf.printf "  MULTI-CHAR MACRO path: start=%d len=%d\n" macro_start macro_len;
            let macro_name = String.sub input macro_start macro_len in
            Printf.printf "  Multi-char macro: '%s'\n" macro_name;
            Printf.printf "  ❌ This would create TMacro(\"%s\")\n" macro_name
          ) else if !pos < len then (
            Printf.printf "  SINGLE-CHAR MACRO path\n";
            let sc = String.unsafe_get input !pos in
            Printf.printf "  Single char: '%c'\n" sc;
            Printf.printf "  ✅ This would create TMacro(\"%c\")\n" sc;
            Printf.printf "  Incrementing pos from %d to %d\n" !pos (!pos + 1);
            incr pos
          ) else (
            Printf.printf "  No more characters\n"
          )
        );
        incr token_count
      end
    | 11 -> begin (* LETTER *)
        Printf.printf "  LETTER: '%c'\n" c;
        incr pos;
        incr token_count
      end
    | _ -> begin (* OTHER *)
        Printf.printf "  OTHER: '%c' (catcode %d)\n" c catcode;
        incr pos;
        incr token_count
      end
  done;
  
  Printf.printf "\nFinal: pos=%d, tokens=%d\n" !pos !token_count;
  print_endline "\n=== TRACE COMPLETE ==="

let () = test_full_tokenization ()