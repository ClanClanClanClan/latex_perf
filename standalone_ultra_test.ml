(* Standalone test for Ultra V3 Fixed - simplified without dependencies *)

(* Token packing utilities *)
module TokenPacking = struct
  let[@inline] pack_token catcode data =
    Int32.logor 
      (Int32.shift_left (Int32.of_int data) 6)
      (Int32.of_int catcode)
  
  let[@inline] unpack_catcode packed =
    Int32.to_int (Int32.logand packed 0x3Fl)
  
  let[@inline] unpack_data packed =
    Int32.to_int (Int32.shift_right_logical packed 6)
  
  let cc_escape = 0
  let cc_letter = 11
  let cc_other = 12
  let cc_space = 10
end

(* Simplified string operations *)
module SimpleStringOps = struct
  let single_char_macros = Hashtbl.create 256
  let () = 
    Hashtbl.add single_char_macros '[' 0;
    Hashtbl.add single_char_macros ']' 1

  let get_macro_name id =
    match id with
    | 0 -> "["
    | 1 -> "]"
    | _ -> "unknown"
end

(* Simplified arena *)
module SimpleArena = struct
  type t = { mutable tokens: int32 list }
  
  let create _ = { tokens = [] }
  
  let emit_packed_token arena packed =
    arena.tokens <- packed :: arena.tokens
  
  let get_tokens arena =
    Array.of_list (List.rev arena.tokens)
end

(* CORRECTED tokenization logic *)
let simple_tokenize input =
  let len = String.length input in
  let arena = SimpleArena.create 100 in
  let pos = ref 0 in
  
  (* Simple catcode lookup *)
  let get_catcode c = 
    match c with
    | '\\' -> 0  (* escape *)
    | 'a'..'z' | 'A'..'Z' -> 11  (* letter *)
    | ' ' | '\t' -> 10  (* space *)
    | _ -> 12  (* other *)
  in
  
  let is_letter c = 
    let code = Char.code c in
    (code >= 65 && code <= 90) || (code >= 97 && code <= 122) in
  
  while !pos < len do
    let c = input.[!pos] in
    let catcode = get_catcode c in
    
    match catcode with
    | 0 -> (* ESCAPE *)
        Printf.printf "ESCAPE at pos %d\n" !pos;
        incr pos;
        if !pos < len then (
          let macro_start = !pos in
          Printf.printf "macro_start = %d (char '%c')\n" macro_start input.[macro_start];
          
          (* Letter scanning loop *)
          while !pos < len && is_letter input.[!pos] do
            Printf.printf "  Letter scan: pos %d char '%c'\n" !pos input.[!pos];
            incr pos
          done;
          
          let macro_len = !pos - macro_start in
          Printf.printf "macro_len = %d\n" macro_len;
          
          if macro_len > 0 then (
            (* Multi-char macro *)
            let name = String.sub input macro_start macro_len in
            Printf.printf "Multi-char macro: '%s'\n" name;
            let packed = TokenPacking.pack_token TokenPacking.cc_escape 99 in
            SimpleArena.emit_packed_token arena packed
          ) else if !pos < len then (
            (* Single-char macro *)
            let sc = input.[!pos] in
            Printf.printf "Single-char macro: '%c'\n" sc;
            let macro_id = match sc with
              | '[' -> 0 
              | ']' -> 1 
              | _ -> 99 in
            let packed = TokenPacking.pack_token TokenPacking.cc_escape macro_id in
            SimpleArena.emit_packed_token arena packed;
            incr pos;
            Printf.printf "After single-char: pos = %d\n" !pos
          )
        )
    | 11 -> (* LETTER *)
        Printf.printf "LETTER '%c' at pos %d\n" c !pos;
        let packed = TokenPacking.pack_token catcode (Char.code c) in
        SimpleArena.emit_packed_token arena packed;
        incr pos
    | _ -> (* OTHER *)
        Printf.printf "OTHER '%c' at pos %d\n" c !pos;
        let packed = TokenPacking.pack_token catcode (Char.code c) in
        SimpleArena.emit_packed_token arena packed;
        incr pos
  done;
  
  SimpleArena.get_tokens arena

let test_input input =
  Printf.printf "\n=== Testing: '%s' ===\n" input;
  let tokens = simple_tokenize input in
  Printf.printf "Result: %d tokens\n" (Array.length tokens);
  
  Array.iteri (fun i token ->
    let catcode = TokenPacking.unpack_catcode token in
    let data = TokenPacking.unpack_data token in
    
    let token_str = match catcode with
      | 0 -> Printf.sprintf "TMacro(\"%s\")" (SimpleStringOps.get_macro_name data)
      | 11 -> Printf.sprintf "TChar('%c')" (Char.chr data)
      | _ -> Printf.sprintf "Other('%c')" (Char.chr data)
    in
    
    Printf.printf "  [%d] %s\n" i token_str
  ) tokens

let () =
  print_endline "=== STANDALONE ULTRA TEST ===";
  test_input "\\[";
  test_input "\\[E";
  test_input "\\[E = mc^2\\]";
  print_endline "\n=== TEST COMPLETE ==="