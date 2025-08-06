(* test_v25_lazy.ml - Phase 3: Lazy materialization implementation *)

open Printf

(* Include arena implementation *)
module Arena = struct
  type t = {
    mutable arr: int64 array;
    mutable len: int;
    mutable capacity: int;
  }

  let create capacity =
    {
      arr = Array.make capacity 0L;
      len = 0;
      capacity;
    }

  let[@inline] push arena value =
    if arena.len >= arena.capacity then
      failwith "Arena overflow - increase capacity";
    Array.unsafe_set arena.arr arena.len value;
    arena.len <- arena.len + 1

  let length arena = arena.len

  let[@inline] get_raw arena index =
    if index >= arena.len then failwith "Arena index out of bounds";
    Array.unsafe_get arena.arr index
end

(* Token packing utilities *)
module TokenPacking = struct
  let[@inline] pack_char uchar_code catcode_val =
    let base = Int64.of_int uchar_code in
    let catcode_bits = Int64.shift_left (Int64.of_int catcode_val) 24 in
    Int64.logor base catcode_bits (* token_tag = 0 for TChar *)

  let[@inline] pack_macro name_hash =
    let base = Int64.of_int (name_hash land 0xFFFFFF) in
    let token_tag = Int64.shift_left 1L 28 in (* TMacro = 1 *)
    Int64.logor base token_tag

  let[@inline] pack_param param_num =
    let base = Int64.of_int param_num in
    let token_tag = Int64.shift_left 2L 28 in (* TParam = 2 *)
    Int64.logor base token_tag

  let[@inline] pack_group_open () =
    Int64.shift_left 3L 28 (* TGroupOpen = 3 *)

  let[@inline] pack_group_close () =
    Int64.shift_left 4L 28 (* TGroupClose = 4 *)

  let[@inline] pack_eof () =
    Int64.shift_left 5L 28 (* TEOF = 5 *)

  let[@inline] get_token_tag packed =
    Int64.to_int (Int64.shift_right (Int64.logand packed 0x70000000L) 28)
end

(* String interning for macro names *)
module StringTable = struct
  type t = {
    mutable table: (string, int) Hashtbl.t;
    mutable names: string array;
    mutable count: int;
  }

  let create capacity = {
    table = Hashtbl.create capacity;
    names = Array.make capacity "";
    count = 0;
  }

  let[@inline] intern st name =
    try
      Hashtbl.find st.table name
    with Not_found ->
      let id = st.count in
      if id >= Array.length st.names then failwith "StringTable overflow";
      Hashtbl.add st.table name id;
      Array.unsafe_set st.names id name;
      st.count <- st.count + 1;
      id

  let[@inline] lookup st id =
    Array.unsafe_get st.names id
end

(* Catcode definitions *)
module Catcode = struct
  type catcode =
    | Escape      (* 0: \ *)
    | BeginGroup  (* 1: { *)
    | EndGroup    (* 2: } *)
    | MathShift   (* 3: $ *)
    | AlignTab    (* 4: & *)
    | Endline     (* 5: newline *)
    | Param       (* 6: # *)
    | Superscript (* 7: ^ *)
    | Subscript   (* 8: _ *)
    | Ignored     (* 9: null *)
    | Space       (* 10: space, tab *)
    | Letter      (* 11: A-Z, a-z *)
    | Other       (* 12: everything else *)
    | Active      (* 13: ~ *)
    | Comment     (* 14: % *)
    | Invalid     (* 15: invalid *)
    
  let catcode_to_int = function
    | Escape -> 0 | BeginGroup -> 1 | EndGroup -> 2 | MathShift -> 3
    | AlignTab -> 4 | Endline -> 5 | Param -> 6 | Superscript -> 7
    | Subscript -> 8 | Ignored -> 9 | Space -> 10 | Letter -> 11
    | Other -> 12 | Active -> 13 | Comment -> 14 | Invalid -> 15
    
  let catcode_of _context uc =
    let code = Uchar.to_int uc in
    match code with
    | 0 -> Ignored
    | 9 | 32 -> Space  (* tab, space *)
    | 10 | 13 -> Endline  (* \n, \r *)
    | 35 -> Param  (* # *)
    | 36 -> MathShift  (* $ *)
    | 37 -> Comment  (* % *)
    | 38 -> AlignTab  (* & *)
    | 92 -> Escape  (* \ *)
    | 94 -> Superscript  (* ^ *)
    | 95 -> Subscript  (* _ *)
    | 123 -> BeginGroup  (* { *)
    | 125 -> EndGroup  (* } *)
    | 126 -> Active  (* ~ *)
    | c when (c >= 65 && c <= 90) || (c >= 97 && c <= 122) -> Letter
    | _ -> Other
end

(* ===== PHASE 3: LAZY MATERIALIZATION ===== *)

module Lexer_v25 = struct
  type token =
    | TChar of Uchar.t * int  (* catcode as int for now *)
    | TMacro of string
    | TParam of int
    | TGroupOpen
    | TGroupClose
    | TEOF
    
  type location = {
    line: int;
    column: int; 
    byte_start: int;
    byte_end: int;
  }

  type located_token = {
    token: token;
    loc: location;
  }

  (* LAZY ITERATOR - Phase 3 Core Innovation *)
  type lazy_lexer = {
    arena: Arena.t;
    strings: StringTable.t;
    mutable position: int;
  }

  let[@inline] materialize_token_at lazy_lex index =
    let packed_value = Arena.get_raw lazy_lex.arena index in
    let tag = TokenPacking.get_token_tag packed_value in
    match tag with
    | 0 -> (* TChar *)
        let uchar_code = Int64.to_int (Int64.logand packed_value 0xFFFFFFL) in
        let catcode = Int64.to_int (Int64.shift_right (Int64.logand packed_value 0xF000000L) 24) in
        TChar (Uchar.of_int uchar_code, catcode)
    | 1 -> (* TMacro *)
        let name_id = Int64.to_int (Int64.logand packed_value 0xFFFFFFL) in
        let name = StringTable.lookup lazy_lex.strings name_id in
        TMacro name
    | 2 -> (* TParam *)
        let param_num = Int64.to_int (Int64.logand packed_value 0xFFFFFFL) in
        TParam param_num
    | 3 -> TGroupOpen
    | 4 -> TGroupClose
    | 5 -> TEOF
    | _ -> failwith "Invalid token tag"

  let[@inline] has_more lazy_lex =
    lazy_lex.position < Arena.length lazy_lex.arena

  let[@inline] next_token lazy_lex =
    if not (has_more lazy_lex) then None
    else begin
      let token = materialize_token_at lazy_lex lazy_lex.position in
      let loc = { line = 0; column = 0; byte_start = lazy_lex.position; byte_end = lazy_lex.position } in
      lazy_lex.position <- lazy_lex.position + 1;
      Some { token; loc }
    end

  let[@inline] peek_token lazy_lex =
    if not (has_more lazy_lex) then None
    else begin
      let token = materialize_token_at lazy_lex lazy_lex.position in
      let loc = { line = 0; column = 0; byte_start = lazy_lex.position; byte_end = lazy_lex.position } in
      Some { token; loc }
    end

  let create_lazy_lexer arena strings = {
    arena;
    strings;
    position = 0;
  }
end

(* Arena-based lexer - Phase 3 optimized *)
module V25_lexer_lazy = struct
  let tokenize content =
    let len = String.length content in
    let bytes = Bytes.unsafe_of_string content in
    
    (* Pre-allocate arena with estimated capacity *)
    let estimated_tokens = len + (len / 10) in
    let arena = Arena.create estimated_tokens in
    let strings = StringTable.create 10000 in
    
    (* Pre-computed catcode table *)
    let ascii_catcodes = Array.make 128 12 in (* Default: Other = 12 *)
    let () =
      ascii_catcodes.(0) <- 9;   (* null -> Ignored *)
      ascii_catcodes.(9) <- 10;  (* tab -> Space *)
      ascii_catcodes.(32) <- 10; (* space -> Space *)
      ascii_catcodes.(10) <- 5;  (* \n -> Endline *)
      ascii_catcodes.(13) <- 5;  (* \r -> Endline *)
      ascii_catcodes.(35) <- 6;  (* # -> Param *)
      ascii_catcodes.(36) <- 3;  (* $ -> MathShift *)
      ascii_catcodes.(37) <- 14; (* % -> Comment *)
      ascii_catcodes.(38) <- 4;  (* & -> AlignTab *)
      ascii_catcodes.(92) <- 0;  (* \ -> Escape *)
      ascii_catcodes.(94) <- 7;  (* ^ -> Superscript *)
      ascii_catcodes.(95) <- 8;  (* _ -> Subscript *)
      ascii_catcodes.(123) <- 1; (* { -> BeginGroup *)
      ascii_catcodes.(125) <- 2; (* } -> EndGroup *)
      ascii_catcodes.(126) <- 13; (* ~ -> Active *)
      for i = 65 to 90 do ascii_catcodes.(i) <- 11 done;   (* A-Z -> Letter *)
      for i = 97 to 122 do ascii_catcodes.(i) <- 11 done   (* a-z -> Letter *)
    in
    
    let[@inline] get_catcode_fast c =
      let code = Char.code c in
      if code < 128 then
        Array.unsafe_get ascii_catcodes code
      else 12 (* Other *)
    in
    
    let[@inline] push_char_token uchar_code catcode_val =
      let packed = TokenPacking.pack_char uchar_code catcode_val in
      Arena.push arena packed
    in
    
    let[@inline] push_macro_token name =
      let name_id = StringTable.intern strings name in
      let packed = TokenPacking.pack_macro name_id in
      Arena.push arena packed
    in
    
    let[@inline] push_param_token param_num =
      let packed = TokenPacking.pack_param param_num in
      Arena.push arena packed
    in
    
    let[@inline] push_group_open () =
      Arena.push arena (TokenPacking.pack_group_open ())
    in
    
    let[@inline] push_group_close () =
      Arena.push arena (TokenPacking.pack_group_close ())
    in
    
    (* Main tokenization loop *)
    let pos = ref 0 in
    
    let read_control_sequence () =
      let start = !pos in
      incr pos; (* skip \ *)
      
      if !pos >= len then "" else
      
      let c = Bytes.unsafe_get bytes !pos in
      let cc = get_catcode_fast c in
      if cc = 11 then begin (* Letter *)
        incr pos;
        while !pos < len && 
              get_catcode_fast (Bytes.unsafe_get bytes !pos) = 11 do
          incr pos
        done;
        (* Skip spaces *)
        while !pos < len && 
              get_catcode_fast (Bytes.unsafe_get bytes !pos) = 10 do
          incr pos
        done;
        let name_len = !pos - start - 1 in
        if name_len > 0 then
          Bytes.sub_string bytes (start + 1) name_len
        else ""
      end else begin
        incr pos;
        String.make 1 c
      end
    in
    
    while !pos < len do
      let c = Bytes.unsafe_get bytes !pos in
      let cc = get_catcode_fast c in
      
      match cc with
      | 0 -> (* Escape *)
          let name = read_control_sequence () in
          push_macro_token name
      
      | 14 -> (* Comment *)
          while !pos < len && Bytes.unsafe_get bytes !pos <> '\n' do
            incr pos
          done
      
      | 1 -> (* BeginGroup *)
          incr pos;
          push_group_open ()
      
      | 2 -> (* EndGroup *)
          incr pos;
          push_group_close ()
      
      | 6 -> (* Param *)
          incr pos;
          if !pos < len then
            let c2 = Bytes.unsafe_get bytes !pos in
            if c2 >= '1' && c2 <= '9' then begin
              incr pos;
              push_param_token (Char.code c2 - Char.code '0')
            end else
              push_char_token (Char.code c) cc
          else
            push_char_token (Char.code c) cc
      
      | 10 -> (* Space *)
          while !pos < len && 
                get_catcode_fast (Bytes.unsafe_get bytes !pos) = 10 do
            incr pos
          done;
          push_char_token 32 10 (* single space char *)
      
      | 5 -> (* Endline *)
          incr pos;
          if !pos < len && Bytes.unsafe_get bytes !pos = '\n' then begin
            incr pos;
            push_macro_token "par"
          end else
            push_char_token 32 10 (* newline becomes space *)
      
      | _ ->
          push_char_token (Char.code c) cc;
          incr pos
    done;
    
    Arena.push arena (TokenPacking.pack_eof ());
    Lexer_v25.create_lazy_lexer arena strings

end

(* Eager materialization for comparison *)
let force_all_tokens lazy_lex =
  let tokens = ref [] in
  while Lexer_v25.has_more lazy_lex do
    match Lexer_v25.next_token lazy_lex with
    | Some token -> tokens := token :: !tokens
    | None -> ()
  done;
  List.rev !tokens

(* ===== MAIN TEST ===== *)
let () =
  printf "🔄 LAZY MATERIALIZATION V25 TEST (PHASE 3)\n";
  printf "==========================================\n";
  
  let content = 
    try
      let ic = open_in "corpora/perf/perf_smoke_big.tex" in
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      printf "✅ Loaded corpus: %d bytes\n" n;
      s
    with _ ->
      printf "❌ Using synthetic test\n";
      String.concat "\n" [
        "% Test document";
        "\\documentclass[12pt]{article}";
        "\\begin{document}";
        "Hello world! This is a test.";
        "$x^2 + y^2 = z^2$";
        "\\end{document}"
      ]
  in
  
  (* Phase 3 Lazy test *)
  printf "\n--- LAZY LEXER (PHASE 3) ---\n";
  for _ = 1 to 3 do
    let lazy_lex = V25_lexer_lazy.tokenize content in
    let _ = force_all_tokens lazy_lex in
    Gc.full_major ()
  done;
  
  let lazy_times = ref [] in
  let lazy_count = ref 0 in
  
  for i = 1 to 15 do
    Gc.full_major ();
    let start = Sys.time () in
    let lazy_lex = V25_lexer_lazy.tokenize content in
    let tokens = force_all_tokens lazy_lex in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    lazy_times := elapsed :: !lazy_times;
    if i = 1 then lazy_count := List.length tokens
  done;
  
  let lazy_sorted = List.sort compare !lazy_times in
  let lazy_median = List.nth lazy_sorted 7 in
  printf "Tokens: %d\n" !lazy_count;
  printf "Median: %.2f ms\n" lazy_median;
  
  (* Compare with Phase 2 arena baseline *)
  printf "\n--- COMPARISON ---\n";
  printf "Lazy vs Expected 944K: %s (%d tokens)\n"
    (if abs (!lazy_count - 944614) < 1000 then "✅ CLOSE" else "❌ DIFFERENT") !lazy_count;
  
  printf "\nPhase 3 Targets:\n";
  printf "≤30ms (Phase 3): %s (%.2fms)\n"
    (if lazy_median <= 30.0 then "✅ PASS" else "❌ FAIL") lazy_median;
  printf "≤20ms (Final): %s (%.2fms)\n"
    (if lazy_median <= 20.0 then "✅ PASS" else "❌ FAIL") lazy_median;
  
  printf "\n🔄 LAZY PHASE 3 COMPLETE\n"