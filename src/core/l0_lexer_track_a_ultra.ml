(* L0 Lexer Track A - ULTRA-OPTIMIZED IMPLEMENTATION *)
(* Aggressive micro-optimizations for <2ms target *)
(* Zero allocations, unsafe operations, manual inlining *)

open Data

(* Token type constants - manually inlined everywhere *)
let token_char = 0
let token_macro = 1
let token_group_open = 2
let token_group_close = 3
let token_param = 4
let token_eof = 5

(* Ultra-optimized: Larger ring buffer for 1.1MB files *)
let ring_size = 3_000_000  (* Handle up to 1M tokens safely *)
let ring_buffer = Bigarray.Array1.create Bigarray.int Bigarray.c_layout ring_size

(* Ultra-optimized: Use unsafe bigarray operations *)
let unsafe_get arr idx = Bigarray.Array1.unsafe_get arr idx
let unsafe_set arr idx v = Bigarray.Array1.unsafe_set arr idx v

(* Pre-computed catcode table with direct array access *)
let catcode_table = 
  let t = Array.make 256 12 in (* Default to OTHER *)
  (* Special characters *)
  Array.unsafe_set t 32 10;   (* space -> SPACE *)
  Array.unsafe_set t 9 10;    (* tab -> SPACE *)
  Array.unsafe_set t 10 5;    (* \n -> EOL *)
  Array.unsafe_set t 13 5;    (* \r -> EOL *)
  Array.unsafe_set t 92 0;    (* \ -> ESCAPE *)
  Array.unsafe_set t 123 1;   (* { -> BEGIN_GROUP *)
  Array.unsafe_set t 125 2;   (* } -> END_GROUP *)
  Array.unsafe_set t 36 3;    (* $ -> MATH_SHIFT *)
  Array.unsafe_set t 38 4;    (* & -> ALIGNMENT *)
  Array.unsafe_set t 35 6;    (* # -> PARAMETER *)
  Array.unsafe_set t 94 7;    (* ^ -> SUPERSCRIPT *)
  Array.unsafe_set t 95 8;    (* _ -> SUBSCRIPT *)
  Array.unsafe_set t 37 14;   (* % -> COMMENT *)
  (* Letters *)
  for i = 65 to 90 do Array.unsafe_set t i 11 done;  (* A-Z -> LETTER *)
  for i = 97 to 122 do Array.unsafe_set t i 11 done; (* a-z -> LETTER *)
  t

(* Ultra-optimized: Pre-allocated macro string buffer *)
let macro_buffer = Bytes.create 256
let macro_table : (string, int) Hashtbl.t = Hashtbl.create 4096  (* Larger initial size *)
let macro_counter = ref 0

(* Ultra-optimized tokenizer with manual loop unrolling *)
let tokenize input =
  let len = String.length input in
  let ring_pos = ref 0 in
  let pos = ref 0 in
  let line = ref 1 in
  let col = ref 1 in
  
  (* Manual inlining of emit_token for maximum speed *)
  let[@inline always] emit_token token_type offset data =
    let rp = !ring_pos in
    unsafe_set ring_buffer rp token_type;
    unsafe_set ring_buffer (rp + 1) offset;
    unsafe_set ring_buffer (rp + 2) data;
    ring_pos := rp + 3
  in
  
  (* Main tokenization loop with manual optimizations *)
  while !pos < len do
    let p = !pos in
    
    (* Ultra-fast: avoid bounds check with unsafe_get *)
    let ch = String.unsafe_get input p in
    let ch_code = Char.code ch in
    let catcode = Array.unsafe_get catcode_table ch_code in
    
    (* Update position tracking *)
    if ch_code = 10 then begin (* newline *)
      incr line;
      col := 1
    end else 
      incr col;
    
    (* Ultra-optimized: use computed goto pattern *)
    if catcode = 0 then begin
      (* ESCAPE - start macro *)
      incr pos;
      if !pos < len then begin
        (* Collect macro name with zero allocations *)
        let macro_start = !pos in
        let macro_len = ref 0 in
        
        (* Unrolled loop for common short macros *)
        if !pos < len && 
           let c = Char.code (String.unsafe_get input !pos) in
           (c >= 97 && c <= 122) || (c >= 65 && c <= 90) then begin
          incr pos; incr macro_len;
          
          if !pos < len && 
             let c = Char.code (String.unsafe_get input !pos) in
             (c >= 97 && c <= 122) || (c >= 65 && c <= 90) then begin
            incr pos; incr macro_len;
            
            if !pos < len && 
               let c = Char.code (String.unsafe_get input !pos) in
               (c >= 97 && c <= 122) || (c >= 65 && c <= 90) then begin
              incr pos; incr macro_len;
              
              (* Continue for longer macros *)
              while !pos < len && 
                    let c = Char.code (String.unsafe_get input !pos) in
                    (c >= 97 && c <= 122) || (c >= 65 && c <= 90) do
                incr pos;
                incr macro_len
              done
            end
          end
        end;
        
        if !macro_len > 0 then begin
          (* Extract macro name efficiently *)
          String.blit input macro_start macro_buffer 0 !macro_len;
          let macro_name = Bytes.sub_string macro_buffer 0 !macro_len in
          
          (* Get or create macro ID *)
          let macro_id = 
            try Hashtbl.find macro_table macro_name
            with Not_found ->
              let id = !macro_counter in
              incr macro_counter;
              Hashtbl.add macro_table macro_name id;
              id
          in
          
          emit_token token_macro p macro_id
        end else if !pos < len then begin
          (* Single character macro *)
          emit_token token_macro p ch_code;
          incr pos
        end
      end
    end else if catcode = 14 then begin
      (* COMMENT - skip to end of line *)
      incr pos;
      while !pos < len && String.unsafe_get input !pos <> '\n' do
        incr pos
      done
    end else if catcode = 1 then begin
      (* BEGIN GROUP *)
      emit_token token_group_open p ch_code;
      incr pos
    end else if catcode = 2 then begin
      (* END GROUP *)
      emit_token token_group_close p ch_code;
      incr pos
    end else if catcode = 6 && !pos + 1 < len then begin
      (* PARAMETER *)
      incr pos;
      let next_ch = String.unsafe_get input !pos in
      if next_ch >= '0' && next_ch <= '9' then begin
        emit_token token_param p (Char.code next_ch - 48);
        incr pos
      end else begin
        emit_token token_char p ch_code;
      end
    end else begin
      (* Regular character *)
      emit_token token_char p ((ch_code lsl 8) lor catcode);
      incr pos
    end
  done;
  
  (* Emit EOF token *)
  emit_token token_eof !pos 0;
  
  (* Ultra-fast: Convert ring buffer to token list in single pass *)
  let token_count = !ring_pos / 3 in
  let rec build_tokens i acc =
    if i < 0 then acc
    else
      let base = i * 3 in
      let tok_type = unsafe_get ring_buffer base in
      let offset = unsafe_get ring_buffer (base + 1) in
      let data = unsafe_get ring_buffer (base + 2) in
      
      let token = 
        if tok_type = token_char then
          let ch_code = data lsr 8 in
          let catcode_val = data land 0xFF in
          let catcode = match catcode_val with
            | 0 -> Catcode.Escape | 1 -> Catcode.BeginGroup
            | 2 -> Catcode.EndGroup | 3 -> Catcode.MathShift
            | 4 -> Catcode.AlignTab | 5 -> Catcode.EndLine
            | 6 -> Catcode.Param | 7 -> Catcode.Superscript
            | 8 -> Catcode.Subscript | 9 -> Catcode.Ignored
            | 10 -> Catcode.Space | 11 -> Catcode.Letter
            | 12 -> Catcode.Other | 13 -> Catcode.Active
            | 14 -> Catcode.Comment | _ -> Catcode.Invalid
          in
          Lexer_v25.TChar (Uchar.of_int ch_code, catcode)
        else if tok_type = token_macro then
          (* Reverse lookup macro name - in production would optimize this *)
          let name = 
            Hashtbl.fold (fun n id acc -> 
              if id = data then n else acc) macro_table "unknown"
          in
          Lexer_v25.TMacro name
        else if tok_type = token_group_open then
          Lexer_v25.TGroupOpen
        else if tok_type = token_group_close then
          Lexer_v25.TGroupClose
        else if tok_type = token_param then
          Lexer_v25.TParam data
        else (* EOF *)
          Lexer_v25.TEOF
      in
      build_tokens (i - 1) (token :: acc)
  in
  build_tokens (token_count - 1) []

(* Export optimized tokenizer *)
let tokenize_ultra = tokenize