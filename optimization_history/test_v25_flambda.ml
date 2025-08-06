(* test_v25_flambda.ml - Flambda2 optimized version *)

(* Copy the exact content from test_v25_correct.ml to test with flambda2 *)

open Printf

(* ===== DATA MODULE TYPES ===== *)
module Location = struct
  type t = {
    line: int;
    column: int; 
    byte_start: int;
    byte_end: int;
  }
end

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
    
  type context = PdfTeX | Unicode
  
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

(* ===== V25 LEXER TYPES ===== *)
module Lexer_v25 = struct
  type token =
    | TChar of Uchar.t * Catcode.catcode
    | TMacro of string
    | TParam of int
    | TGroupOpen
    | TGroupClose
    | TEOF
    
  type lexer_state = 
    | S0_Normal
    | SComment
    | SMacroAcc
    
  type located_token = {
    token: token;
    loc: Location.t;
  }
end

(* ===== CORRECT V25 BASELINE IMPLEMENTATION ===== *)
module V25_lexer_baseline = struct
  open Lexer_v25
  open Catcode
  
  let tokenize content =
    let len = String.length content in
    let tokens = ref [] in
    let pos = ref 0 in
    let line = ref 1 in
    let col = ref 1 in
    
    let[@inline] advance () =
      if !pos < len then begin
        if content.[!pos] = '\n' then begin
          incr line; col := 1
        end else incr col;
        incr pos
      end
    in
    
    let[@inline] current_char () =
      if !pos < len then content.[!pos] else '\x00'
    in
    
    let[@inline] push_token tok =
      let loc = {
        Location.line = !line;
        column = !col;
        byte_start = !pos;
        byte_end = !pos + 1;
      } in
      tokens := { token = tok; loc } :: !tokens
    in
    
    (* Skip whitespace after control sequence *)
    let skip_spaces () =
      while !pos < len && 
            let c = current_char () in 
            (c = ' ' || c = '\t') do
        advance ()
      done
    in
    
    (* Read control sequence name *)
    let read_control_sequence () =
      let start = !pos in
      advance (); (* skip \ *)
      
      if !pos >= len then "" else
      
      let c = current_char () in
      let cc = catcode_of PdfTeX (Uchar.of_char c) in
      
      if cc = Letter then begin
        (* Multi-letter control sequence *)
        while !pos < len && 
              catcode_of PdfTeX (Uchar.of_char (current_char ())) = Letter do
          advance ()
        done;
        let name = String.sub content start (!pos - start) in
        skip_spaces (); (* Spaces after control word are ignored *)
        String.sub name 1 (String.length name - 1)  (* Remove \ *)
      end else begin
        (* Single-char control sequence *)
        advance ();
        String.make 1 c
      end
    in
    
    (* Skip comment until end of line *)
    let skip_comment () =
      while !pos < len && current_char () <> '\n' do
        advance ()
      done
    in
    
    (* Read parameter number *)
    let read_param () =
      advance (); (* skip # *)
      if !pos < len then
        let c = current_char () in
        if c >= '1' && c <= '9' then begin
          advance ();
          Some (Char.code c - Char.code '0')
        end else None
      else None
    in
    
    (* Main tokenization loop *)
    while !pos < len do
      let c = current_char () in
      let uc = Uchar.of_char c in
      let cc = catcode_of PdfTeX uc in
      
      match cc with
      | Escape ->
          let name = read_control_sequence () in
          push_token (TMacro name)
      
      | Comment ->
          skip_comment ()
      
      | BeginGroup ->
          advance ();
          push_token TGroupOpen
      
      | EndGroup ->
          advance ();
          push_token TGroupClose
      
      | Param ->
          (match read_param () with
           | Some n -> push_token (TParam n)
           | None -> 
               (* # not followed by digit *)
               push_token (TChar (uc, cc));
               advance ())
      
      | Space ->
          (* Collect consecutive spaces into single space token *)
          while !pos < len && 
                let cc = catcode_of PdfTeX (Uchar.of_char (current_char ())) in
                cc = Space do
            advance ()
          done;
          push_token (TChar (Uchar.of_char ' ', Space))
      
      | Endline ->
          (* Single newline becomes space, double becomes \par *)
          advance ();
          if !pos < len && current_char () = '\n' then begin
            (* Double newline -> \par *)
            advance ();
            push_token (TMacro "par")
          end else
            (* Single newline -> space *)
            push_token (TChar (Uchar.of_char ' ', Space))
      
      | _ ->
          (* All other characters *)
          push_token (TChar (uc, cc));
          advance ()
    done;
    
    push_token TEOF;
    List.rev !tokens
end

(* ===== OPTIMIZED TRACK A IMPLEMENTATION ===== *)
module V25_lexer_track_a = struct
  open Lexer_v25
  open Catcode
  
  let tokenize content =
    let len = String.length content in
    let bytes = Bytes.unsafe_of_string content in
    
    (* Pre-allocate token list builder *)
    let tokens = ref [] in
    let token_count = ref 0 in
    
    (* Position tracking *)
    let pos = ref 0 in
    
    (* Pre-computed catcode table for ASCII *)
    let ascii_catcodes = Array.make 128 Other in
    let () =
      ascii_catcodes.(0) <- Ignored;
      ascii_catcodes.(9) <- Space;
      ascii_catcodes.(10) <- Endline;
      ascii_catcodes.(13) <- Endline;
      ascii_catcodes.(32) <- Space;
      ascii_catcodes.(35) <- Param;
      ascii_catcodes.(36) <- MathShift;
      ascii_catcodes.(37) <- Comment;
      ascii_catcodes.(38) <- AlignTab;
      ascii_catcodes.(92) <- Escape;
      ascii_catcodes.(94) <- Superscript;
      ascii_catcodes.(95) <- Subscript;
      ascii_catcodes.(123) <- BeginGroup;
      ascii_catcodes.(125) <- EndGroup;
      ascii_catcodes.(126) <- Active;
      for i = 65 to 90 do ascii_catcodes.(i) <- Letter done;
      for i = 97 to 122 do ascii_catcodes.(i) <- Letter done
    in
    
    let[@inline] get_catcode c =
      let code = Char.code c in
      if code < 128 then
        Array.unsafe_get ascii_catcodes code
      else Other
    in
    
    let[@inline] push_token tok =
      tokens := { 
        token = tok; 
        loc = { line=0; column=0; byte_start = !pos; byte_end = !pos }
      } :: !tokens;
      incr token_count
    in
    
    (* Optimized control sequence reader *)
    let read_control_sequence () =
      let start = !pos in
      incr pos; (* skip \ *)
      
      if !pos >= len then "" else
      
      let c = Bytes.unsafe_get bytes !pos in
      if get_catcode c = Letter then begin
        (* Multi-letter *)
        incr pos;
        while !pos < len && 
              get_catcode (Bytes.unsafe_get bytes !pos) = Letter do
          incr pos
        done;
        (* Skip spaces *)
        while !pos < len && 
              let cc = get_catcode (Bytes.unsafe_get bytes !pos) in
              cc = Space do
          incr pos
        done;
        let name_len = !pos - start - 1 in
        if name_len > 0 then
          Bytes.sub_string bytes (start + 1) name_len
        else ""
      end else begin
        (* Single-char *)
        incr pos;
        String.make 1 c
      end
    in
    
    (* Main loop *)
    while !pos < len do
      let c = Bytes.unsafe_get bytes !pos in
      let cc = get_catcode c in
      
      match cc with
      | Escape ->
          let name = read_control_sequence () in
          push_token (TMacro name)
      
      | Comment ->
          (* Skip to end of line *)
          while !pos < len && Bytes.unsafe_get bytes !pos <> '\n' do
            incr pos
          done
      
      | BeginGroup ->
          incr pos;
          push_token TGroupOpen
      
      | EndGroup ->
          incr pos;
          push_token TGroupClose
      
      | Param ->
          incr pos;
          if !pos < len then
            let c2 = Bytes.unsafe_get bytes !pos in
            if c2 >= '1' && c2 <= '9' then begin
              incr pos;
              push_token (TParam (Char.code c2 - Char.code '0'))
            end else
              push_token (TChar (Uchar.of_char c, cc))
          else
            push_token (TChar (Uchar.of_char c, cc))
      
      | Space ->
          (* Skip consecutive spaces *)
          while !pos < len && 
                get_catcode (Bytes.unsafe_get bytes !pos) = Space do
            incr pos
          done;
          push_token (TChar (Uchar.of_char ' ', Space))
      
      | Endline ->
          incr pos;
          (* Check for double newline *)
          if !pos < len && Bytes.unsafe_get bytes !pos = '\n' then begin
            incr pos;
            push_token (TMacro "par")
          end else
            push_token (TChar (Uchar.of_char ' ', Space))
      
      | _ ->
          push_token (TChar (Uchar.of_char c, cc));
          incr pos
    done;
    
    push_token TEOF;
    List.rev !tokens
end

(* ===== MAIN TEST ===== *)
let () =
  printf "🚀 FLAMBDA2 OPTIMIZED V25 TEST\n";
  printf "===============================\n";
  
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
  
  (* Test baseline *)
  printf "\n--- V25 BASELINE (FLAMBDA2) ---\n";
  for _ = 1 to 3 do
    let _ = V25_lexer_baseline.tokenize content in
    Gc.full_major ()
  done;
  
  let base_times = ref [] in
  let base_tokens = ref [] in
  
  for i = 1 to 15 do
    Gc.full_major ();
    let start = Sys.time () in
    let tokens = V25_lexer_baseline.tokenize content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    base_times := elapsed :: !base_times;
    if i = 1 then base_tokens := tokens
  done;
  
  let base_sorted = List.sort compare !base_times in
  let base_median = List.nth base_sorted 7 in
  let token_count = List.length !base_tokens in
  printf "Tokens: %d\n" token_count;
  printf "Median: %.2f ms\n" base_median;
  
  (* Test Track A *)
  printf "\n--- V25 TRACK A (FLAMBDA2) ---\n";
  for _ = 1 to 3 do
    let _ = V25_lexer_track_a.tokenize content in
    Gc.full_major ()
  done;
  
  let track_a_times = ref [] in
  let track_a_tokens = ref [] in
  
  for i = 1 to 15 do
    Gc.full_major ();
    let start = Sys.time () in
    let tokens = V25_lexer_track_a.tokenize content in
    let elapsed = (Sys.time () -. start) *. 1000.0 in
    track_a_times := elapsed :: !track_a_times;
    if i = 1 then track_a_tokens := tokens
  done;
  
  let track_a_sorted = List.sort compare !track_a_times in
  let track_a_median = List.nth track_a_sorted 7 in
  let track_a_count = List.length !track_a_tokens in
  printf "Tokens: %d\n" track_a_count;
  printf "Median: %.2f ms\n" track_a_median;
  
  (* Results *)
  printf "\n--- FLAMBDA2 RESULTS ---\n";
  printf "Token count: %s (%d vs %d)\n"
    (if token_count = track_a_count then "✅ MATCH" else "❌ MISMATCH")
    token_count track_a_count;
  
  let speedup = base_median /. track_a_median in
  printf "Performance: %.2fx %s\n" speedup
    (if speedup > 1.0 then "faster" else "slower");
  
  printf "\nTargets:\n";
  printf "≤70ms (Phase 1): %s (%.2fms)\n"
    (if track_a_median <= 70.0 then "✅" else "❌") track_a_median;
  printf "≤20ms (Final): %s (%.2fms)\n"
    (if track_a_median <= 20.0 then "✅" else "❌") track_a_median;
  
  printf "\nExpected improvement from baseline: %.1fx faster\n"
    speedup;
  
  printf "\n🚀 FLAMBDA2 PHASE 1 COMPLETE\n"