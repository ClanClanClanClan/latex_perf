(* Simple test to verify L0 macro fix *)

(* Mock the minimal types needed *)
module Catcode = struct
  type t = 
    | Escape | BeginGroup | EndGroup | MathShift | AlignTab
    | EndLine | Param | Superscript | Subscript | Ignored
    | Space | Letter | Other | Active | Comment | Invalid
    
  let catcode_to_string = function
    | Escape -> "Escape" | BeginGroup -> "BeginGroup" | EndGroup -> "EndGroup"
    | MathShift -> "MathShift" | AlignTab -> "AlignTab" | EndLine -> "EndLine"
    | Param -> "Param" | Superscript -> "Superscript" | Subscript -> "Subscript"
    | Ignored -> "Ignored" | Space -> "Space" | Letter -> "Letter"
    | Other -> "Other" | Active -> "Active" | Comment -> "Comment" | Invalid -> "Invalid"
end

module Lexer_v25 = struct
  type token =
    | TChar of Uchar.t * Catcode.t
    | TMacro of string
    | TParam of int
    | TGroupOpen | TGroupClose
    | TEOF
end

open Printf

let test_display_math_simple () =
  printf "=== SIMPLE L0 MACRO TEST ===\n";
  
  (* Test tokenizing display math *)
  let input = "\\[x^2\\]" in
  printf "Input: %s\n" input;
  
  (* Initialize macros *)
  if not !L0_lexer_track_a_arena.initialized then (
    L0_lexer_track_a_arena.StringOps.macro_counter := 0;
    Hashtbl.clear L0_lexer_track_a_arena.StringOps.macro_table;
    Hashtbl.clear L0_lexer_track_a_arena.StringOps.reverse_macro_table;
    L0_lexer_track_a_arena.StringOps.initialize_builtin_macros ();
    L0_lexer_track_a_arena.initialized := true
  );
  
  (* Tokenize *)
  let packed_tokens = L0_lexer_track_a_arena.tokenize_arena input in
  printf "Packed tokens: %d\n" (Array.length packed_tokens);
  
  (* Check what macros we got *)
  Array.iteri (fun i packed ->
    let catcode = L0_lexer_track_a_arena.TokenPacking.unpack_catcode packed in
    let data = L0_lexer_track_a_arena.TokenPacking.unpack_data packed in
    if catcode = L0_lexer_track_a_arena.TokenPacking.cc_escape then (
      let name = L0_lexer_track_a_arena.StringOps.get_macro_name_by_id data in
      printf "  [%d] Macro: \"%s\" (id=%d) %s\n" i name data
        (if name = "[" || name = "]" then "✅ RECOGNIZED!" else "")
    ) else (
      printf "  [%d] Other token (catcode=%d, data=%d)\n" i catcode data
    )
  ) packed_tokens;
  
  (* Check hashtable contents *)
  printf "\nMacro table contents (first 10):\n";
  let count = ref 0 in
  Hashtbl.iter (fun name id ->
    if !count < 10 then (
      printf "  \"%s\" -> %d\n" name id;
      incr count
    )
  ) L0_lexer_track_a_arena.StringOps.macro_table;
  
  printf "\nTotal macros in table: %d\n" (Hashtbl.length L0_lexer_track_a_arena.StringOps.macro_table);
  
  (* Check if [ and ] are in the table *)
  let has_lbrack = Hashtbl.mem L0_lexer_track_a_arena.StringOps.macro_table "[" in
  let has_rbrack = Hashtbl.mem L0_lexer_track_a_arena.StringOps.macro_table "]" in
  printf "Has '[' macro: %b\n" has_lbrack;
  printf "Has ']' macro: %b\n" has_rbrack;
  
  if has_lbrack && has_rbrack then
    printf "\n✅ SUCCESS: Display math macros are in the built-in catalog!\n"
  else
    printf "\n❌ FAILED: Display math macros missing from catalog\n"

let () = test_display_math_simple ()