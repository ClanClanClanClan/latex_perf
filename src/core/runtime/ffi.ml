(* LaTeX Perfectionist v25 - Track B OCaml FFI Bindings
 * High-performance C kernel integration via Ctypes
 *)

open Ctypes
open Foreign

(* === TYPE DEFINITIONS === *)

(* C enum: token_type_t *)
let token_type_char = 0
let token_type_macro = 1  
let token_type_param = 2
let token_type_group_open = 3
let token_type_group_close = 4
let token_type_eof = 5

(* C enum: catcode_t *)
let catcode_escape = 0
let catcode_begin_group = 1
let catcode_end_group = 2
let catcode_math_shift = 3
let catcode_alignment = 4
let catcode_eol = 5
let catcode_parameter = 6
let catcode_superscript = 7
let catcode_subscript = 8
let catcode_ignored = 9
let catcode_space = 10
let catcode_letter = 11
let catcode_other = 12
let catcode_active = 13
let catcode_comment = 14
let catcode_invalid = 15

(* C struct: token_t - 16 bytes *)
type c_token
let c_token : c_token structure typ = structure "token_t"
let c_token_type = field c_token "type" uint32_t
let c_token_offset = field c_token "offset" uint32_t  
let c_token_line = field c_token "line" uint16_t
let c_token_col = field c_token "col" uint16_t
let c_token_data = field c_token "data" uint32_t (* Union simplified as uint32_t *)
let () = seal c_token

(* C struct: arena_t *)
type c_arena
let c_arena : c_arena structure typ = structure "arena_t"
let c_arena_base = field c_arena "base" (ptr char)
let c_arena_size = field c_arena "size" size_t
let c_arena_offset = field c_arena "offset" size_t
let c_arena_tokens_count = field c_arena "tokens_count" size_t
let c_arena_strings_size = field c_arena "strings_size" size_t
let () = seal c_arena

(* C struct: perf_stats_t *)
type c_perf_stats  
let c_perf_stats : c_perf_stats structure typ = structure "perf_stats_t"
let c_perf_bytes = field c_perf_stats "bytes_processed" uint64_t
let c_perf_tokens = field c_perf_stats "tokens_generated" uint64_t
let c_perf_time_ns = field c_perf_stats "time_ns" uint64_t
let c_perf_simd_ops = field c_perf_stats "simd_operations" uint32_t
let c_perf_scalar_fallbacks = field c_perf_stats "scalar_fallbacks" uint32_t
let c_perf_simd_enabled = field c_perf_stats "simd_enabled" bool
let () = seal c_perf_stats

(* === C FUNCTION BINDINGS === *)

(* Arena management *)
let arena_create = foreign "arena_create" (size_t @-> returning (ptr c_arena))
let arena_destroy = foreign "arena_destroy" (ptr c_arena @-> returning void)
let arena_reset = foreign "arena_reset" (ptr c_arena @-> returning void)
let arena_alloc_tokens = foreign "arena_alloc_tokens" 
  (ptr c_arena @-> size_t @-> returning (ptr c_token))

(* Scalar lexer *)
let catcode_init = foreign "catcode_init" (void @-> returning void)
let lexer_tokenize_c_scalar = foreign "lexer_tokenize_scalar"
  (ptr char @-> size_t @-> ptr c_token @-> size_t @-> returning size_t)

(* SIMD lexer (optional) *)
let lexer_tokenize_c_simd = foreign "lexer_tokenize_simd"
  (ptr char @-> size_t @-> ptr c_token @-> size_t @-> returning size_t)

(* Feature detection *)
let simd_available = foreign "simd_available" (void @-> returning bool)
let simd_name = foreign "simd_name" (void @-> returning string)

(* Performance stats *)
let get_perf_stats = foreign "get_perf_stats" (void @-> returning c_perf_stats)
let reset_perf_stats = foreign "reset_perf_stats" (void @-> returning void)

(* === OCAML WRAPPER TYPES === *)

type track_b_token = {
  token_type : int;
  offset : int;
  line : int;
  col : int;
  data : int; (* Simplified - real implementation would decode union *)
}

type track_b_stats = {
  bytes_processed : int64;
  tokens_generated : int64;
  time_ns : int64;
  simd_operations : int;
  scalar_fallbacks : int;
  simd_enabled : bool;
}

(* === CONVERSION FUNCTIONS === *)

(* Convert C token to OCaml token *)
let c_token_to_ocaml (c_tok : c_token structure) : track_b_token =
  {
    token_type = Unsigned.UInt32.to_int (getf c_tok c_token_type);
    offset = Unsigned.UInt32.to_int (getf c_tok c_token_offset);
    line = Unsigned.UInt16.to_int (getf c_tok c_token_line);
    col = Unsigned.UInt16.to_int (getf c_tok c_token_col);
    data = Unsigned.UInt32.to_int (getf c_tok c_token_data);
  }

(* Convert C stats to OCaml stats *)
let c_stats_to_ocaml (c_stats : c_perf_stats structure) : track_b_stats =
  {
    bytes_processed = Unsigned.UInt64.to_int64 (getf c_stats c_perf_bytes);
    tokens_generated = Unsigned.UInt64.to_int64 (getf c_stats c_perf_tokens);
    time_ns = Unsigned.UInt64.to_int64 (getf c_stats c_perf_time_ns);
    simd_operations = Unsigned.UInt32.to_int (getf c_stats c_perf_simd_ops);
    scalar_fallbacks = Unsigned.UInt32.to_int (getf c_stats c_perf_scalar_fallbacks);
    simd_enabled = getf c_stats c_perf_simd_enabled;
  }

(* === HIGH-LEVEL API === *)

(* Track B initialization *)
let init () =
  catcode_init ()

(* Check SIMD capabilities *)
let simd_info () =
  let available = simd_available () in
  let name = if available then simd_name () else "none" in
  (available, name)

(* High-level tokenization function *)
let tokenize_track_b ?(use_simd=true) (input : string) : track_b_token list =
  let input_len = String.length input in
  let max_tokens = input_len / 4 + 1000 in (* Estimate token count *)
  
  (* Create arena *)
  let arena = arena_create (Unsigned.Size_t.of_int max_tokens) in
  if is_null arena then
    failwith "Track B: Failed to create arena";
    
  (* Allocate token buffer *)
  let token_buf = arena_alloc_tokens arena (Unsigned.Size_t.of_int max_tokens) in
  if is_null token_buf then (
    arena_destroy arena;
    failwith "Track B: Failed to allocate token buffer"
  );
  
  (* Choose tokenization function *)
  let tokenize_fn = 
    if use_simd && simd_available () then
      lexer_tokenize_c_simd
    else
      lexer_tokenize_c_scalar
  in
  
  (* Convert string to C buffer *)
  let input_buf = Bytes.unsafe_of_string input in
  let input_ptr = bigarray_start ptr1 (Bytes.to_bigarray input_buf) in
  
  (* Perform tokenization *)
  let token_count = tokenize_fn input_ptr 
    (Unsigned.Size_t.of_int input_len) 
    token_buf 
    (Unsigned.Size_t.of_int max_tokens) in
    
  (* Convert results to OCaml *)
  let result = ref [] in
  for i = Unsigned.Size_t.to_int token_count - 1 downto 0 do
    let c_tok = !@(token_buf +@ i) in
    let ocaml_tok = c_token_to_ocaml c_tok in
    result := ocaml_tok :: !result
  done;
  
  (* Cleanup *)
  arena_destroy arena;
  
  !result

(* Get performance statistics *)
let get_stats () : track_b_stats =
  let c_stats = get_perf_stats () in
  c_stats_to_ocaml c_stats

(* Reset performance counters *)
let reset_stats () =
  reset_perf_stats ()

(* === INTEGRATION WITH EXISTING LEXER === *)

(* Convert Track B tokens to Lexer_v25.token format *)
let track_b_to_lexer_token (tb_token : track_b_token) : Lexer_v25.token =
  match tb_token.token_type with
  | 0 -> (* TOKEN_CHAR *)
    let codepoint = Uchar.of_int (tb_token.data land 0xFFFFFF) in
    let catcode_val = (tb_token.data lsr 24) land 0xFF in
    let catcode = match catcode_val with
      | 0 -> Data.Catcode.Escape | 1 -> Data.Catcode.BeginGroup
      | 2 -> Data.Catcode.EndGroup | 3 -> Data.Catcode.MathShift
      | 4 -> Data.Catcode.Alignment | 5 -> Data.Catcode.EOL
      | 6 -> Data.Catcode.Parameter | 7 -> Data.Catcode.Superscript
      | 8 -> Data.Catcode.Subscript | 9 -> Data.Catcode.Ignored
      | 10 -> Data.Catcode.Space | 11 -> Data.Catcode.Letter
      | 12 -> Data.Catcode.Other | 13 -> Data.Catcode.Active
      | 14 -> Data.Catcode.Comment | _ -> Data.Catcode.Invalid
    in
    Lexer_v25.TChar (codepoint, catcode)
  | 1 -> (* TOKEN_MACRO *)
    (* Note: Retrieve macro name from string arena *)
    Lexer_v25.TMacro "macro" (* Placeholder *)
  | 2 -> (* TOKEN_PARAM *)
    Lexer_v25.TParam tb_token.data
  | 3 -> Lexer_v25.TGroupOpen
  | 4 -> Lexer_v25.TGroupClose
  | 5 -> Lexer_v25.TEOF
  | _ -> failwith ("Unknown token type: " ^ string_of_int tb_token.token_type)

(* Main Track B tokenization function matching Lexer_v25.tokenize signature *)
let tokenize (input : string) : Lexer_v25.token list =
  let track_b_tokens = tokenize_track_b input in
  List.map track_b_to_lexer_token track_b_tokens