(* Phase C - SIMD FFI Bindings for LaTeX Perfectionist *)
(* OCaml interface to C SIMD microkernel *)

open Bigarray

(* Token types matching C definitions *)
type catcode =
  | Escape (* 0 - \ *)
  | BeginGrp (* 1 - { *)
  | EndGrp (* 2 - } *)
  | Math (* 3 - $ *)
  | Newline (* 5 - \n *)
  | Space (* 10 - space *)
  | Letter (* 11 - a-z, A-Z *)
  | Other (* 12 - default *)
  | Comment (* 14 - % *)

let catcode_to_int = function
  | Escape -> 0
  | BeginGrp -> 1
  | EndGrp -> 2
  | Math -> 3
  | Newline -> 5
  | Space -> 10
  | Letter -> 11
  | Other -> 12
  | Comment -> 14

let int_to_catcode = function
  | 0 -> Escape
  | 1 -> BeginGrp
  | 2 -> EndGrp
  | 3 -> Math
  | 5 -> Newline
  | 10 -> Space
  | 11 -> Letter
  | 14 -> Comment
  | _ -> Other

(* SIMD token buffer structure (matches C struct) *)
type simd_buffer = {
  kinds : (int32, int32_elt, c_layout) Array1.t;
  codes : (int32, int32_elt, c_layout) Array1.t;
  start_pos : (int32, int32_elt, c_layout) Array1.t;
  end_pos : (int32, int32_elt, c_layout) Array1.t;
  lines : (int32, int32_elt, c_layout) Array1.t;
  cols : (int32, int32_elt, c_layout) Array1.t;
  mutable count : int;
  capacity : int;
}

(* Create SIMD buffer with specified capacity *)
let create_simd_buffer capacity =
  let mk () = Array1.create Int32 C_layout capacity in
  {
    kinds = mk ();
    codes = mk ();
    start_pos = mk ();
    end_pos = mk ();
    lines = mk ();
    cols = mk ();
    count = 0;
    capacity;
  }

(* Clear SIMD buffer *)
let clear_simd_buffer buf = buf.count <- 0

(* FFI external declarations *)
external simd_tokenize_c :
  (char, int8_unsigned_elt, c_layout) Array1.t ->
  int ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  int ->
  int = "simd_tokenize_stub_bytecode" "simd_tokenize_stub"

external simd_vs_scalar_benchmark_c :
  (char, int8_unsigned_elt, c_layout) Array1.t ->
  int ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  (int32, int32_elt, c_layout) Array1.t ->
  int ->
  int = "simd_vs_scalar_benchmark_stub_bytecode" "simd_vs_scalar_benchmark_stub"

(* High-level SIMD tokenization function *)
let simd_tokenize input_ba buf =
  clear_simd_buffer buf;
  let input_len = Array1.dim input_ba in
  let token_count =
    simd_tokenize_c input_ba input_len buf.kinds buf.codes buf.start_pos
      buf.end_pos buf.lines buf.cols buf.capacity
  in
  if token_count >= 0 then (
    buf.count <- token_count;
    token_count)
  else failwith "SIMD tokenization failed"

(* Convert bytes to bigarray for SIMD processing *)
let bytes_to_bigarray bytes =
  let len = Bytes.length bytes in
  let ba = Array1.create Char C_layout len in
  for i = 0 to len - 1 do
    Array1.unsafe_set ba i (Bytes.get bytes i)
  done;
  ba

(* High-level interface: tokenize bytes with SIMD *)
let tokenize_bytes_simd bytes capacity =
  let input_ba = bytes_to_bigarray bytes in
  let buf = create_simd_buffer capacity in
  let token_count = simd_tokenize input_ba buf in
  (buf, token_count)

(* Performance comparison: SIMD vs Scalar *)
let benchmark_simd_vs_scalar bytes capacity =
  let input_ba = bytes_to_bigarray bytes in
  let simd_buf = create_simd_buffer capacity in
  let scalar_buf = create_simd_buffer capacity in

  let input_len = Array1.dim input_ba in
  let diff =
    simd_vs_scalar_benchmark_c input_ba input_len simd_buf.kinds simd_buf.codes
      simd_buf.start_pos simd_buf.end_pos simd_buf.lines simd_buf.cols
      scalar_buf.kinds scalar_buf.codes scalar_buf.start_pos scalar_buf.end_pos
      scalar_buf.lines scalar_buf.cols capacity
  in

  (* Update counts based on actual results *)
  simd_buf.count <- (if diff >= 0 then diff else 0) + scalar_buf.count;

  (simd_buf, scalar_buf, diff)

(* Convert SIMD buffer to OCaml compatible format *)
(* let simd_buffer_to_soa buf existing_soa = (* Copy SIMD results to existing
   SoA structure *) let count = min buf.count existing_soa.n in for i = 0 to
   count - 1 do let kind = Array1.unsafe_get buf.kinds i |> Int32.to_int in let
   code = Array1.unsafe_get buf.codes i |> Int32.to_int in let start_pos =
   Array1.unsafe_get buf.start_pos i |> Int32.to_int in let end_pos =
   Array1.unsafe_get buf.end_pos i |> Int32.to_int in let line =
   Array1.unsafe_get buf.lines i |> Int32.to_int in let col = Array1.unsafe_get
   buf.cols i |> Int32.to_int in

   Array1.unsafe_set existing_soa.kind i (Int32.of_int kind); Array1.unsafe_set
   existing_soa.char_code i (Int32.of_int code); Array1.unsafe_set
   existing_soa.start_pos i (Int32.of_int start_pos); Array1.unsafe_set
   existing_soa.end_pos i (Int32.of_int end_pos); Array1.unsafe_set
   existing_soa.line i (Int32.of_int line); Array1.unsafe_set existing_soa.col i
   (Int32.of_int col) done; existing_soa.n <- count; count *)

(* Architecture detection *)
let simd_architecture () =
  (* This would normally use cpuid or similar, but for now return based on
     compilation *)
  match Sys.word_size with
  | 64 -> (
      match Sys.os_type with
      | "Unix" -> (
          try
            let ic = Unix.open_process_in "uname -m" in
            let arch = input_line ic in
            let _ = Unix.close_process_in ic in
            if String.contains arch '6' then "AVX2"
            else if Str.string_match (Str.regexp ".*arm.*\\|.*aarch.*") arch 0
            then "NEON"
            else "Scalar"
          with _ -> "Scalar")
      | _ -> "Scalar")
  | _ -> "Scalar"

(* Performance info *)
let simd_info () =
  Printf.sprintf "SIMD Architecture: %s, SIMD Width: %s" (simd_architecture ())
    (match simd_architecture () with
    | "AVX2" -> "32 bytes"
    | "NEON" -> "16 bytes"
    | _ -> "1 byte (scalar)")

(* Compatibility layer with existing tokens_soa type *)
(* Type will be imported from main module when integrated *)

(* Enhanced tokenization with SIMD acceleration *)
(* let tokenize_with_simd_acceleration input_bytes existing_soa = let simd_buf,
   token_count = tokenize_bytes_simd input_bytes existing_soa.capacity in let
   copied_count = simd_buffer_to_soa simd_buf existing_soa in copied_count *)
