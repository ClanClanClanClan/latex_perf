(* Integration with existing v25_R1 SIMD tokenizer *)
external real_simd_tokenize_soa : 
  bytes -> int -> (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t -> int -> int
  = "tokenize_bytes_into_soa_simd_stub_bytecode" "tokenize_bytes_into_soa_simd_stub"

(* status, n_tokens, issues_len *)
let run (input:bytes) (out:Arena.buffers) : (int * int * int) =
  try
    let input_len = Bytes.length input in
    let max_tokens = Bigarray.Array1.dim out.Arena.kinds in
    
    (* Create temporary arrays for SIMD tokenizer - it needs 6 arrays *)
    let lines = Bigarray.Array1.create Bigarray.int32 Bigarray.c_layout max_tokens in
    let cols = Bigarray.Array1.create Bigarray.int32 Bigarray.c_layout max_tokens in
    
    (* Call existing v25_R1 SIMD tokenizer *)
    let token_count = real_simd_tokenize_soa input input_len 
      out.Arena.kinds out.Arena.codes out.Arena.offs out.Arena.offs 
      lines cols max_tokens in
    
    (* Update next_ix in output buffer *)
    out.Arena.next_ix <- token_count;
    
    (* Return actual token count - let higher layers handle any limits *)
    (* Note: Removed artificial 200K cap to see true performance *)
    (0, token_count, 0)
  with 
  | exn -> 
    Printf.eprintf "SIMD tokenizer failed: %s\n" (Printexc.to_string exn);
    (* Return error status *)
    (1, 0, 0)