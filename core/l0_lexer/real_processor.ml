(* Integration with existing high-performance SIMD tokenizer *)
external real_simd_tokenize_soa :
  bytes ->
  int ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  int ->
  int
  = "tokenize_bytes_into_soa_simd_stub_bytecode"
    "tokenize_bytes_into_soa_simd_stub"

(* status, n_tokens, issues_len *)
let run (input : bytes) (out : Arena.buffers) : int * int * int =
  try
    let input_len = Bytes.length input in
    let max_tokens = Bigarray.Array1.dim out.Arena.kinds in

    (* Clear the output buffer *)
    out.Arena.next_ix <- 0;

    (* Use pre-allocated temporary arrays from Arena to avoid memory churn *)
    let lines = out.Arena.lines in
    let cols = out.Arena.cols in

    (* Call existing high-performance SIMD tokenizer *)
    let token_count =
      real_simd_tokenize_soa input input_len out.Arena.kinds out.Arena.codes
        out.Arena.offs out.Arena.issues lines cols max_tokens
    in

    (* Update next_ix in output buffer *)
    out.Arena.next_ix <- token_count;

    (* Count every issue entry up to the produced token count to preserve
       accuracy. *)
    let issues_len =
      let limit = min token_count max_tokens in
      if limit <= 0 then 0
      else
        let count = ref 0 in
        for i = 0 to limit - 1 do
          if Int32.compare out.Arena.issues.{i} 0l <> 0 then incr count
        done;
        !count
    in

    (* Return success with actual token count and issues *)
    (0, token_count, issues_len)
  with exn ->
    Printf.eprintf "SIMD tokenizer failed: %s\n" (Printexc.to_string exn);
    (* Return error status *)
    (1, 0, 0)
