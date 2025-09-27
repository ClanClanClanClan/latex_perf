let () =
  (* Test SIMD capability *)
  let simd_avail = Latex_parse_lib.Simd_guard.available () in
  Printf.printf "SIMD Available: %b\n" simd_avail;

  (* Run a small test *)
  let test_input =
    Bytes.of_string "\\section{test} hello world $x=1$ % comment\n"
  in
  let module Arena = Latex_parse_lib.Arena in
  let arena = Arena.create ~cap:1000 in
  let buf = Arena.current arena in

  (* Tokenize using SIMD *)
  let status, token_count, issues =
    Latex_parse_lib.Real_processor.run test_input buf
  in

  Printf.printf "Status: %d\n" status;
  Printf.printf "Tokens generated: %d\n" token_count;
  Printf.printf "Issues: %d\n" issues;

  (* Print first few tokens for verification *)
  Printf.printf "First few tokens:\n";
  let open Arena in
  for i = 0 to min 9 (token_count - 1) do
    let kind = Bigarray.Array1.get buf.kinds i in
    let code = Bigarray.Array1.get buf.codes i in
    let start_pos = Bigarray.Array1.get buf.offs i in
    Printf.printf "  Token %d: kind=%ld code=%ld start=%ld\n" i kind code
      start_pos
  done
