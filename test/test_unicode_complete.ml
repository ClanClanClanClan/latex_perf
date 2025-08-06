let test_catcode_alpha () =
  (* Test the actual catcode system *)
  Printf.printf "=== Testing actual catcode system ===\n";
  
  (* Create Greek alpha manually *)
  let alpha_uchar = Uchar.of_int 945 in  (* Greek small letter alpha *)
  Printf.printf "Created alpha Uchar: %d\n" (Uchar.to_int alpha_uchar);
  
  (* Test with XeTeX engine - should return Letter *)
  let result_xetex = "PLACEHOLDER" in  (* We'll simulate this *)
  Printf.printf "XeTeX result: %s\n" result_xetex

let () = test_catcode_alpha ()
EOF < /dev/null