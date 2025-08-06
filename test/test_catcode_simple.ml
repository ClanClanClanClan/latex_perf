(* Simple Catcode Test - Basic validation *)

let test_catcode_basic () =
  Printf.printf "Testing basic catcode functionality:\n";
  
  (* Test letter classification *)
  let uchar_A = Uchar.of_int 65 in  (* ASCII 'A' *)
  let catcode_A = Catcode.catcode_of Catcode.PdfTeX uchar_A in
  
  Printf.printf "  ASCII 'A' (65) -> %s\n" (Catcode.catcode_to_string catcode_A);
  
  (* Test backslash *)
  let uchar_backslash = Uchar.of_int 92 in  (* ASCII '\' *) 
  let catcode_backslash = Catcode.catcode_of Catcode.PdfTeX uchar_backslash in
  
  Printf.printf "  ASCII '\\' (92) -> %s\n" (Catcode.catcode_to_string catcode_backslash);
  
  (* Basic assertions *)
  assert (catcode_A = Catcode.Letter);
  assert (catcode_backslash = Catcode.Escape);
  
  Printf.printf "  ✓ Basic catcode tests passed\n"

let () =
  Printf.printf "=== Simple Catcode Test ===\n";
  test_catcode_basic ();
  Printf.printf "✅ Catcode module working correctly!\n"