(* Test for Catcode module - Week 1-2 Deliverable *)

open Data.Catcode

let test_basic_catcodes () =
  Printf.printf "Testing basic catcode assignments:\n";
  
  (* Test escape character *)
  let c = catcode_of PdfTeX (Uchar.of_char '\\') in
  Printf.printf "  '\\\\' -> %s\n" (catcode_to_string c);
  assert (c = Escape);
  
  (* Test group delimiters *)
  let c = catcode_of PdfTeX (Uchar.of_char '{') in
  Printf.printf "  '{' -> %s\n" (catcode_to_string c);
  assert (c = BeginGroup);
  
  let c = catcode_of PdfTeX (Uchar.of_char '}') in
  Printf.printf "  '}' -> %s\n" (catcode_to_string c);
  assert (c = EndGroup);
  
  (* Test math shift *)
  let c = catcode_of PdfTeX (Uchar.of_char '$') in
  Printf.printf "  '$' -> %s\n" (catcode_to_string c);
  assert (c = MathShift);
  
  (* Test letters *)
  let c = catcode_of PdfTeX (Uchar.of_char 'a') in
  Printf.printf "  'a' -> %s\n" (catcode_to_string c);
  assert (c = Letter);
  
  let c = catcode_of PdfTeX (Uchar.of_char 'Z') in
  Printf.printf "  'Z' -> %s\n" (catcode_to_string c);
  assert (c = Letter);
  
  (* Test space *)
  let c = catcode_of PdfTeX (Uchar.of_char ' ') in
  Printf.printf "  ' ' -> %s\n" (catcode_to_string c);
  assert (c = Space);
  
  (* Test comment *)
  let c = catcode_of PdfTeX (Uchar.of_char '%') in
  Printf.printf "  '%%' -> %s\n" (catcode_to_string c);
  assert (c = Comment);
  
  (* Test other *)
  let c = catcode_of PdfTeX (Uchar.of_char '1') in
  Printf.printf "  '1' -> %s\n" (catcode_to_string c);
  assert (c = Other);
  
  Printf.printf "  ✓ All basic catcodes correct\n\n"

let test_unicode_handling () =
  Printf.printf "Testing Unicode handling:\n";
  
  (* Test high ASCII as Invalid in PdfTeX *)
  let c = catcode_of PdfTeX (Uchar.of_int 255) in
  Printf.printf "  U+00FF in PdfTeX -> %s\n" (catcode_to_string c);
  assert (c = Invalid);
  
  (* Test Unicode letter in XeTeX *)
  let c = catcode_of XeTeX (Uchar.of_int 0x00E9) in (* é *)
  Printf.printf "  U+00E9 (é) in XeTeX -> %s\n" (catcode_to_string c);
  assert (c = Letter);
  
  (* Test Unicode letter in LuaTeX *)
  let c = catcode_of LuaTeX (Uchar.of_int 0x03B1) in (* α *)
  Printf.printf "  U+03B1 (α) in LuaTeX -> %s\n" (catcode_to_string c);
  assert (c = Letter);
  
  (* Test Unicode non-letter in XeTeX *)
  let c = catcode_of XeTeX (Uchar.of_int 0x2020) in (* † *)
  Printf.printf "  U+2020 (†) in XeTeX -> %s\n" (catcode_to_string c);
  assert (c = Other);
  
  Printf.printf "  ✓ Unicode handling correct\n\n"

let test_serialization () =
  Printf.printf "Testing serialization:\n";
  
  let test_roundtrip catcode =
    let n = catcode_to_int catcode in
    match int_to_catcode n with
    | Some c' ->
        Printf.printf "  %s -> %d -> %s\n" 
          (catcode_to_string catcode) n (catcode_to_string c');
        assert (catcode_eq catcode c')
    | None -> failwith "Serialization failed"
  in
  
  test_roundtrip Escape;
  test_roundtrip BeginGroup;
  test_roundtrip EndGroup;
  test_roundtrip MathShift;
  test_roundtrip AlignTab;
  test_roundtrip EndLine;
  test_roundtrip Param;
  test_roundtrip Superscript;
  test_roundtrip Subscript;
  test_roundtrip Ignored;
  test_roundtrip Space;
  test_roundtrip Letter;
  test_roundtrip Other;
  test_roundtrip Active;
  test_roundtrip Comment;
  test_roundtrip Invalid;
  
  Printf.printf "  ✓ All serialization roundtrips successful\n\n"

let test_equality () =
  Printf.printf "Testing catcode equality:\n";
  
  assert (catcode_eq Escape Escape);
  assert (not (catcode_eq Escape BeginGroup));
  assert (catcode_eq Letter Letter);
  assert (not (catcode_eq Letter Other));
  
  Printf.printf "  ✓ Equality function correct\n\n"

let () =
  Printf.printf "=== Catcode Module Tests (Week 1-2) ===\n\n";
  test_basic_catcodes ();
  test_unicode_handling ();
  test_serialization ();
  test_equality ();
  Printf.printf "✓ All tests passed!\n"