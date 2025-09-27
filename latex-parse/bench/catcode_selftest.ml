open Latex_parse_lib

let expect cond msg =
  if not cond then (
    prerr_endline ("[catcode-selftest] " ^ msg);
    exit 1)

let test_basic () =
  let c = Catcode in
  let ( = ) a b = a = b in
  expect (Catcode.classify_ascii (Char.code '\\') = 0) "\\ should be Escape (0)";
  expect (Catcode.classify_ascii (Char.code '{') = 1) "{ should be BeginGrp (1)";
  expect (Catcode.classify_ascii (Char.code '}') = 2) "} should be EndGrp (2)";
  expect (Catcode.classify_ascii (Char.code '$') = 3) "$ should be Math (3)";
  expect (Catcode.classify_ascii (Char.code '&') = 4) "& should be AlignTab (4)";
  expect
    (Catcode.classify_ascii (Char.code '\n') = 5)
    "NL should be Newline (5)";
  expect (Catcode.classify_ascii (Char.code '#') = 6) "# should be Param (6)";
  expect (Catcode.classify_ascii (Char.code '^') = 7) "^ should be Superscr (7)";
  expect (Catcode.classify_ascii (Char.code '_') = 8) "_ should be Subscr (8)";
  expect (Catcode.classify_ascii 0 = 9) "NUL should be Ignored (9)";
  expect
    (Catcode.classify_ascii (Char.code ' ') = 10)
    "space should be Space (10)";
  expect (Catcode.classify_ascii (Char.code '~') = 13) "~ should be Active (13)";
  expect
    (Catcode.classify_ascii (Char.code '%') = 14)
    "% should be Comment (14)";
  expect (Catcode.classify_ascii 127 = 15) "DEL should be Invalid (15)";
  ()

let test_letters () =
  for c = Char.code 'A' to Char.code 'Z' do
    expect
      (Catcode.classify_ascii c = 11)
      "uppercase letter not classified as Letter (11)"
  done;
  for c = Char.code 'a' to Char.code 'z' do
    expect
      (Catcode.classify_ascii c = 11)
      "lowercase letter not classified as Letter (11)"
  done

let test_invariants () =
  for b = 0 to 255 do
    let k = Catcode.classify_ascii b in
    expect (k >= 0 && k <= 15) "classify_ascii out of bounds"
  done

let () =
  test_basic ();
  test_letters ();
  test_invariants ();
  print_endline "[catcode-selftest] OK"
