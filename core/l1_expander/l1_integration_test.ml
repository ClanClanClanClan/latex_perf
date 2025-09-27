(* Spot-compare token sequences on tiny samples for both strategies. *)

let expect cond msg =
  if not cond then (
    prerr_endline ("[l1-integ] " ^ msg);
    exit 1)

module L = L1_expander

let to_list toks = toks

let tok_str = function
  | L.L1_ab_api.Control n -> "\\" ^ n
  | L.L1_ab_api.Text t -> "T(" ^ t ^ ")"

let eq_list a b =
  let rec go = function
    | [], [] -> true
    | x :: xs, y :: ys -> x = y && go (xs, ys)
    | _ -> false
  in
  go (a, b)

let test_case input exp_a exp_b =
  let ta = L.L1_ab_api.tokenize_a input |> to_list in
  let tb = L.L1_ab_api.tokenize_b input |> to_list in
  let sa = List.map tok_str ta in
  let sb = List.map tok_str tb in
  let show xs = String.concat " | " xs in
  expect (eq_list sa exp_a) ("A mismatch: " ^ show sa);
  expect (eq_list sb exp_b) ("B mismatch: " ^ show sb)

let () =
  (* Sample 1: simple controls and text *)
  test_case "\\foo A \\Bar"
    [ "\\foo"; "T( A )"; "\\Bar" ]
    [ "\\foo"; "T( A )"; "\\bar" ];

  (* Sample 2: adjacent backslashes w/o name, treated as text *)
  test_case "\\\\\\xyz"
    [ "T(\\)"; "T(\\)"; "\\xyz" ]
    [ "T(\\)"; "T(\\)"; "\\xyz" ];

  (* From corpora *)
  let read_all p =
    let ic = open_in p in
    Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
    really_input_string ic (in_channel_length ic)
  in
  let c1 = read_all "corpora/l1/sample_basic.tex" in
  test_case c1 [ "\\foo"; "T( A )"; "\\Bar" ] [ "\\foo"; "T( A )"; "\\bar" ];
  let c2 = read_all "corpora/l1/sample_adjacent_backslashes.tex" in
  test_case c2 [ "T(\\)"; "T(\\)"; "\\xyz" ] [ "T(\\)"; "T(\\)"; "\\xyz" ];
  let c3 = read_all "corpora/l1/sample_mixed_text.tex" in
  (* Expected: text chunk before, control Alpha/Beta (case folded in B) *)
  test_case c3
    [ "T(This is text with )"; "\\Alpha"; "T( and )"; "\\beta"; "T( tokens.)" ]
    [ "T(This is text with )"; "\\alpha"; "T( and )"; "\\beta"; "T( tokens.)" ];

  let c4 = read_all "corpora/l1/sample_comment.tex" in
  (* Our minimal tokenizer doesn't treat % specially; it's text. *)
  test_case c4
    [ "T(% This is a comment line with a control )"; "\\Cmd" ]
    [ "T(% This is a comment line with a control )"; "\\cmd" ];

  (* Args + braces: treat braces as text, control names as contiguous letters *)
  let c5 = read_all "corpora/l1/sample_args.tex" in
  test_case c5
    [ "\\cmd"; "T({arg} and )"; "\\section"; "T({Title})" ]
    [ "\\cmd"; "T({arg} and )"; "\\section"; "T({Title})" ];

  (* Math content remains text apart from controls *)
  let c6 = read_all "corpora/l1/sample_math.tex" in
  test_case c6
    [ "T(Math mode: $x^2 + y^2 = z^2$ and inline )"; "\\alpha"; "T(.)" ]
    [ "T(Math mode: $x^2 + y^2 = z^2$ and inline )"; "\\alpha"; "T(.)" ];

  (* Trailing backslash becomes text in our minimal tokenizer *)
  let c7 = read_all "corpora/l1/sample_trailing_backslash.tex" in
  test_case c7
    [ "T(Trailing backslash: )"; "T(\\)" ]
    [ "T(Trailing backslash: )"; "T(\\)" ];

  (* Nested braces with controls treated as text for braces, control names
     parsed *)
  let c8 = read_all "corpora/l1/sample_nested_braces.tex" in
  test_case c8
    [ "\\textbf"; "T({)"; "\\emph"; "T({N}})" ]
    [ "\\textbf"; "T({)"; "\\emph"; "T({N}})" ];

  let c9 = read_all "corpora/l1/sample_brace_edge.tex" in
  test_case c9
    [ "\\section"; "T({A {nested}})" ]
    [ "\\section"; "T({A {nested}})" ];

  let c10 = read_all "corpora/l1/sample_nested_combo.tex" in
  test_case c10
    [ "T(Before )"; "\\textbf"; "T({A )"; "\\emph"; "T({B} C})"; "T( after)" ]
    [ "T(Before )"; "\\textbf"; "T({A )"; "\\emph"; "T({b} C})"; "T( after)" ];

  let c11 = read_all "corpora/l1/sample_malformed_unmatched_brace.tex" in
  test_case c11
    [ "\\section"; "T({A {nested)" ]
    [ "\\section"; "T({a {nested)" ];

  let c12 = read_all "corpora/l1/sample_malformed_controls.tex" in
  (* Our tokenizer only recognizes letter sequences after backslash. So "\\1bad"
     yields Text("\\") then Text("1bad"); "\\@cmd" yields Text("\\") then
     Text("@cmd"). *)
  test_case c12
    [
      "T(Malformed controls: )";
      "T(\\)";
      "T(1bad and )";
      "T(\\)";
      "T(@cmd appear here.)";
    ]
    [
      "T(Malformed controls: )";
      "T(\\)";
      "T(1bad and )";
      "T(\\)";
      "T(@cmd appear here.)";
    ];

  let c13 = read_all "corpora/l1/sample_malformed_space.tex" in
  (* Backslash followed by space is treated as text in this minimal
     tokenizer. *)
  test_case c13
    [ "T(Backslash-space: )"; "T(\\)"; "T( text and )"; "T(\\)"; "T(  more.)" ]
    [ "T(Backslash-space: )"; "T(\\)"; "T( text and )"; "T(\\)"; "T(  more.)" ];

  let c14 = read_all "corpora/l1/sample_backslash_newline.tex" in
  (* Backslash-newline → Text("\\") then text chunk with newline retained. *)
  test_case c14
    [ "T(Line1 )"; "T(\\)"; "T(\nLine2)" ]
    [ "T(Line1 )"; "T(\\)"; "T(\nLine2)" ];

  let c15 = read_all "corpora/l1/sample_math_only.tex" in
  (* Math is text here, control names still parsed. *)
  test_case c15
    [ "T($E=mc^2$ and $a^2 + b^2 = c^2$.)" ]
    [ "T($E=mc^2$ and $a^2 + b^2 = c^2$.)" ];

  print_endline "[l1-integ] OK"
