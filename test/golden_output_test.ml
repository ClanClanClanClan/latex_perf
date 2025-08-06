(* Golden Output Testing - Week 3-6 Requirement *)
(* LaTeX Perfectionist v25 - "golden output vs TeX — snapshot" *)

open Core.Chunk_lexer
open Core.Lexer_v25

(** Test case with expected tokenization *)
type test_case = {
  name: string;
  input: string;
  expected_tokens: string list;  (* String representation of expected tokens *)
}

(** Golden test cases based on TeX behavior *)
let golden_test_cases = [
  {
    name = "basic_document";
    input = "\\documentclass{article}";
    expected_tokens = [
      "TMacro(documentclass)";
      "TGroupOpen";
      "TChar(a,Letter)"; "TChar(r,Letter)"; "TChar(t,Letter)"; 
      "TChar(i,Letter)"; "TChar(c,Letter)"; "TChar(l,Letter)"; "TChar(e,Letter)";
      "TGroupClose";
      "TEOF";
    ];
  };
  
  {
    name = "math_mode";
    input = "$x^2 + y_i$";
    expected_tokens = [
      "TChar($,MathShift)";
      "TChar(x,Letter)";
      "TChar(^,Superscript)";
      "TChar(2,Other)";
      "TChar( ,Space)";
      "TChar(+,Other)";
      "TChar( ,Space)";
      "TChar(y,Letter)";
      "TChar(_,Subscript)";
      "TChar(i,Letter)";
      "TChar($,MathShift)";
      "TEOF";
    ];
  };
  
  {
    name = "parameters";
    input = "\\newcommand{#1}{text}";
    expected_tokens = [
      "TMacro(newcommand)";
      "TGroupOpen";
      "TParam(1)";
      "TGroupClose";
      "TGroupOpen";
      "TChar(t,Letter)"; "TChar(e,Letter)"; "TChar(x,Letter)"; "TChar(t,Letter)";
      "TGroupClose";
      "TEOF";
    ];
  };
  
  {
    name = "comments";
    input = "before % comment\nafter";
    expected_tokens = [
      "TChar(b,Letter)"; "TChar(e,Letter)"; "TChar(f,Letter)"; 
      "TChar(o,Letter)"; "TChar(r,Letter)"; "TChar(e,Letter)";
      "TChar( ,Space)";
      (* comment chars are skipped *)
      "TChar(\n,EndLine)";
      "TChar(a,Letter)"; "TChar(f,Letter)"; "TChar(t,Letter)"; 
      "TChar(e,Letter)"; "TChar(r,Letter)";
      "TEOF";
    ];
  };
  
  {
    name = "alignment";
    input = "a & b \\\\ c & d";
    expected_tokens = [
      "TChar(a,Letter)";
      "TChar( ,Space)";
      "TChar(&,AlignTab)";
      "TChar( ,Space)";
      "TChar(b,Letter)";
      "TChar( ,Space)";
      "TMacro()";  (* \\ is a macro with empty name *)
      "TChar( ,Space)";
      "TChar(c,Letter)";
      "TChar( ,Space)";
      "TChar(&,AlignTab)";
      "TChar( ,Space)";
      "TChar(d,Letter)";
      "TEOF";
    ];
  };
  
  {
    name = "special_chars";
    input = "\\$ \\& \\% \\# \\_";
    expected_tokens = [
      "TMacro($)";   (* \$ as macro *)
      "TChar( ,Space)";
      "TMacro(&)";   (* \& as macro *)
      "TChar( ,Space)";
      "TMacro(%)";   (* \% as macro *)
      "TChar( ,Space)";
      "TMacro(#)";   (* \# as macro *)
      "TChar( ,Space)";
      "TMacro(_)";   (* \_ as macro *)
      "TEOF";
    ];
  };
]

(** Run a single golden test *)
let run_golden_test test_case =
  Printf.printf "Testing: %s\n" test_case.name;
  Printf.printf "  Input: %s\n" (String.escaped test_case.input);
  
  let tokens = lex_string test_case.input in
  let actual_tokens = List.map (fun tok -> token_to_string tok.token) tokens in
  
  Printf.printf "  Expected (%d): [%s]\n" 
    (List.length test_case.expected_tokens)
    (String.concat "; " test_case.expected_tokens);
  Printf.printf "  Actual   (%d): [%s]\n" 
    (List.length actual_tokens)
    (String.concat "; " actual_tokens);
  
  let matches = actual_tokens = test_case.expected_tokens in
  if matches then
    Printf.printf "  ✅ PASS\n"
  else begin
    Printf.printf "  ❌ FAIL\n";
    Printf.printf "  Differences:\n";
    
    let max_len = max (List.length test_case.expected_tokens) (List.length actual_tokens) in
    for i = 0 to max_len - 1 do
      let expected = try Some (List.nth test_case.expected_tokens i) with _ -> None in
      let actual = try Some (List.nth actual_tokens i) with _ -> None in
      match expected, actual with
      | Some e, Some a when e = a -> ()
      | Some e, Some a -> Printf.printf "    [%d] Expected: %s, Got: %s\n" i e a
      | Some e, None -> Printf.printf "    [%d] Expected: %s, Got: <missing>\n" i e
      | None, Some a -> Printf.printf "    [%d] Expected: <missing>, Got: %s\n" i a
      | None, None -> ()
    done
  end;
  Printf.printf "\n";
  matches

(** Run all golden tests *)
let run_all_golden_tests () =
  Printf.printf "=== Golden Output Tests (vs TeX behavior) ===\n\n";
  
  let passed = ref 0 in
  let total = List.length golden_test_cases in
  
  List.iter (fun test_case ->
    if run_golden_test test_case then
      incr passed
  ) golden_test_cases;
  
  Printf.printf "Results: %d/%d tests passed\n" !passed total;
  
  if !passed = total then begin
    Printf.printf "✅ All golden output tests passed!\n";
    Printf.printf "Lexer output matches expected TeX tokenization behavior.\n"
  end else begin
    Printf.printf "❌ Some golden output tests failed.\n";
    Printf.printf "Lexer behavior differs from TeX in %d cases.\n" (total - !passed)
  end;
  
  !passed = total

(** Create snapshot of current behavior for regression testing *)
let create_snapshot () =
  Printf.printf "Creating behavioral snapshot...\n";
  
  let snapshot_file = "test_snapshots.ml" in
  let oc = open_out snapshot_file in
  
  Printf.fprintf oc "(* Generated snapshot of lexer behavior - DO NOT EDIT *)\n\n";
  Printf.fprintf oc "let behavioral_snapshots = [\n";
  
  List.iteri (fun i test_case ->
    let tokens = lex_string test_case.input in
    let token_strings = List.map (fun tok -> token_to_string tok.token) tokens in
    
    Printf.fprintf oc "  (* %s *)\n" test_case.name;
    Printf.fprintf oc "  {\n";
    Printf.fprintf oc "    name = \"%s\";\n" test_case.name;
    Printf.fprintf oc "    input = %S;\n" test_case.input;
    Printf.fprintf oc "    tokens = [\n";
    List.iter (fun tok_str ->
      Printf.fprintf oc "      \"%s\";\n" tok_str
    ) token_strings;
    Printf.fprintf oc "    ];\n";
    Printf.fprintf oc "  }%s\n" (if i = List.length golden_test_cases - 1 then "" else ";");
  ) golden_test_cases;
  
  Printf.fprintf oc "]\n";
  close_out oc;
  
  Printf.printf "Snapshot saved to %s\n" snapshot_file;
  Printf.printf "Use this for regression testing in CI/CD\n\n"

let () =
  let success = run_all_golden_tests () in
  create_snapshot ();
  if not success then exit 1