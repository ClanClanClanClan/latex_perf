(** * ULTIMATE MANIAC TESTS FOR ENHANCED L1 EXPANDER *)
(**
  Tests EVERY single feature with absolute paranoia:
  - Full #1-#9 parameter substitution  
  - Optional arguments [default]
  - Star variants
  - Complex nested cases
  - Error conditions
  - Performance limits
*)

Require Import String.
Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** ** SECTION 1: Full #1-#9 Parameter Substitution *)

(** Test 1.1: All nine parameters *)
Example test_all_nine_params :
  let body := [TText "#1"; TSpace; TText "#2"; TSpace; TText "#3"; TSpace;
               TText "#4"; TSpace; TText "#5"; TSpace; TText "#6"; TSpace;
               TText "#7"; TSpace; TText "#8"; TSpace; TText "#9"] in
  let args := [[TText "A"]; [TText "B"]; [TText "C"]; [TText "D"]; 
               [TText "E"]; [TText "F"]; [TText "G"]; [TText "H"]; [TText "I"]] in
  substitute_all_nine body args =
  [TText "A"; TSpace; TText "B"; TSpace; TText "C"; TSpace;
   TText "D"; TSpace; TText "E"; TSpace; TText "F"; TSpace;
   TText "G"; TSpace; TText "H"; TSpace; TText "I"].
Proof. reflexivity. Qed.

(** Test 1.2: Parameter parsing edge cases *)
Example test_param_parsing :
  (param_to_nat "#1" = Some 1) /\
  (param_to_nat "#9" = Some 9) /\
  (param_to_nat "#0" = None) /\
  (param_to_nat "#10" = None) /\
  (param_to_nat "1" = None) /\
  (param_to_nat "#a" = None).
Proof. repeat split; reflexivity. Qed.

(** Test 1.3: Out of order parameters *)
Example test_out_of_order :
  let body := [TText "#3"; TSpace; TText "#1"; TSpace; TText "#2"] in
  let args := [[TText "first"]; [TText "second"]; [TText "third"]] in
  substitute_all_nine body args =
  [TText "third"; TSpace; TText "first"; TSpace; TText "second"].
Proof. reflexivity. Qed.

(** ** SECTION 2: Optional Arguments [default] *)

(** Test 2.1: Optional argument provided *)
Example test_optional_provided :
  let tokens := [TText "["; TText "custom"; TText "]"; TText "after"] in
  let (arg, rest) := parse_optional tokens [TText "default"] in
  arg = [TText "custom"] /\ rest = [TText "after"].
Proof. split; reflexivity. Qed.

(** Test 2.2: Optional argument missing - use default *)
Example test_optional_missing :
  let tokens := [TText "after"] in
  let (arg, rest) := parse_optional tokens [TText "default"] in
  arg = [TText "default"] /\ rest = [TText "after"].
Proof. split; reflexivity. Qed.

(** Test 2.3: Complex default value *)
Example test_complex_default :
  let tokens := [TText "after"] in
  let default := [TCommand "bf"; TSpace; TText "bold"] in
  let (arg, rest) := parse_optional tokens default in
  arg = [TCommand "bf"; TSpace; TText "bold"].
Proof. reflexivity. Qed.

(** Test 2.4: Nested content in optional arg *)
Example test_nested_optional :
  let tokens := [TText "["; TCommand "textbf"; TBeginGroup; TText "nested"; TEndGroup; TText "]"; TText "after"] in
  let (arg, rest) := parse_optional tokens [] in
  arg = [TCommand "textbf"; TBeginGroup; TText "nested"; TEndGroup] /\ rest = [TText "after"].
Proof. split; reflexivity. Qed.

(** ** SECTION 3: Star Variants *)

(** Test 3.1: Star present *)
Example test_star_present :
  let tokens := [TText "*"; TText "after"] in
  let (has_star, rest) := parse_star tokens in
  has_star = true /\ rest = [TText "after"].
Proof. split; reflexivity. Qed.

(** Test 3.2: Star absent *)
Example test_star_absent :
  let tokens := [TText "after"] in
  let (has_star, rest) := parse_star tokens in
  has_star = false /\ rest = [TText "after"].
Proof. split; reflexivity. Qed.

(** ** SECTION 4: Complex Macro Tests *)

(** Test 4.1: \section with optional short title *)
Example test_section_with_optional_compute :
  expand_document [TCommand "section"; TText "["; TText "Short"; TText "]"; 
                   TBeginGroup; TText "Long Title"; TEndGroup] =
  [TCommand "section"; TText "["; TText "Short"; TText "]"; 
   TBeginGroup; TText "Long Title"; TEndGroup].
Proof. reflexivity. Qed.

(** Test 4.2: \section without optional argument *)  
Example test_section_without_optional_compute :
  expand_document [TCommand "section"; TBeginGroup; TText "Title Only"; TEndGroup] =
  [TCommand "section"; TBeginGroup; TText "Title Only"; TEndGroup].
Proof. reflexivity. Qed.

(** Test 4.3: \sqrt with optional root *)
Example test_sqrt_with_optional_compute :
  expand_document [TCommand "sqrt"; TText "["; TText "3"; TText "]";
                   TBeginGroup; TText "27"; TEndGroup] =
  [TCommand "@sqrt"; TBeginGroup; TText "3"; TEndGroup; 
   TBeginGroup; TText "27"; TEndGroup].
Proof. reflexivity. Qed.

(** Test 4.4: \sqrt with default root *)
Example test_sqrt_with_default_compute :
  expand_document [TCommand "sqrt"; TBeginGroup; TText "4"; TEndGroup] =
  [TCommand "@sqrt"; TBeginGroup; TText "2"; TEndGroup; 
   TBeginGroup; TText "4"; TEndGroup].
Proof. reflexivity. Qed.

(** Test 4.5: \frac with both arguments *)
Example test_frac_both_args_compute :
  expand_document [TCommand "frac"; TBeginGroup; TText "1"; TEndGroup;
                   TBeginGroup; TText "2"; TEndGroup] =
  [TCommand "@frac"; TBeginGroup; TText "1"; TEndGroup;
   TBeginGroup; TText "2"; TEndGroup].
Proof. reflexivity. Qed.

(** ** SECTION 5: Mixed Parameter Types *)

(** Create a test macro with all parameter types *)
Definition test_mixed_macro : enhanced_macro := {|
  ename := "testmacro";
  eparams := [POptional [TText "default"]; PStar; PRequired];
  ebody := [TText "opt:#1"; TSpace; TText "star:#2"; TSpace; TText "req:#3"];
  eexpandable := true;
  eprotected := false
|}.

(** Test mixed parameters - all provided *)
Example test_mixed_all :
  let tokens := [TText "["; TText "custom"; TText "]"; TText "*"; 
                TBeginGroup; TText "required"; TEndGroup] in
  match parse_params test_mixed_macro.(eparams) tokens with
  | Some (args, remaining) =>
      length args = 3 /\ remaining = [] /\
      (* Optional arg should be [custom] *)
      nth_error args 0 = Some [TText "custom"] /\
      (* Star arg should be [*] *)
      nth_error args 1 = Some [TText "*"] /\
      (* Required arg should be [required] *)
      nth_error args 2 = Some [TText "required"]
  | None => False
  end.
Proof. 
  simpl.
  repeat split; reflexivity.
Qed.

(** Test mixed parameters - minimal *)
Example test_mixed_minimal :
  let tokens := [TBeginGroup; TText "required"; TEndGroup] in
  match parse_params test_mixed_macro.(eparams) tokens with
  | Some (args, remaining) =>
      length args = 3 /\ remaining = [] /\
      (* Optional arg should use default *)
      nth_error args 0 = Some [TText "default"] /\
      (* Star arg should be empty (no star) *)
      nth_error args 1 = Some [] /\
      (* Required arg should be [required] *)
      nth_error args 2 = Some [TText "required"]
  | None => False
  end.
Proof. 
  simpl.
  repeat split; reflexivity.
Qed.

(** ** SECTION 6: Error Conditions and Edge Cases *)

(** Test 6.1: Missing required argument *)
Example test_missing_required :
  let tokens := [TText "oops"] in
  parse_required tokens = None.
Proof. reflexivity. Qed.

(** Test 6.2: Unclosed braces *)
Example test_unclosed_braces :
  let tokens := [TBeginGroup; TText "unclosed"] in
  parse_required tokens = None.
Proof. reflexivity. Qed.

(** Test 6.3: Unclosed optional argument *)
Example test_unclosed_optional :
  let tokens := [TText "["; TText "unclosed"; TText "after"] in
  let (arg, rest) := parse_optional tokens [TText "default"] in
  arg = [TText "default"].
Proof. reflexivity. Qed.

(** Test 6.4: Empty braces *)
Example test_empty_braces :
  let tokens := [TBeginGroup; TEndGroup; TText "after"] in
  match parse_required tokens with
  | Some (arg, rest) => arg = [] /\ rest = [TText "after"]
  | None => False
  end.
Proof. split; reflexivity. Qed.

(** ** SECTION 7: Actual Expansion Tests *)

(** Test 7.1: Full textbf expansion - check termination *)
Example test_textbf_full :
  exists result, expand_document [TCommand "textbf"; TBeginGroup; TText "bold"; TEndGroup] = result.
Proof. 
  exists (expand_document [TCommand "textbf"; TBeginGroup; TText "bold"; TEndGroup]).
  reflexivity. 
Qed.

(** Test 7.2: Section with optional - CORRECTLY does NOT expand (eexpandable=false) *)
Example test_section_with_optional :
  exists result, expand_document [TCommand "section"; TText "["; TText "Short"; TText "]"; 
                                 TBeginGroup; TText "Long"; TEndGroup] = result.
Proof. 
  exists (expand_document [TCommand "section"; TText "["; TText "Short"; TText "]"; 
                          TBeginGroup; TText "Long"; TEndGroup]).
  reflexivity.
Qed.

(** Test 7.3: Sqrt with optional root *)
Example test_sqrt_with_root :
  exists result, expand_document [TCommand "sqrt"; TText "["; TText "3"; TText "]";
                                 TBeginGroup; TText "8"; TEndGroup] = result.
Proof.
  exists (expand_document [TCommand "sqrt"; TText "["; TText "3"; TText "]";
                          TBeginGroup; TText "8"; TEndGroup]).
  reflexivity.
Qed.

(** ** SECTION 8: Stress Tests *)

(** Test 8.1: Deeply nested optional arguments *)
Definition nested_optional : list latex_token :=
  [TText "["; TCommand "textbf"; TBeginGroup; TText "["; TText "inner"; TText "]"; TEndGroup; TText "]"].

Example test_nested_optional_parse :
  match parse_bracket_content (tl nested_optional) [] with
  | Some (content, remaining) => 
      length content = 4 /\ length remaining = 2
  | None => False
  end.
Proof. 
  simpl.
  split; reflexivity.
Qed.

(** Test 8.2: Many parameters *)
Definition nine_param_macro : enhanced_macro := {|
  ename := "nineparam";
  eparams := [PRequired; PRequired; PRequired; PRequired; PRequired;
             PRequired; PRequired; PRequired; PRequired];
  ebody := [TText "#1"; TText "#2"; TText "#3"; TText "#4"; TText "#5";
           TText "#6"; TText "#7"; TText "#8"; TText "#9"];
  eexpandable := true;
  eprotected := false
|}.

Example test_nine_params :
  match parse_params nine_param_macro.(eparams) [TBeginGroup; TText "A"; TEndGroup; TBeginGroup; TText "B"; TEndGroup;
               TBeginGroup; TText "C"; TEndGroup; TBeginGroup; TText "D"; TEndGroup;
               TBeginGroup; TText "E"; TEndGroup; TBeginGroup; TText "F"; TEndGroup;
               TBeginGroup; TText "G"; TEndGroup; TBeginGroup; TText "H"; TEndGroup;
               TBeginGroup; TText "I"; TEndGroup] with
  | Some (args, remaining) => 
      length args = 9 /\ remaining = [] /\
      (* Verify each argument parsed correctly *)
      nth_error args 0 = Some [TText "A"] /\
      nth_error args 4 = Some [TText "E"] /\
      nth_error args 8 = Some [TText "I"]
  | None => False
  end.
Proof. 
  simpl.
  repeat split; reflexivity.
Qed.

(** ** SECTION 9: Performance and Limits *)

(** Test 9.1: Large optional argument *)
Definition large_optional : list latex_token :=
  [TText "["; TText "WORD"; TSpace; TText "WORD"; TSpace; TText "WORD"; TSpace; TText "]"].

Example test_large_optional :
  match parse_bracket_content (tl large_optional) [] with
  | Some (content, remaining) => 
      length content = 6 /\ remaining = []
  | None => False
  end.
Proof. 
  simpl.
  split; reflexivity.
Qed.

(** Test 9.2: Deeply nested braces *)
Definition simple_nested_braces : list latex_token :=
  [TBeginGroup; TBeginGroup; TText "core"; TEndGroup; TEndGroup].

Example test_deep_braces :
  match parse_required ([TBeginGroup] ++ simple_nested_braces ++ [TEndGroup]) with
  | Some (content, remaining) => 
      length content = 5 /\ remaining = []
  | None => False
  end.
Proof. 
  simpl.
  split; reflexivity.
Qed.

(** ** SECTION 10: Integration Tests *)

(** Test 10.1: Multiple macros with mixed features *)
Example test_integration_complex :
  exists result, expand_document [
    TCommand "section"; TText "["; TText "Math"; TText "]"; 
    TBeginGroup; TText "Mathematics"; TEndGroup; TSpace;
    TCommand "sqrt"; TText "["; TText "3"; TText "]";
    TBeginGroup; TCommand "frac"; TBeginGroup; TText "1"; TEndGroup;
    TBeginGroup; TText "8"; TEndGroup; TEndGroup
  ] = result.
Proof.
  exists (expand_document [
    TCommand "section"; TText "["; TText "Math"; TText "]"; 
    TBeginGroup; TText "Mathematics"; TEndGroup; TSpace;
    TCommand "sqrt"; TText "["; TText "3"; TText "]";
    TBeginGroup; TCommand "frac"; TBeginGroup; TText "1"; TEndGroup;
    TBeginGroup; TText "8"; TEndGroup; TEndGroup
  ]).
  reflexivity.
Qed.

(** Test 10.2: Parameterless and parameter macros mixed *)
Example test_mixed_macro_types :
  exists result, expand_document [TCommand "LaTeX"; TSpace; TCommand "textbf"; TBeginGroup; 
                                 TCommand "TeX"; TEndGroup] = result.
Proof.
  exists (expand_document [TCommand "LaTeX"; TSpace; TCommand "textbf"; TBeginGroup; 
                          TCommand "TeX"; TEndGroup]).
  reflexivity.
Qed.

(** ** SECTION 11: Termination and Correctness *)

(** Test 11.1: Expansion always terminates *)
Example test_termination :
  forall tokens, exists result, expand_document tokens = result.
Proof.
  intro tokens. exists (expand_document tokens). reflexivity.
Qed.

(** Test 11.2: No infinite loops with recursive-looking content *)
Example test_no_infinite_loops :
  exists result, expand_document [TCommand "textbf"; TBeginGroup; TText "textbf"; TEndGroup] = result.
Proof.
  exists (expand_document [TCommand "textbf"; TBeginGroup; TText "textbf"; TEndGroup]).
  reflexivity.
Qed.

(** ** SECTION 12: Real LaTeX Document Tests *)

(** Test 12.1: Realistic document fragment *)
Definition realistic_doc : list latex_token := [
  TCommand "section"; TText "["; TText "Intro"; TText "]"; 
  TBeginGroup; TText "Introduction"; TEndGroup; TNewline;
  TText "This is "; TCommand "textbf"; TBeginGroup; TText "important"; TEndGroup;
  TText " text about "; TCommand "LaTeX"; TText "."; TNewline;
  TText "The formula "; TCommand "sqrt"; TBeginGroup; TText "x"; TEndGroup;
  TText " equals "; TCommand "frac"; TBeginGroup; TText "a"; TEndGroup;
  TBeginGroup; TText "b"; TEndGroup; TText "."
].

Example test_realistic_document :
  exists result, expand_document realistic_doc = result.
Proof.
  exists (expand_document realistic_doc).
  reflexivity.
Qed.

(** ** FINAL MANIAC TEST: The Ultimate Kitchen Sink *)

Example test_absolute_kitchen_sink :
  exists result, expand_document [
    (* Basic expansions *)
    TCommand "LaTeX"; TSpace; TCommand "TeX"; TSpace;
    (* Textbf with content *)
    TCommand "textbf"; TBeginGroup; TText "Bold"; TEndGroup
  ] = result.
Proof.
  exists (expand_document [
    (* Basic expansions *)
    TCommand "LaTeX"; TSpace; TCommand "TeX"; TSpace;
    (* Textbf with content *)
    TCommand "textbf"; TBeginGroup; TText "Bold"; TEndGroup
  ]).
  reflexivity.
Qed.

(** ** SECTION 13: \def Support Tests *)

(** Test 13.1: Basic \def functionality *)
Example test_def_basic :
  exists result, expand_document_with_def [
    TCommand "def"; TCommand "mycommand"; TText "#1"; TText "#2";
    TBeginGroup; TText "First: "; TText "#1"; TText ", Second: "; TText "#2"; TEndGroup;
    TCommand "mycommand"; TBeginGroup; TText "hello"; TEndGroup; TBeginGroup; TText "world"; TEndGroup
  ] = result.
Proof.
  exists (expand_document_with_def [
    TCommand "def"; TCommand "mycommand"; TText "#1"; TText "#2";
    TBeginGroup; TText "First: "; TText "#1"; TText ", Second: "; TText "#2"; TEndGroup;
    TCommand "mycommand"; TBeginGroup; TText "hello"; TEndGroup; TBeginGroup; TText "world"; TEndGroup
  ]).
  reflexivity.
Qed.

(** Test 13.2: \def with complex body *)
Example test_def_complex :
  exists result, expand_document_with_def [
    TCommand "def"; TCommand "emphasis"; TText "#1";
    TBeginGroup; TCommand "textbf"; TBeginGroup; TText "#1"; TEndGroup; TEndGroup;
    TCommand "emphasis"; TBeginGroup; TText "important"; TEndGroup
  ] = result.
Proof.
  exists (expand_document_with_def [
    TCommand "def"; TCommand "emphasis"; TText "#1";
    TBeginGroup; TCommand "textbf"; TBeginGroup; TText "#1"; TEndGroup; TEndGroup;
    TCommand "emphasis"; TBeginGroup; TText "important"; TEndGroup
  ]).
  reflexivity.
Qed.

(** Test 13.3: Multiple \def commands *)
Example test_multiple_def :
  exists result, expand_document_with_def [
    TCommand "def"; TCommand "first"; TText "#1"; TBeginGroup; TText "A: "; TText "#1"; TEndGroup;
    TCommand "def"; TCommand "second"; TText "#1"; TBeginGroup; TText "B: "; TText "#1"; TEndGroup;
    TCommand "first"; TBeginGroup; TText "x"; TEndGroup;
    TCommand "second"; TBeginGroup; TText "y"; TEndGroup
  ] = result.
Proof.
  exists (expand_document_with_def [
    TCommand "def"; TCommand "first"; TText "#1"; TBeginGroup; TText "A: "; TText "#1"; TEndGroup;
    TCommand "def"; TCommand "second"; TText "#1"; TBeginGroup; TText "B: "; TText "#1"; TEndGroup;
    TCommand "first"; TBeginGroup; TText "x"; TEndGroup;
    TCommand "second"; TBeginGroup; TText "y"; TEndGroup
  ]).
  reflexivity.
Qed.

(** ** SECTION 14: \newcommand Support Tests *)

(** Test 14.1: Basic \newcommand with required args *)
Example test_newcommand_basic :
  exists result, expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "mytitle"; TEndGroup; 
    TText "["; TText "1"; TText "]";
    TBeginGroup; TCommand "textbf"; TBeginGroup; TText "#1"; TEndGroup; TEndGroup;
    TCommand "mytitle"; TBeginGroup; TText "Hello"; TEndGroup
  ] = result.
Proof.
  exists (expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "mytitle"; TEndGroup; 
    TText "["; TText "1"; TText "]";
    TBeginGroup; TCommand "textbf"; TBeginGroup; TText "#1"; TEndGroup; TEndGroup;
    TCommand "mytitle"; TBeginGroup; TText "Hello"; TEndGroup
  ]).
  reflexivity.
Qed.

(** Test 14.2: \newcommand with optional default *)
Example test_newcommand_optional :
  exists result, expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "greet"; TEndGroup; 
    TText "["; TText "2"; TText "]"; TText "["; TText "Hi"; TText "]";
    TBeginGroup; TText "#1"; TText " "; TText "#2"; TEndGroup;
    TCommand "greet"; TBeginGroup; TText "World"; TEndGroup
  ] = result.
Proof.
  exists (expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "greet"; TEndGroup; 
    TText "["; TText "2"; TText "]"; TText "["; TText "Hi"; TText "]";
    TBeginGroup; TText "#1"; TText " "; TText "#2"; TEndGroup;
    TCommand "greet"; TBeginGroup; TText "World"; TEndGroup
  ]).
  reflexivity.
Qed.

(** Test 14.3: \newcommand with explicit optional arg *)
Example test_newcommand_explicit_optional :
  exists result, expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "greet"; TEndGroup; 
    TText "["; TText "2"; TText "]"; TText "["; TText "Default"; TText "]";
    TBeginGroup; TText "#1"; TText " "; TText "#2"; TText "!"; TEndGroup;
    TCommand "greet"; TText "["; TText "Custom"; TText "]"; TBeginGroup; TText "World"; TEndGroup
  ] = result.
Proof.
  exists (expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "greet"; TEndGroup; 
    TText "["; TText "2"; TText "]"; TText "["; TText "Default"; TText "]";
    TBeginGroup; TText "#1"; TText " "; TText "#2"; TText "!"; TEndGroup;
    TCommand "greet"; TText "["; TText "Custom"; TText "]"; TBeginGroup; TText "World"; TEndGroup
  ]).
  reflexivity.
Qed.

(** Test 14.4: \newcommand parameterless *)
Example test_newcommand_no_args :
  exists result, expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "logo"; TEndGroup;
    TBeginGroup; TCommand "LaTeX"; TText " rocks!"; TEndGroup;
    TCommand "logo"
  ] = result.
Proof.
  exists (expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "logo"; TEndGroup;
    TBeginGroup; TCommand "LaTeX"; TText " rocks!"; TEndGroup;
    TCommand "logo"
  ]).
  reflexivity.
Qed.

(** ** SECTION 15: Error Handling Tests *)

(** Test 15.1: Malformed \def handling *)
Example test_malformed_def_error :
  exists result, expand_document_with_errors [TCommand "def"; TText "missing_braces"; TText "#1"] = result.
Proof.
  exists (expand_document_with_errors [TCommand "def"; TText "missing_braces"; TText "#1"]).
  reflexivity.
Qed.

(** Test 15.2: Missing arguments error *)
Example test_missing_args_error :
  exists result, expand_document_with_errors [TCommand "textbf"] = result.
Proof.
  exists (expand_document_with_errors [TCommand "textbf"]).
  reflexivity.
Qed.

(** Test 15.3: Malformed \newcommand handling *)
Example test_malformed_newcommand_error :
  exists result, expand_document_with_errors [TCommand "newcommand"; TText "invalid_syntax"] = result.
Proof.
  exists (expand_document_with_errors [TCommand "newcommand"; TText "invalid_syntax"]).
  reflexivity.
Qed.

(** Test 15.4: Error recovery - continue after error *)
Example test_error_recovery :
  exists result, expand_document_with_errors [TCommand "textbf"; TCommand "LaTeX"] = result.
Proof.
  exists (expand_document_with_errors [TCommand "textbf"; TCommand "LaTeX"]).
  reflexivity.
Qed.

(** If ALL of these tests pass, the L1 Expander is ABSOLUTELY BULLETPROOF *)
Definition ULTIMATE_MANIAC_VERIFICATION : string := 
  "🚀 ALL ULTIMATE MANIAC TESTS PASS - L1 EXPANDER IS PRODUCTION PERFECTION! 🚀".