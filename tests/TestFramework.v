(* LaTeX Perfectionist Test Framework *)
(* Provides common infrastructure for writing meaningful tests *)

From Coq Require Import String List Bool.
From Coq Require Import Ascii.
Import ListNotations.

(* Import the validation types *)
From LP Require Import ValidationResult RuleId BaseValidator.

(* Test result type *)
Inductive test_result : Type :=
  | Pass : test_result
  | Fail : string -> test_result.

(* Test case type *)
Record test_case : Type := {
  test_name : string;
  test_doc : string;
  expected_rules : list rule_id;
  test_description : string
}.

(* Helper to create test documents *)
Definition make_test_doc (content : string) : string := content.

(* Check if a specific rule was triggered *)
Definition rule_triggered (rule : rule_id) (results : list validation_result) : bool :=
  existsb (fun r => rule_id_eqb (result_rule r) rule) results.

(* Check if exactly the expected rules were triggered *)
Definition exact_rules_triggered (expected : list rule_id) 
                                (results : list validation_result) : bool :=
  let triggered := map result_rule results in
  andb (forallb (fun r => existsb (rule_id_eqb r) triggered) expected)
       (Nat.eqb (length triggered) (length expected)).

(* Test assertion helpers *)
Definition assert_detects (rule : rule_id) (doc : string) 
                         (validator : string -> list validation_result) : test_result :=
  let results := validator doc in
  if rule_triggered rule results
  then Pass
  else Fail ("Rule " ++ rule_id_to_string rule ++ " did not trigger").

Definition assert_no_issues (doc : string) 
                           (validator : string -> list validation_result) : test_result :=
  let results := validator doc in
  match results with
  | [] => Pass
  | _ => Fail ("Expected no issues, but found " ++ 
               string_of_nat (length results) ++ " issues")
  end.

Definition assert_exact_issues (expected : list rule_id) (doc : string)
                              (validator : string -> list validation_result) : test_result :=
  let results := validator doc in
  if exact_rules_triggered expected results
  then Pass
  else Fail "Did not get exactly the expected issues".

(* Test runner *)
Definition run_test (tc : test_case) 
                   (validator : string -> list validation_result) : test_result :=
  assert_exact_issues (expected_rules tc) (test_doc tc) validator.

(* Test suite type *)
Definition test_suite := list (test_case * (string -> list validation_result)).

(* Run a test suite *)
Definition run_test_suite (suite : test_suite) : list (string * test_result) :=
  map (fun test_pair => 
    let (tc, validator) := test_pair in
    (test_name tc, run_test tc validator)) suite.

(* Pretty printing for test results *)
Definition format_test_result (name : string) (result : test_result) : string :=
  match result with
  | Pass => "✓ " ++ name
  | Fail msg => "✗ " ++ name ++ ": " ++ msg
  end.

(* Summary statistics *)
Definition count_passes (results : list (string * test_result)) : nat :=
  length (filter (fun r => match snd r with Pass => true | _ => false end) results).

Definition count_failures (results : list (string * test_result)) : nat :=
  length (filter (fun r => match snd r with Fail _ => true | _ => false end) results).

(* Generate test report *)
Definition generate_test_report (results : list (string * test_result)) : string :=
  let passes := count_passes results in
  let failures := count_failures results in
  let total := length results in
  "Test Results: " ++ string_of_nat passes ++ "/" ++ string_of_nat total ++ " passed" ++ "
" ++
  String.concat "
" (map (fun r => format_test_result (fst r) (snd r)) results).

(* Example of a well-structured test *)
Example good_test_example : test_case := {|
  test_name := "TYPO-001 detects straight quotes";
  test_doc := make_test_doc "This has \"straight quotes\" in it";
  expected_rules := [TYPO_001];
  test_description := "Verifies that TYPO-001 correctly identifies straight quotes"
|}.

(* Performance test helpers *)
Definition time_validator (validator : string -> list validation_result) 
                         (doc : string) (iterations : nat) : nat :=
  (* In extraction, this would actually measure time *)
  (* For now, just run the validator *)
  let _ := validator doc in
  0.

(* Corpus test helpers *)
Definition test_on_corpus (validator : string -> list validation_result)
                         (corpus : list string) : list nat :=
  map (fun doc => length (validator doc)) corpus.

(* Property-based test helpers *)
Definition property_no_false_positives (validator : string -> list validation_result)
                                      (valid_docs : list string) : bool :=
  forallb (fun doc => 
    match validator doc with
    | [] => true
    | _ => false
    end) valid_docs.

Definition property_catches_all_violations (validator : string -> list validation_result)
                                          (rule : rule_id)
                                          (violating_docs : list string) : bool :=
  forallb (fun doc => rule_triggered rule (validator doc)) violating_docs.

(* Export for use in test files *)
Module TestFramework.
  Definition make_test_doc := make_test_doc.
  Definition rule_triggered := rule_triggered.
  Definition exact_rules_triggered := exact_rules_triggered.
  Definition assert_detects := assert_detects.
  Definition assert_no_issues := assert_no_issues.
  Definition assert_exact_issues := assert_exact_issues.
  Definition run_test := run_test.
  Definition run_test_suite := run_test_suite.
  Definition generate_test_report := generate_test_report.
End TestFramework.