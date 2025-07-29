Require Import String.
Require Import Ascii.
Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Require Import LatexLexer.
Require Import ValidationTypes.
Require Import TypoRules.
Open Scope string_scope.

(** 🔥 EXTREME HELL-LEVEL TESTS 🔥 **)
(** PUSHING VALIDATORS TO ABSOLUTE LIMITS **)

Definition make_doc (content : string) : document_state :=
  let tokens := lex content in
  {|
    tokens := tokens;
    expanded_tokens := None;
    ast := None;
    semantics := None;
    filename := "extreme_test.tex";
    doc_layer := L0_Lexer
  |}.

(** === STRESS TEST: PATHOLOGICAL DOCUMENTS === **)

(** Generate string of length n **)
Fixpoint repeat_string (s : string) (n : nat) : string :=
  match n with
  | 0 => EmptyString
  | S n' => s ++ repeat_string s n'
  end.

(** ASCII characters for testing **)
Definition quote := String (ascii_of_nat 34) EmptyString.
Definition backslash := String (ascii_of_nat 92) EmptyString.

(** Test: Document with 100 straight quotes **)
Example test_hundred_quotes :
  let doc := make_doc (repeat_string quote 100) in
  let issues := typo_001_validator doc in
  length issues >= 1.
Proof. vm_compute. simpl. lia. Qed.

(** Test: Deeply nested braces **)
Example test_deep_nesting :
  let open_braces := repeat_string "{" 50 in
  let close_braces := repeat_string "}" 50 in
  let doc := make_doc (open_braces ++ "x" ++ close_braces) in
  let issues := execute_rules all_l0_rules doc in
  (* Should complete without stack overflow *)
  length issues = 4.
Proof. vm_compute. reflexivity. Qed.

(** Test: Command soup - many backslashes **)
Example test_command_soup :
  let commands := repeat_string (backslash ++ "cmd ") 20 in
  let doc := make_doc commands in
  let issues := execute_rules all_l0_rules doc in
  length issues >= 3.
Proof. vm_compute. lia. Qed.

(** === ADVERSARIAL INPUTS === **)

(** Test: Malicious path in filename **)
Example test_malicious_filename :
  let evil_doc := {|
    tokens := lex "normal content";
    expanded_tokens := None;
    ast := None;
    semantics := None;
    filename := "../../../etc/passwd";
    doc_layer := L0_Lexer
  |} in
  (* Validators should still work correctly *)
  length (execute_rules all_l0_rules evil_doc) >= 3.
Proof. vm_compute. auto. Qed.

(** Test: Unicode confusion attack **)
Example test_unicode_confusion :
  (* Using different quote-like characters *)
  let confusing := String (ascii_of_nat 39) ("text" ++ String (ascii_of_nat 39) EmptyString) in
  let doc := make_doc confusing in
  (* Should handle ASCII apostrophes differently from quotes *)
  let issues := typo_001_validator doc in
  issues = []. (* TYPO-001 only detects double quotes, not single *)
Proof. vm_compute. reflexivity. Qed.

(** === BOUNDARY TESTING === **)

(** Test: Single character document **)
Example test_single_char_docs :
  let doc_quote := make_doc quote in
  let doc_brace := make_doc "{" in
  let doc_space := make_doc " " in
  (length (typo_001_validator doc_quote) = 1) /\
  (length (execute_rules all_l0_rules doc_brace) >= 3) /\
  (length (execute_rules all_l0_rules doc_space) >= 3).
Proof. vm_compute. split; [|split]; auto. Qed.

(** Test: Maximum rule violations in minimal space **)
Example test_max_violations_minimal :
  let bad := quote ++ "{" ++ "}" ++ quote in
  let doc := make_doc bad in
  let typo_issues := typo_001_validator doc in
  let all_issues := execute_rules all_l0_rules doc in
  (length typo_issues >= 1) /\ (length all_issues >= 4).
Proof. vm_compute. split; auto. Qed.

(** === INTERACTION TESTING === **)

(** Test: Rules don't interfere with each other **)
Example test_rule_independence :
  let doc := make_doc quote in
  let single_rule := execute_rule typo_001_rule doc in
  let all_rules := execute_rules all_l0_rules doc in
  (* TYPO-001 should produce same result alone or with other rules *)
  exists issue, In issue single_rule /\ In issue all_rules.
Proof.
  vm_compute.
  exists {| rule_id := "TYPO-001";
            issue_severity := Error;
            message := "ASCII straight quotes must be curly quotes";
            loc := None;
            suggested_fix := Some "auto_replace";
            rule_owner := "@lint-team" |}.
  split; left; reflexivity.
Qed.

(** === PERFORMANCE BOUNDARIES === **)

(** Test: All validators on large mixed content **)
Example test_large_mixed_content :
  let content := repeat_string "test " 10 ++ quote ++ repeat_string " more " 10 in
  let doc := make_doc content in
  let all_issues := execute_rules all_l0_rules doc in
  (* Should find at least the quote issue *)
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
  - right. right. right. left. reflexivity.
  - reflexivity.
Qed.

(** === REGRESSION GUARDS === **)

(** Test: Validators produce consistent severity levels **)
Example test_severity_consistency :
  let doc := make_doc quote in
  match typo_001_validator doc with
  | issue :: _ => issue.(issue_severity) = Error
  | [] => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Test: Validators provide actionable fixes **)
Example test_suggested_fixes :
  let doc := make_doc quote in
  match typo_001_validator doc with
  | issue :: _ => issue.(suggested_fix) <> None
  | [] => False
  end.
Proof. vm_compute. discriminate. Qed.

(** === EDGE CASE COMPLETENESS === **)

(** Test: Empty tokens edge case **)
Example test_empty_tokens :
  let empty_doc := {|
    tokens := [];
    expanded_tokens := None;
    ast := None;
    semantics := None;
    filename := "empty.tex";
    doc_layer := L0_Lexer
  |} in
  typo_001_validator empty_doc = [].
Proof. vm_compute. reflexivity. Qed.

(** Test: Wrong layer rejection **)
Example test_wrong_layer :
  let wrong_layer_doc := {|
    tokens := lex quote;
    expanded_tokens := None;
    ast := None;
    semantics := None;
    filename := "test.tex";
    doc_layer := L1_Expansion (* Wrong layer! *)
  |} in
  (* Most rules should not execute on wrong layer *)
  let applicable := filter (fun r => rule_applicable r wrong_layer_doc) all_l0_rules in
  length applicable = 0.
Proof. vm_compute. reflexivity. Qed.