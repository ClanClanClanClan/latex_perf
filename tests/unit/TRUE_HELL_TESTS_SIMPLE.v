Require Import String.
Require Import Ascii.
Require Import List.
Require Import Bool.
Import ListNotations.
Require Import LatexLexer.
Require Import ValidationTypes.
Require Import TypoRules.
Open Scope string_scope.

(** 🔥 TRUE HELL-LEVEL TESTS (SIMPLIFIED) 🔥 **)

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

(** ASCII double quote character **)
Definition dquote := String (ascii_of_nat 34) EmptyString.

(** Make string with quotes **)
Definition with_quotes (s : string) : string :=
  dquote ++ s ++ dquote.

(** === TYPO-001: STRAIGHT QUOTES DETECTION === **)

(** Test: TYPO-001 MUST detect straight quotes **)
Example test_typo_001_detects_quotes :
  let doc := make_test_doc (with_quotes "text") in
  let issues := typo_001_validator doc in
  match issues with
  | [] => False
  | issue :: _ => issue.(rule_id) = "TYPO-001"
  end.
Proof. vm_compute. reflexivity. Qed.

(** Test: Empty document produces no TYPO-001 issues **)
Example test_typo_001_empty :
  let doc := make_test_doc "" in
  typo_001_validator doc = [].
Proof. vm_compute. reflexivity. Qed.

(** Test: Text without quotes produces no TYPO-001 issues **)
Example test_typo_001_no_quotes :
  let doc := make_test_doc "text without quotes" in
  typo_001_validator doc = [].
Proof. vm_compute. reflexivity. Qed.

(** Test: Single quote character triggers TYPO-001 **)
Example test_typo_001_single_quote :
  let doc := make_test_doc dquote in
  let issues := typo_001_validator doc in
  length issues = 1.
Proof. vm_compute. reflexivity. Qed.

(** === ALL RULES: COMPREHENSIVE TESTING === **)

(** Test: Empty document with all rules produces structure errors **)
Example test_all_rules_empty :
  let doc := make_test_doc "" in
  let issues := execute_rules all_l0_rules doc in
  (* Empty document should trigger structure rules *)
  length issues >= 3.
Proof. vm_compute. reflexivity. Qed.

(** Test: Document with quotes triggers at least TYPO-001 **)
Example test_all_rules_quotes :
  let doc := make_test_doc (with_quotes "hello") in
  let issues := execute_rules all_l0_rules doc in
  exists issue, In issue issues /\ issue.(rule_id) = "TYPO-001".
Proof.
  vm_compute.
  exists {| rule_id := "TYPO-001";
            issue_severity := Error;
            message := "ASCII straight quotes must be curly quotes";
            loc := None;
            suggested_fix := Some "auto_replace";
            rule_owner := "@lint-team" |}.
  split; [left; reflexivity | reflexivity].
Qed.

(** === VALIDATOR PROPERTIES === **)

(** Test: Validators are deterministic **)
Example test_validator_deterministic :
  let doc := make_test_doc "test" in
  typo_001_validator doc = typo_001_validator doc.
Proof. reflexivity. Qed.

(** Test: Issue fields are properly set **)
Example test_issue_fields :
  let doc := make_test_doc dquote in
  match typo_001_validator doc with
  | issue :: _ => 
      issue.(issue_severity) = Error /\
      issue.(suggested_fix) = Some "auto_replace" /\
      issue.(rule_owner) = "@lint-team"
  | [] => False
  end.
Proof. vm_compute. split; [|split]; reflexivity. Qed.

(** === SOUNDNESS VERIFICATION === **)

(** Test: Soundness holds for actual detection **)
Example test_soundness_concrete :
  let doc := make_test_doc dquote in
  forall issue, In issue (typo_001_validator doc) ->
    exists tok, In tok doc.(tokens) /\
    match tok with
    | TText s => typo_001_check s = true
    | _ => False
    end.
Proof.
  intros issue H.
  apply (typo_001_soundness (make_test_doc dquote)); auto.
Qed.

(** === RULE STRUCTURE === **)

(** Test: All rules present **)
Example test_rule_count :
  length all_l0_rules = 75.
Proof. vm_compute. reflexivity. Qed.

(** Test: TYPO-001 rule structure **)
Example test_typo_001_structure :
  typo_001_rule.(id) = "TYPO-001" /\
  typo_001_rule.(default_severity) = Error /\
  typo_001_rule.(precondition) = L0_Lexer.
Proof. vm_compute. split; [|split]; reflexivity. Qed.

(** === EDGE CASES === **)

(** Test: Multiple quotes in same token **)
Example test_multiple_quotes :
  let multi_quotes := dquote ++ dquote ++ dquote in
  let doc := make_test_doc multi_quotes in
  let issues := typo_001_validator doc in
  length issues >= 1.
Proof. vm_compute. auto. Qed.

(** Test: Quote at different positions **)
Example test_quote_positions :
  let start := dquote ++ "text" in
  let middle := "te" ++ dquote ++ "xt" in
  let end_ := "text" ++ dquote in
  let doc1 := make_test_doc start in
  let doc2 := make_test_doc middle in
  let doc3 := make_test_doc end_ in
  (length (typo_001_validator doc1) > 0) /\
  (length (typo_001_validator doc2) > 0) /\
  (length (typo_001_validator doc3) > 0).
Proof. vm_compute. split; [|split]; reflexivity. Qed.