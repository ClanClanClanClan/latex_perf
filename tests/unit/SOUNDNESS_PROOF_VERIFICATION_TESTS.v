Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ValidationTypes.
Require Import TypoRules.
Open Scope string_scope.

(** 🔥 SOUNDNESS PROOF VERIFICATION TESTS 🔥 **)
(** SYSTEMATIC VERIFICATION OF RULE SOUNDNESS PROOFS **)

(** === HELPER FUNCTIONS === **)

(** Create a standard test document **)
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

(** === TYPO SOUNDNESS PROOF VERIFICATION === **)

(** Test TYPO-001 soundness proof by applying it **)
Example test_typo_001_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := typo_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => typo_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply typo_001_soundness; auto.
Qed.

(** Test TYPO-002 soundness proof by applying it **)
Example test_typo_002_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := typo_002_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => typo_002_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply typo_002_soundness; auto.
Qed.

(** Test TYPO-003 soundness proof by applying it **)
Example test_typo_003_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := typo_003_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => typo_003_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply typo_003_soundness; auto.
Qed.

(** === ENC SOUNDNESS PROOF VERIFICATION === **)

(** Test ENC-001 soundness proof by applying it **)
Example test_enc_001_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := enc_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => enc_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply enc_001_soundness; auto.
Qed.

(** Test ENC-002 soundness proof by applying it **)
Example test_enc_002_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := enc_002_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => enc_002_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply enc_002_soundness; auto.
Qed.

(** === CHAR SOUNDNESS PROOF VERIFICATION === **)

(** Test CHAR-001 soundness proof by applying it **)
Example test_char_001_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := char_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => char_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply char_001_soundness; auto.
Qed.

(** === MATH SOUNDNESS PROOF VERIFICATION === **)

(** Test MATH-001 soundness proof by applying it **)
Example test_math_001_soundness_application : 
  let doc := make_test_doc "$x$" in
  let issues := math_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => math_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply math_001_soundness; auto.
Qed.

(** === ENV SOUNDNESS PROOF VERIFICATION === **)

(** Test ENV-001 soundness proof by applying it **)
Example test_env_001_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := env_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => env_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply env_001_soundness; auto.
Qed.

(** === STRUCT SOUNDNESS PROOF VERIFICATION === **)

(** Test STRUCT-001 soundness proof by applying it **)
Example test_struct_001_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := struct_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => struct_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply struct_001_soundness; auto.
Qed.

(** === REF SOUNDNESS PROOF VERIFICATION === **)

(** Test REF-001 soundness proof by applying it **)
Example test_ref_001_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := ref_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => ref_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply ref_001_soundness; auto.
Qed.

(** === STYLE SOUNDNESS PROOF VERIFICATION === **)

(** Test STYLE-001 soundness proof by applying it **)
Example test_style_001_soundness_application : 
  let doc := make_test_doc "hello world" in
  let issues := style_001_validator doc in
  (* For every issue, the soundness proof should hold *)
  forall issue, In issue issues -> 
    exists tok, In tok doc.(tokens) /\ 
    match tok with
    | TText s => style_001_check s = true
    | _ => False
    end.
Proof. 
  intros issue Hin.
  (* Apply the soundness theorem *)
  apply style_001_soundness; auto.
Qed.

(** === COUNTEREXAMPLE TESTING === **)

(** Test that soundness proofs reject invalid counterexamples **)
Example test_soundness_counterexample_rejection : 
  let doc := make_test_doc "hello world" in
  let issues := typo_001_validator doc in
  (* If we claim an issue exists but it doesn't, soundness should fail *)
  ~ (In {| rule_id := "FAKE-001"; issue_severity := Error; message := "Fake"; 
           loc := None; suggested_fix := None; rule_owner := "fake" |} issues).
Proof. 
  intro H.
  (* This should be impossible to prove, demonstrating soundness *)
  unfold typo_001_validator in H.
  (* The fake issue shouldn't be in the real validator output *)
  simpl in H.
  contradiction.
Qed.

(** Test that validators are decidable **)
Example test_validator_decidability : 
  forall doc, 
    (exists issue, In issue (typo_001_validator doc)) \/ 
    (forall issue, ~ In issue (typo_001_validator doc)).
Proof. 
  intro doc.
  (* Since the validator produces a concrete list, this is decidable *)
  destruct (typo_001_validator doc) as [|issue rest].
  - right. intros issue' H. inversion H.
  - left. exists issue. left. reflexivity.
Qed.

(** Test that soundness proofs are consistent **)
Example test_soundness_consistency : 
  let doc := make_test_doc "hello world" in
  let issues := typo_001_validator doc in
  (* If an issue is found, the check function must return true for some token *)
  (issues <> []) -> 
  (exists tok, In tok doc.(tokens) /\ 
   match tok with
   | TText s => typo_001_check s = true
   | _ => False
   end).
Proof. 
  intro H.
  (* Use the soundness theorem *)
  destruct issues as [|issue rest].
  - contradiction.
  - apply typo_001_soundness; auto.
    left. reflexivity.
Qed.