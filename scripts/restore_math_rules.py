#!/usr/bin/env python3
"""
Script to restore and add MATH-001 through MATH-005 rules with proper soundness proofs.
"""

def get_math_rules_content():
    """Generate the complete MATH rules section."""
    return '''
(** ** MATH: Mathematical Rules - MATH-001 through MATH-005 *)

(** MATH-001: Mathematical expressions in text mode *)
Definition math_001_check (s : string) : bool :=
  orb (string_contains_substring s "x^2")
  (orb (string_contains_substring s "a_i")
  (orb (string_contains_substring s "=")
       (string_contains_substring s "alpha"))).

Definition math_001_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if math_001_check s then
            [{| rule_id := "MATH-001";
                issue_severity := Warning;
                message := "Mathematical expressions should be in math mode";
                loc := None;
                suggested_fix := Some "add_math_mode";
                rule_owner := "@math-rules" |}]
          else []
      | _ => []
      end) doc.(tokens).

(** ** MATH-001 Soundness Proof *)
Theorem math_001_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue (math_001_validator doc) ->
  (exists tok : latex_token, 
    In tok doc.(tokens) /\\
    match tok with
    | TText s => math_001_check s = true
    | _ => False
    end).
Proof.
  intros doc Hlayer issue Hin.
  unfold math_001_validator in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [tok [Htok_in Hissue_in]].
  exists tok. split. exact Htok_in.
  destruct tok; simpl in Hissue_in.
  - (* TCommand case *) 
    contradiction.
  - (* TBeginGroup case *)
    contradiction.
  - (* TEndGroup case *)
    contradiction.
  - (* TMathShift case *)
    contradiction.
  - (* TAlignment case *)
    contradiction.
  - (* TParameter case *)
    contradiction.
  - (* TSuperscript case *)
    contradiction.
  - (* TSubscript case *)
    contradiction.
  - (* TText case *)
    destruct (math_001_check s) eqn:Hcheck.
    + reflexivity.
    + contradiction.
  - (* TSpace case *)
    contradiction.
  - (* TComment case *)
    contradiction.
  - (* TNewline case *)
    contradiction.
  - (* TEOF case *)
    contradiction.
Qed.

Definition math_001_rule : validation_rule := {|
  id := "MATH-001";
  description := "Mathematical expressions should be in math mode";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@math-rules";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "add_math_mode";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_001_validator;
  rule_sound := Some (ProofRef "math_001_soundness")
|}.

(** MATH-002: Unmatched math delimiters *)
Fixpoint math_002_count_delimiters (tokens : list latex_token) (count : nat) : bool :=
  match tokens with
  | [] => negb (Nat.eqb count 0)  (* True if unmatched *)
  | TMathShift :: rest =>
      math_002_count_delimiters rest (if Nat.eqb count 0 then 1 else 0)
  | _ :: rest => math_002_count_delimiters rest count
  end.

Definition math_002_validator : document_state -> list validation_issue :=
  fun doc =>
    if math_002_count_delimiters doc.(tokens) 0 then
      [{| rule_id := "MATH-002";
          issue_severity := Error;
          message := "Unmatched math delimiters $ detected";
          loc := None;
          suggested_fix := Some "fix_math_delimiters";
          rule_owner := "@math-rules" |}]
    else [].

(** ** MATH-002 Soundness Proof *)
Theorem math_002_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue (math_002_validator doc) ->
  math_002_count_delimiters doc.(tokens) 0 = true.
Proof.
  intros doc Hlayer issue Hin.
  unfold math_002_validator in Hin.
  destruct (math_002_count_delimiters doc.(tokens) 0) eqn:Hcheck.
  - reflexivity.
  - simpl in Hin. contradiction.
Qed.

Definition math_002_rule : validation_rule := {|
  id := "MATH-002";
  description := "Unmatched math delimiters $ detected";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@math-rules";
  performance_bucket := TokenKind_Mixed;
  auto_fix := Some "fix_math_delimiters";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_002_validator;
  rule_sound := Some (ProofRef "math_002_soundness")
|}.

(** MATH-003: Double dollar signs deprecated *)
Definition math_003_check (s : string) : bool :=
  string_contains_substring s "$$".

Definition math_003_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if math_003_check s then
            [{| rule_id := "MATH-003";
                issue_severity := Warning;
                message := "Double dollar $$ deprecated, use \\\\[ \\\\] instead";
                loc := None;
                suggested_fix := Some "replace_display_math";
                rule_owner := "@math-rules" |}]
          else []
      | _ => []
      end) doc.(tokens).

(** ** MATH-003 Soundness Proof *)
Theorem math_003_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue (math_003_validator doc) ->
  (exists tok : latex_token, 
    In tok doc.(tokens) /\\
    match tok with
    | TText s => math_003_check s = true
    | _ => False
    end).
Proof.
  intros doc Hlayer issue Hin.
  unfold math_003_validator in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [tok [Htok_in Hissue_in]].
  exists tok. split. exact Htok_in.
  destruct tok; simpl in Hissue_in.
  - (* TCommand case *) 
    contradiction.
  - (* TBeginGroup case *)
    contradiction.
  - (* TEndGroup case *)
    contradiction.
  - (* TMathShift case *)
    contradiction.
  - (* TAlignment case *)
    contradiction.
  - (* TParameter case *)
    contradiction.
  - (* TSuperscript case *)
    contradiction.
  - (* TSubscript case *)
    contradiction.
  - (* TText case *)
    destruct (math_003_check s) eqn:Hcheck.
    + reflexivity.
    + contradiction.
  - (* TSpace case *)
    contradiction.
  - (* TComment case *)
    contradiction.
  - (* TNewline case *)
    contradiction.
  - (* TEOF case *)
    contradiction.
Qed.

Definition math_003_rule : validation_rule := {|
  id := "MATH-003";
  description := "Double dollar $$ deprecated, use \\\\[ \\\\] instead";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@math-rules";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "replace_display_math";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_003_validator;
  rule_sound := Some (ProofRef "math_003_soundness")
|}.

(** MATH-004: Math symbols in text mode *)
Definition math_004_check (s : string) : bool :=
  orb (string_contains_substring s "∑")
  (orb (string_contains_substring s "∫")
  (orb (string_contains_substring s "≤")
  (orb (string_contains_substring s "≥")
       (string_contains_substring s "±")))).

Definition math_004_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if math_004_check s then
            [{| rule_id := "MATH-004";
                issue_severity := Warning;
                message := "Unicode math symbols should use LaTeX commands";
                loc := None;
                suggested_fix := Some "convert_math_symbols";
                rule_owner := "@math-rules" |}]
          else []
      | _ => []
      end) doc.(tokens).

(** ** MATH-004 Soundness Proof *)
Theorem math_004_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue (math_004_validator doc) ->
  (exists tok : latex_token, 
    In tok doc.(tokens) /\\
    match tok with
    | TText s => math_004_check s = true
    | _ => False
    end).
Proof.
  intros doc Hlayer issue Hin.
  unfold math_004_validator in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [tok [Htok_in Hissue_in]].
  exists tok. split. exact Htok_in.
  destruct tok; simpl in Hissue_in.
  - (* TCommand case *) 
    contradiction.
  - (* TBeginGroup case *)
    contradiction.
  - (* TEndGroup case *)
    contradiction.
  - (* TMathShift case *)
    contradiction.
  - (* TAlignment case *)
    contradiction.
  - (* TParameter case *)
    contradiction.
  - (* TSuperscript case *)
    contradiction.
  - (* TSubscript case *)
    contradiction.
  - (* TText case *)
    destruct (math_004_check s) eqn:Hcheck.
    + reflexivity.
    + contradiction.
  - (* TSpace case *)
    contradiction.
  - (* TComment case *)
    contradiction.
  - (* TNewline case *)
    contradiction.
  - (* TEOF case *)
    contradiction.
Qed.

Definition math_004_rule : validation_rule := {|
  id := "MATH-004";
  description := "Unicode math symbols should use LaTeX commands";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@math-rules";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "convert_math_symbols";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_004_validator;
  rule_sound := Some (ProofRef "math_004_soundness")
|}.

(** MATH-005: Inline math spacing *)
Definition math_005_check (s : string) : bool :=
  orb (string_contains_substring s " $")
  (string_contains_substring s "$ ").

Definition math_005_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if math_005_check s then
            [{| rule_id := "MATH-005";
                issue_severity := Info;
                message := "Math mode spacing may need adjustment";
                loc := None;
                suggested_fix := Some "adjust_math_spacing";
                rule_owner := "@math-rules" |}]
          else []
      | _ => []
      end) doc.(tokens).

(** ** MATH-005 Soundness Proof *)
Theorem math_005_soundness : 
  forall doc : document_state,
  doc.(doc_layer) = L0_Lexer ->
  forall issue : validation_issue,
  In issue (math_005_validator doc) ->
  (exists tok : latex_token, 
    In tok doc.(tokens) /\\
    match tok with
    | TText s => math_005_check s = true
    | _ => False
    end).
Proof.
  intros doc Hlayer issue Hin.
  unfold math_005_validator in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [tok [Htok_in Hissue_in]].
  exists tok. split. exact Htok_in.
  destruct tok; simpl in Hissue_in.
  - (* TCommand case *) 
    contradiction.
  - (* TBeginGroup case *)
    contradiction.
  - (* TEndGroup case *)
    contradiction.
  - (* TMathShift case *)
    contradiction.
  - (* TAlignment case *)
    contradiction.
  - (* TParameter case *)
    contradiction.
  - (* TSuperscript case *)
    contradiction.
  - (* TSubscript case *)
    contradiction.
  - (* TText case *)
    destruct (math_005_check s) eqn:Hcheck.
    + reflexivity.
    + contradiction.
  - (* TSpace case *)
    contradiction.
  - (* TComment case *)
    contradiction.
  - (* TNewline case *)
    contradiction.
  - (* TEOF case *)
    contradiction.
Qed.

Definition math_005_rule : validation_rule := {|
  id := "MATH-005";
  description := "Math mode spacing may need adjustment";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@math-rules";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "adjust_math_spacing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_005_validator;
  rule_sound := Some (ProofRef "math_005_soundness")
|}.

(** ** Multi-category implementation status *)
(** Phase 1 Progress: 40 L0_Lexer rules across 4 categories (TYPO, ENC, CHAR, MATH) *)
(** Demonstrates scalable cross-category pattern: 0 axioms, 0 admits maintained **)
'''

def restore_math_rules():
    """Append MATH rules to the TypoRules.v file."""
    filename = "src/rules/phase1/TypoRules.v"
    
    with open(filename, 'a') as f:
        f.write(get_math_rules_content())
    
    print("MATH rules restored successfully!")

if __name__ == "__main__":
    restore_math_rules()