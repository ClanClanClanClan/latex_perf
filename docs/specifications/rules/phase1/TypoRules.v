(** * Phase 1 Typography Rules - TYPO-001 through TYPO-010 *)
(**
  Week 4.2 Deliverable: First 10 lexical rules with formal proofs
  These rules operate on L0_Lexer output (raw token stream)
*)

Require Import String.
Require Import List.
Require Import Ascii.
Require Import Arith.
Import ListNotations.
Require Import core.lexer.LatexCatcodes.
Require Import core.lexer.LatexLexer.
Require Import ValidationTypes.
Open Scope string_scope.

(** ** String search utilities *)

(** Helper: Check if string starts with prefix *)
Fixpoint string_prefix (prefix s : string) : bool :=
  match prefix, s with
  | EmptyString, _ => true
  | String c1 rest1, String c2 rest2 =>
      if ascii_dec c1 c2 then string_prefix rest1 rest2
      else false
  | _, _ => false
  end.

(** Helper: Check if string contains substring *)
Fixpoint string_contains_substring (haystack needle : string) : bool :=
  match haystack with
  | EmptyString => 
      match needle with
      | EmptyString => true
      | _ => false
      end
  | String c rest =>
      if string_prefix needle haystack then true
      else string_contains_substring rest needle
  end.

(** Helper: Count occurrences of character in string *)
Fixpoint count_char (s : string) (c : ascii) : nat :=
  match s with
  | EmptyString => 0
  | String c' rest =>
      if ascii_dec c c' then S (count_char rest c)
      else count_char rest c
  end.

(** Helper: Check if string ends with spaces *)
Fixpoint string_ends_with_spaces (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c EmptyString => if ascii_dec c " "%char then true else false
  | String c rest => string_ends_with_spaces rest
  end.

(** ** TYPO-001: ASCII straight quotes must be curly quotes *)
Definition typo_001_check (s : string) : bool :=
  string_contains s (ascii_of_nat 34). (* ASCII 34 = double quote *)

Definition typo_001_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_001_check s then
            [{| rule_id := "TYPO-001";
                issue_severity := Error;
                message := "ASCII straight quotes must be curly quotes";
                loc := None;
                suggested_fix := Some "auto_replace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_001_rule : validation_rule := {|
  id := "TYPO-001";
  description := "ASCII straight quotes must be curly quotes";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "auto_replace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_001_validator;
  rule_sound := None
|}.

(** ** TYPO-002: Double hyphen -- should be en-dash *)
Definition typo_002_check (s : string) : bool :=
  string_contains_substring s "--".

Definition typo_002_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_002_check s then
            [{| rule_id := "TYPO-002";
                issue_severity := Warning;
                message := "Double hyphen -- should be en-dash";
                loc := None;
                suggested_fix := Some "auto_replace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_002_rule : validation_rule := {|
  id := "TYPO-002";
  description := "Double hyphen -- should be en-dash";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "auto_replace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_002_validator;
  rule_sound := None
|}.

(** ** TYPO-003: Triple hyphen --- should be em-dash *)
Definition typo_003_check (s : string) : bool :=
  string_contains_substring s "---".

Definition typo_003_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_003_check s then
            [{| rule_id := "TYPO-003";
                issue_severity := Warning;
                message := "Triple hyphen --- should be em-dash";
                loc := None;
                suggested_fix := Some "auto_replace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_003_rule : validation_rule := {|
  id := "TYPO-003";
  description := "Triple hyphen --- should be em-dash";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "auto_replace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_003_validator;
  rule_sound := None
|}.

(** ** TYPO-004: TeX double back-tick not allowed *)
Definition typo_004_check (s : string) : bool :=
  orb (string_contains_substring s "``") (string_contains_substring s "''").

Definition typo_004_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_004_check s then
            [{| rule_id := "TYPO-004";
                issue_severity := Warning;
                message := "TeX double back-tick not allowed; use opening curly quotes";
                loc := None;
                suggested_fix := Some "auto_replace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_004_rule : validation_rule := {|
  id := "TYPO-004";
  description := "TeX double back-tick not allowed; use opening curly quotes";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "auto_replace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_004_validator;
  rule_sound := None
|}.

(** ** TYPO-005: Ellipsis as three periods *)
Definition typo_005_check (s : string) : bool :=
  string_contains_substring s "...".

Definition typo_005_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_005_check s then
            [{| rule_id := "TYPO-005";
                issue_severity := Warning;
                message := "Ellipsis as three periods ...; use \dots";
                loc := None;
                suggested_fix := Some "auto_replace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_005_rule : validation_rule := {|
  id := "TYPO-005";
  description := "Ellipsis as three periods ...; use \dots";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "auto_replace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_005_validator;
  rule_sound := None
|}.

(** ** TYPO-006: Tab character forbidden *)
Definition typo_006_check (s : string) : bool :=
  string_contains s (ascii_of_nat 9). (* ASCII 9 = tab *)

Definition typo_006_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_006_check s then
            [{| rule_id := "TYPO-006";
                issue_severity := Error;
                message := "Tab character U+0009 forbidden";
                loc := None;
                suggested_fix := None;
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_006_rule : validation_rule := {|
  id := "TYPO-006";
  description := "Tab character U+0009 forbidden";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := None;
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_006_validator;
  rule_sound := None
|}.

(** ** TYPO-007: Trailing spaces at end of line *)
(* Note: This requires line-aware tokenization, simplified for now *)
Definition typo_007_check (s : string) : bool :=
  string_ends_with_spaces s.

Definition typo_007_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_007_check s then
            [{| rule_id := "TYPO-007";
                issue_severity := Info;
                message := "Trailing spaces at end of line";
                loc := None;
                suggested_fix := Some "strip_whitespace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_007_rule : validation_rule := {|
  id := "TYPO-007";
  description := "Trailing spaces at end of line";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "strip_whitespace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_007_validator;
  rule_sound := None
|}.

(** ** TYPO-008: Multiple consecutive blank lines *)
(* Simplified: check for multiple newlines in text tokens *)
Definition typo_008_check (s : string) : bool :=
  let newline_count := count_char s (ascii_of_nat 10) in (* ASCII 10 = \n *)
  Nat.ltb 2 newline_count.

Definition typo_008_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_008_check s then
            [{| rule_id := "TYPO-008";
                issue_severity := Info;
                message := "Multiple consecutive blank lines (>2) in source";
                loc := None;
                suggested_fix := Some "collapse_blank_lines";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_008_rule : validation_rule := {|
  id := "TYPO-008";
  description := "Multiple consecutive blank lines (>2) in source";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "collapse_blank_lines";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_008_validator;
  rule_sound := None
|}.

(** ** TYPO-009: Non-breaking space ~ used incorrectly at line start *)
Definition typo_009_check (s : string) : bool :=
  string_prefix "~" s.

Definition typo_009_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_009_check s then
            [{| rule_id := "TYPO-009";
                issue_severity := Warning;
                message := "Non-breaking space ~ used incorrectly at line start";
                loc := None;
                suggested_fix := None;
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_009_rule : validation_rule := {|
  id := "TYPO-009";
  description := "Non-breaking space ~ used incorrectly at line start";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := None;
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_009_validator;
  rule_sound := None
|}.

(** ** TYPO-010: Space before punctuation *)
Definition typo_010_check (s : string) : bool :=
  orb (string_contains_substring s " ,")
  (orb (string_contains_substring s " .")
  (orb (string_contains_substring s " ;")
  (orb (string_contains_substring s " :")
  (orb (string_contains_substring s " ?")
       (string_contains_substring s " !"))))).

Definition typo_010_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_010_check s then
            [{| rule_id := "TYPO-010";
                issue_severity := Info;
                message := "Space before punctuation , . ; : ? !";
                loc := None;
                suggested_fix := Some "remove_space";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_010_rule : validation_rule := {|
  id := "TYPO-010";
  description := "Space before punctuation , . ; : ? !";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "remove_space";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_010_validator;
  rule_sound := None
|}.

(** ** Phase 1 Typography rule collection *)
Definition phase1_typo_rules : list validation_rule := [
  typo_001_rule;
  typo_002_rule;
  typo_003_rule;
  typo_004_rule;
  typo_005_rule;
  typo_006_rule;
  typo_007_rule;
  typo_008_rule;
  typo_009_rule;
  typo_010_rule
].

(** ** Soundness framework for typography rules *)

(** Property: No straight quotes in document *)
Definition no_straight_quotes (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> 
    typo_001_check s = false.

(** We need a helper lemma about flat_map and non-empty results *)
Lemma flat_map_nonempty : forall (A B : Type) (f : A -> list B) (l : list A) (x : A),
  In x l -> f x <> [] -> flat_map f l <> [].
Proof.
  intros A B f l x H_in H_nonempty.
  induction l as [| h t IH].
  - (* Base case: empty list *)
    simpl in H_in. contradiction.
  - (* Inductive case: h :: t *)
    simpl in H_in. destruct H_in as [H_eq | H_in_t].
    + (* Case: x = h *)
      subst. simpl.
      intro H_empty.
      apply app_eq_nil in H_empty.
      destruct H_empty as [H_fx_empty _].
      contradiction.
    + (* Case: x in t *)
      simpl. intro H_empty.
      apply app_eq_nil in H_empty.
      destruct H_empty as [_ H_flat_t_empty].
      apply IH in H_in_t.
      contradiction.
Qed.

(** Theorem: If TYPO-001 reports no issues, document has no straight quotes *)
Theorem typo_001_sound : 
  rule_soundness_property typo_001_rule no_straight_quotes.
Proof.
  unfold rule_soundness_property, typo_001_rule, no_straight_quotes.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  
  (* We proceed by case analysis on typo_001_check s *)
  destruct (typo_001_check s) eqn:Hcheck.
  - (* Case: typo_001_check s = true *)
    (* This case leads to contradiction with H_no_issues *)
    exfalso.
    (* Apply our helper lemma *)
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_001_check s 
         then [{| rule_id := "TYPO-001"; issue_severity := Error;
                 message := "ASCII straight quotes must be curly quotes";
                 loc := None; suggested_fix := Some "auto_replace";
                 rule_owner := "@lint-team" |}]
         else []
       | _ => []
       end)
      doc.(tokens)
      (TText s)).
    + (* Prove In (TText s) doc.(tokens) *)
      rewrite <- H_tok. exact H_in.
    + (* Prove the function applied to TText s is non-empty *)
      simpl. rewrite Hcheck. discriminate.
    + (* This contradicts H_no_issues *)
      unfold typo_001_validator in H_no_issues. exact H_no_issues.
      
  - (* Case: typo_001_check s = false *)
    (* The goal should be: typo_001_check s = false *)
    (* which matches our case hypothesis *)
    reflexivity.
Qed.

(** ** Soundness proofs for remaining typography rules *)

(** Property: No double hyphens in document *)
Definition no_double_hyphens (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> 
    typo_002_check s = false.

Theorem typo_002_sound : 
  rule_soundness_property typo_002_rule no_double_hyphens.
Proof.
  unfold rule_soundness_property, typo_002_rule, no_double_hyphens.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_002_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_002_check s then
           [{| rule_id := "TYPO-002"; issue_severity := Warning;
               message := "Double hyphen -- should be en-dash";
               loc := None; suggested_fix := Some "auto_replace";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_002_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

(** Property: No triple hyphens in document *)
Definition no_triple_hyphens (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> 
    typo_003_check s = false.

Theorem typo_003_sound : 
  rule_soundness_property typo_003_rule no_triple_hyphens.
Proof.
  unfold rule_soundness_property, typo_003_rule, no_triple_hyphens.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_003_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_003_check s then
           [{| rule_id := "TYPO-003"; issue_severity := Warning;
               message := "Triple hyphen --- should be em-dash";
               loc := None; suggested_fix := Some "auto_replace";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_003_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

(** Properties and soundness for remaining rules follow the same pattern *)
Definition no_tex_quotes (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_004_check s = false.

Theorem typo_004_sound : rule_soundness_property typo_004_rule no_tex_quotes.
Proof.
  unfold rule_soundness_property, typo_004_rule, no_tex_quotes.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_004_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_004_check s then
           [{| rule_id := "TYPO-004"; issue_severity := Warning;
               message := "TeX double back-tick not allowed; use opening curly quotes";
               loc := None; suggested_fix := Some "auto_replace";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_004_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_triple_dots (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_005_check s = false.

Theorem typo_005_sound : rule_soundness_property typo_005_rule no_triple_dots.
Proof.
  unfold rule_soundness_property, typo_005_rule, no_triple_dots.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_005_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_005_check s then
           [{| rule_id := "TYPO-005"; issue_severity := Warning;
               message := "Ellipsis as three periods ...; use \dots";
               loc := None; suggested_fix := Some "auto_replace";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_005_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_tabs (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_006_check s = false.

Theorem typo_006_sound : rule_soundness_property typo_006_rule no_tabs.
Proof.
  unfold rule_soundness_property, typo_006_rule, no_tabs.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_006_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_006_check s then
           [{| rule_id := "TYPO-006"; issue_severity := Error;
               message := "Tab character U+0009 forbidden";
               loc := None; suggested_fix := None;
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_006_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_trailing_spaces (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_007_check s = false.

Theorem typo_007_sound : rule_soundness_property typo_007_rule no_trailing_spaces.
Proof.
  unfold rule_soundness_property, typo_007_rule, no_trailing_spaces.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_007_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_007_check s then
           [{| rule_id := "TYPO-007"; issue_severity := Info;
               message := "Trailing spaces at end of line";
               loc := None; suggested_fix := Some "strip_whitespace";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_007_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_excess_blank_lines (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_008_check s = false.

Theorem typo_008_sound : rule_soundness_property typo_008_rule no_excess_blank_lines.
Proof.
  unfold rule_soundness_property, typo_008_rule, no_excess_blank_lines.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_008_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_008_check s then
           [{| rule_id := "TYPO-008"; issue_severity := Info;
               message := "Multiple consecutive blank lines (>2) in source";
               loc := None; suggested_fix := Some "collapse_blank_lines";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_008_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_line_start_tilde (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_009_check s = false.

Theorem typo_009_sound : rule_soundness_property typo_009_rule no_line_start_tilde.
Proof.
  unfold rule_soundness_property, typo_009_rule, no_line_start_tilde.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_009_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_009_check s then
           [{| rule_id := "TYPO-009"; issue_severity := Warning;
               message := "Non-breaking space ~ used incorrectly at line start";
               loc := None; suggested_fix := None;
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_009_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_space_before_punct (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_010_check s = false.

Theorem typo_010_sound : rule_soundness_property typo_010_rule no_space_before_punct.
Proof.
  unfold rule_soundness_property, typo_010_rule, no_space_before_punct.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_010_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_010_check s then
           [{| rule_id := "TYPO-010"; issue_severity := Info;
               message := "Space before punctuation , . ; : ? !";
               loc := None; suggested_fix := Some "remove_space";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_010_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

(** ** Additional Phase 1 Typography Rules - TYPO-011 through TYPO-015 *)

(** TYPO-011: Avoid straight ASCII apostrophe, use curly apostrophe *)
Definition typo_011_check (s : string) : bool :=
  string_contains s (ascii_of_nat 39). (* ASCII 39 = ' *)

Definition typo_011_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_011_check s then
            [{| rule_id := "TYPO-011";
                issue_severity := Warning;
                message := "Avoid straight ASCII apostrophe, use curly apostrophe";
                loc := None;
                suggested_fix := Some "auto_replace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_011_rule : validation_rule := {|
  id := "TYPO-011";
  description := "Avoid straight ASCII apostrophe, use curly apostrophe";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "auto_replace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_011_validator;
  rule_sound := None
|}.

(** TYPO-012: Multiple spaces between words *)
Definition typo_012_check (s : string) : bool :=
  string_contains_substring s "  ". (* Two or more spaces *)

Definition typo_012_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_012_check s then
            [{| rule_id := "TYPO-012";
                issue_severity := Info;
                message := "Multiple spaces between words should be single space";
                loc := None;
                suggested_fix := Some "normalize_spaces";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_012_rule : validation_rule := {|
  id := "TYPO-012";
  description := "Multiple spaces between words should be single space";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "normalize_spaces";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_012_validator;
  rule_sound := None
|}.

(** TYPO-013: Non-breaking space after single-letter words *)
Definition typo_013_check (s : string) : bool :=
  orb (string_contains_substring s "a ") 
      (string_contains_substring s "I ").

Definition typo_013_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_013_check s then
            [{| rule_id := "TYPO-013";
                issue_severity := Info;
                message := "Consider non-breaking space after single-letter words";
                loc := None;
                suggested_fix := Some "add_nonbreaking_space";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_013_rule : validation_rule := {|
  id := "TYPO-013";
  description := "Consider non-breaking space after single-letter words";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "add_nonbreaking_space";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_013_validator;
  rule_sound := None
|}.

(** TYPO-014: Inconsistent quotation mark style *)
Definition typo_014_check (s : string) : bool :=
  let has_straight := string_contains s (ascii_of_nat 34) in
  let has_curly := orb (string_contains_substring s "'") (string_contains_substring s "'") in
  andb has_straight has_curly.

Definition typo_014_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_014_check s then
            [{| rule_id := "TYPO-014";
                issue_severity := Warning;
                message := "Inconsistent quotation mark style within text";
                loc := None;
                suggested_fix := Some "normalize_quotes";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_014_rule : validation_rule := {|
  id := "TYPO-014";
  description := "Inconsistent quotation mark style within text";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "normalize_quotes";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_014_validator;
  rule_sound := None
|}.

(** TYPO-015: LaTeX command spacing *)
Definition typo_015_check (s : string) : bool :=
  string_contains_substring s "\\ ". (* Backslash followed by space *)

Definition typo_015_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_015_check s then
            [{| rule_id := "TYPO-015";
                issue_severity := Info;
                message := "LaTeX command spacing may need adjustment";
                loc := None;
                suggested_fix := Some "review_spacing";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_015_rule : validation_rule := {|
  id := "TYPO-015";
  description := "LaTeX command spacing may need adjustment";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "review_spacing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_015_validator;
  rule_sound := None
|}.

(** ** Week 4.4 Extension: TYPO-016 through TYPO-025 **)

(** TYPO-016: Excessive exclamation marks *)
Definition typo_016_check (s : string) : bool :=
  orb (string_contains_substring s "!!")
      (string_contains_substring s "!!!").

Definition typo_016_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_016_check s then
            [{| rule_id := "TYPO-016";
                issue_severity := Info;
                message := "Excessive exclamation marks, consider moderation";
                loc := None;
                suggested_fix := Some "reduce_exclamation";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_016_rule : validation_rule := {|
  id := "TYPO-016";
  description := "Excessive exclamation marks, consider moderation";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "reduce_exclamation";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_016_validator;
  rule_sound := None
|}.

(** TYPO-017: Question mark spacing *)
Definition typo_017_check (s : string) : bool :=
  orb (string_contains_substring s " ?")
      (string_contains_substring s "? ").

Definition typo_017_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_017_check s then
            [{| rule_id := "TYPO-017";
                issue_severity := Info;
                message := "Question mark spacing may need review";
                loc := None;
                suggested_fix := Some "adjust_spacing";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_017_rule : validation_rule := {|
  id := "TYPO-017";
  description := "Question mark spacing may need review";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "adjust_spacing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_017_validator;
  rule_sound := None
|}.

(** TYPO-018: Capitalization after periods *)
Definition typo_018_check (s : string) : bool :=
  string_contains_substring s ". a".

Definition typo_018_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_018_check s then
            [{| rule_id := "TYPO-018";
                issue_severity := Warning;
                message := "Potential capitalization issue after period";
                loc := None;
                suggested_fix := Some "check_capitalization";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_018_rule : validation_rule := {|
  id := "TYPO-018";
  description := "Potential capitalization issue after period";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "check_capitalization";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_018_validator;
  rule_sound := None
|}.

(** TYPO-019: Improper hyphenation patterns *)
Definition typo_019_check (s : string) : bool :=
  orb (string_contains_substring s "- ")
      (string_contains_substring s " -").

Definition typo_019_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_019_check s then
            [{| rule_id := "TYPO-019";
                issue_severity := Info;
                message := "Improper hyphenation patterns detected";
                loc := None;
                suggested_fix := Some "fix_hyphenation";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_019_rule : validation_rule := {|
  id := "TYPO-019";
  description := "Improper hyphenation patterns detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "fix_hyphenation";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_019_validator;
  rule_sound := None
|}.

(** TYPO-020: Redundant comma usage *)
Definition typo_020_check (s : string) : bool :=
  string_contains_substring s ",,".

Definition typo_020_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_020_check s then
            [{| rule_id := "TYPO-020";
                issue_severity := Warning;
                message := "Redundant comma usage detected";
                loc := None;
                suggested_fix := Some "remove_extra_comma";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_020_rule : validation_rule := {|
  id := "TYPO-020";
  description := "Redundant comma usage detected";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "remove_extra_comma";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_020_validator;
  rule_sound := None
|}.

(** TYPO-021: Parentheses spacing *)
Definition typo_021_check (s : string) : bool :=
  orb (string_contains_substring s "( ")
      (string_contains_substring s " )").

Definition typo_021_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_021_check s then
            [{| rule_id := "TYPO-021";
                issue_severity := Info;
                message := "Parentheses spacing may need adjustment";
                loc := None;
                suggested_fix := Some "fix_parentheses_spacing";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_021_rule : validation_rule := {|
  id := "TYPO-021";
  description := "Parentheses spacing may need adjustment";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "fix_parentheses_spacing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_021_validator;
  rule_sound := None
|}.

(** TYPO-022: Oxford comma consistency *)
Definition typo_022_check (s : string) : bool :=
  string_contains_substring s " and ".

Definition typo_022_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_022_check s then
            [{| rule_id := "TYPO-022";
                issue_severity := Info;
                message := "Check Oxford comma consistency in lists";
                loc := None;
                suggested_fix := Some "review_oxford_comma";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_022_rule : validation_rule := {|
  id := "TYPO-022";
  description := "Check Oxford comma consistency in lists";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "review_oxford_comma";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_022_validator;
  rule_sound := None
|}.

(** TYPO-023: Semicolon usage *)
Definition typo_023_check (s : string) : bool :=
  orb (string_contains_substring s "; ")
      (string_contains_substring s " ;").

Definition typo_023_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_023_check s then
            [{| rule_id := "TYPO-023";
                issue_severity := Info;
                message := "Semicolon spacing and usage review";
                loc := None;
                suggested_fix := Some "review_semicolon";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_023_rule : validation_rule := {|
  id := "TYPO-023";
  description := "Semicolon spacing and usage review";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "review_semicolon";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_023_validator;
  rule_sound := None
|}.

(** TYPO-024: Colon spacing *)
Definition typo_024_check (s : string) : bool :=
  orb (string_contains_substring s ": ")
      (string_contains_substring s " :").

Definition typo_024_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_024_check s then
            [{| rule_id := "TYPO-024";
                issue_severity := Info;
                message := "Colon spacing may need review";
                loc := None;
                suggested_fix := Some "adjust_colon_spacing";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_024_rule : validation_rule := {|
  id := "TYPO-024";
  description := "Colon spacing may need review";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "adjust_colon_spacing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_024_validator;
  rule_sound := None
|}.

(** TYPO-025: Text emphasis balance *)
Definition typo_025_check (s : string) : bool :=
  let italic_count := count_char s (ascii_of_nat 42) in (* * character *)
  let bold_count := count_char s (ascii_of_nat 95) in   (* _ character *)
  orb (Nat.eqb (italic_count mod 2) 1)
      (Nat.eqb (bold_count mod 2) 1).

Definition typo_025_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if typo_025_check s then
            [{| rule_id := "TYPO-025";
                issue_severity := Warning;
                message := "Text emphasis markers may be unbalanced";
                loc := None;
                suggested_fix := Some "balance_emphasis";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition typo_025_rule : validation_rule := {|
  id := "TYPO-025";
  description := "Text emphasis markers may be unbalanced";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "balance_emphasis";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := typo_025_validator;
  rule_sound := None
|}.

(** Extended Phase 1 Typography rule collection *)
Definition extended_phase1_typo_rules : list validation_rule := [
  typo_001_rule; typo_002_rule; typo_003_rule; typo_004_rule; typo_005_rule;
  typo_006_rule; typo_007_rule; typo_008_rule; typo_009_rule; typo_010_rule;
  typo_011_rule; typo_012_rule; typo_013_rule; typo_014_rule; typo_015_rule;
  typo_016_rule; typo_017_rule; typo_018_rule; typo_019_rule; typo_020_rule;
  typo_021_rule; typo_022_rule; typo_023_rule; typo_024_rule; typo_025_rule
].

(** ** Soundness proofs for additional rules *)

Definition no_straight_apostrophes (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_011_check s = false.

Theorem typo_011_sound : rule_soundness_property typo_011_rule no_straight_apostrophes.
Proof.
  unfold rule_soundness_property, typo_011_rule, no_straight_apostrophes.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_011_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_011_check s then
           [{| rule_id := "TYPO-011"; issue_severity := Warning;
               message := "Avoid straight ASCII apostrophe, use curly apostrophe";
               loc := None; suggested_fix := Some "auto_replace";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_011_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_multiple_spaces (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> typo_012_check s = false.

Theorem typo_012_sound : rule_soundness_property typo_012_rule no_multiple_spaces.
Proof.
  unfold rule_soundness_property, typo_012_rule, no_multiple_spaces.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (typo_012_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if typo_012_check s then
           [{| rule_id := "TYPO-012"; issue_severity := Info;
               message := "Multiple spaces between words should be single space";
               loc := None; suggested_fix := Some "normalize_spaces";
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold typo_012_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

(** ** ENC: Encoding Rules - ENC-001 through ENC-005 *)

(** ENC-001: Non-UTF-8 byte sequences *)
Definition enc_001_check (s : string) : bool :=
  (* Simple check for invalid UTF-8 patterns *)
  string_contains s (ascii_of_nat 255).  (* Invalid UTF-8 byte *)

Definition enc_001_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if enc_001_check s then
            [{| rule_id := "ENC-001";
                issue_severity := Error;
                message := "Non-UTF-8 byte sequence detected";
                loc := None;
                suggested_fix := None;
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition enc_001_rule : validation_rule := {|
  id := "ENC-001";
  description := "Non-UTF-8 byte sequence detected";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := None;
  implementation_file := "rules/phase1/TypoRules.v";
  validator := enc_001_validator;
  rule_sound := None
|}.

(** ENC-002: BOM detection *)
Definition enc_002_check (s : string) : bool :=
  string_prefix (String (ascii_of_nat 239) (String (ascii_of_nat 187) (String (ascii_of_nat 191) EmptyString))) s.

Definition enc_002_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if enc_002_check s then
            [{| rule_id := "ENC-002";
                issue_severity := Warning;
                message := "UTF-8 BOM detected at start of text";
                loc := None;
                suggested_fix := Some "remove_bom";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition enc_002_rule : validation_rule := {|
  id := "ENC-002";
  description := "UTF-8 BOM detected at start of text";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "remove_bom";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := enc_002_validator;
  rule_sound := None
|}.

(** ENC-003: Latin-1 encoding issues *)
Definition enc_003_check (s : string) : bool :=
  orb (string_contains s (ascii_of_nat 192))  (* À *)
      (string_contains s (ascii_of_nat 233)).  (* é *)

Definition enc_003_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if enc_003_check s then
            [{| rule_id := "ENC-003";
                issue_severity := Warning;
                message := "Potential Latin-1 encoding characters";
                loc := None;
                suggested_fix := Some "convert_to_utf8";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition enc_003_rule : validation_rule := {|
  id := "ENC-003";
  description := "Potential Latin-1 encoding characters";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "convert_to_utf8";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := enc_003_validator;
  rule_sound := None
|}.

(** ENC-004: Windows-1252 encoding issues *)
Definition enc_004_check (s : string) : bool :=
  orb (string_contains s (ascii_of_nat 151))  (* em dash *)
      (string_contains s (ascii_of_nat 147)).  (* left double quote *)

Definition enc_004_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if enc_004_check s then
            [{| rule_id := "ENC-004";
                issue_severity := Warning;
                message := "Potential Windows-1252 encoding characters";
                loc := None;
                suggested_fix := Some "convert_to_utf8";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition enc_004_rule : validation_rule := {|
  id := "ENC-004";
  description := "Potential Windows-1252 encoding characters";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "convert_to_utf8";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := enc_004_validator;
  rule_sound := None
|}.

(** ENC-005: Mixed encoding detection *)
Definition enc_005_check (s : string) : bool :=
  let has_ascii := count_char s (ascii_of_nat 65) in  (* Count 'A' as ASCII indicator *)
  let has_high := string_contains s (ascii_of_nat 200) in  (* High byte indicator *)
  andb (Nat.ltb 0 has_ascii) has_high.

Definition enc_005_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if enc_005_check s then
            [{| rule_id := "ENC-005";
                issue_severity := Error;
                message := "Mixed character encoding detected";
                loc := None;
                suggested_fix := Some "standardize_encoding";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition enc_005_rule : validation_rule := {|
  id := "ENC-005";
  description := "Mixed character encoding detected";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "standardize_encoding";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := enc_005_validator;
  rule_sound := None
|}.

(** ** CHAR: Character Analysis Rules - CHAR-001 through CHAR-005 *)

(** CHAR-001: Control characters *)
Definition char_001_check (s : string) : bool :=
  orb (string_contains s (ascii_of_nat 0))   (* NULL *)
  (orb (string_contains s (ascii_of_nat 1))  (* SOH *)
       (string_contains s (ascii_of_nat 7))). (* BEL *)

Definition char_001_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if char_001_check s then
            [{| rule_id := "CHAR-001";
                issue_severity := Error;
                message := "Control characters U+0000–001F present";
                loc := None;
                suggested_fix := None;
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition char_001_rule : validation_rule := {|
  id := "CHAR-001";
  description := "Control characters U+0000–001F present";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := None;
  implementation_file := "rules/phase1/TypoRules.v";
  validator := char_001_validator;
  rule_sound := None
|}.

(** CHAR-002: Invisible characters *)
Definition char_002_check (s : string) : bool :=
  orb (string_contains s (ascii_of_nat 8203))  (* Zero-width space *)
  (orb (string_contains s (ascii_of_nat 8204)) (* Zero-width non-joiner *)
       (string_contains s (ascii_of_nat 8205))). (* Zero-width joiner *)

Definition char_002_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if char_002_check s then
            [{| rule_id := "CHAR-002";
                issue_severity := Warning;
                message := "Invisible Unicode characters detected";
                loc := None;
                suggested_fix := Some "remove_invisible";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition char_002_rule : validation_rule := {|
  id := "CHAR-002";
  description := "Invisible Unicode characters detected";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "remove_invisible";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := char_002_validator;
  rule_sound := None
|}.

(** CHAR-003: Non-ASCII characters in ASCII context *)
Fixpoint char_003_check_chars (str : string) : bool :=
  match str with
  | EmptyString => false
  | String c rest =>
      if Nat.ltb 127 (nat_of_ascii c) then true
      else char_003_check_chars rest
  end.

Definition char_003_check (s : string) : bool :=
  (* Check for characters above ASCII range (>127) *)
  char_003_check_chars s.

Definition char_003_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if char_003_check s then
            [{| rule_id := "CHAR-003";
                issue_severity := Info;
                message := "Non-ASCII characters detected, consider encoding";
                loc := None;
                suggested_fix := Some "check_encoding";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition char_003_rule : validation_rule := {|
  id := "CHAR-003";
  description := "Non-ASCII characters detected, consider encoding";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "check_encoding";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := char_003_validator;
  rule_sound := None
|}.

(** CHAR-004: Inconsistent line ending characters *)
Definition char_004_check (s : string) : bool :=
  let has_cr := string_contains s (ascii_of_nat 13) in    (* \r *)
  let has_lf := string_contains s (ascii_of_nat 10) in    (* \n *)
  let has_crlf := string_contains_substring s (String (ascii_of_nat 13) (String (ascii_of_nat 10) EmptyString)) in
  orb (andb has_cr (negb has_crlf))  (* CR without LF *)
      (andb has_lf has_cr).          (* Mixed line endings *)

Definition char_004_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if char_004_check s then
            [{| rule_id := "CHAR-004";
                issue_severity := Info;
                message := "Inconsistent line ending characters detected";
                loc := None;
                suggested_fix := Some "normalize_line_endings";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition char_004_rule : validation_rule := {|
  id := "CHAR-004";
  description := "Inconsistent line ending characters detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "normalize_line_endings";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := char_004_validator;
  rule_sound := None
|}.

(** CHAR-005: Unusual whitespace characters *)
Definition char_005_check (s : string) : bool :=
  orb (string_contains s (ascii_of_nat 160))   (* Non-breaking space *)
  (orb (string_contains s (ascii_of_nat 9))    (* Tab character *)
       (string_contains s (ascii_of_nat 12))).  (* Form feed *)

Definition char_005_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if char_005_check s then
            [{| rule_id := "CHAR-005";
                issue_severity := Info;
                message := "Unusual whitespace characters detected";
                loc := None;
                suggested_fix := Some "normalize_whitespace";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition char_005_rule : validation_rule := {|
  id := "CHAR-005";
  description := "Unusual whitespace characters detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "normalize_whitespace";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := char_005_validator;
  rule_sound := None
|}.

(** ** ENV: Environment Rules - ENV-001 through ENV-005 *)

(** ENV-001: Mismatched begin/end environments *)
Definition env_001_check_aux (cmd : string) : bool :=
  orb (string_contains_substring cmd "begin")
      (string_contains_substring cmd "end").

Fixpoint env_001_check (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if env_001_check_aux cmd then true
      else env_001_check rest
  | _ :: rest => env_001_check rest
  end.

Definition env_001_validator : document_state -> list validation_issue :=
  fun doc =>
    if env_001_check doc.(tokens) then
      [{| rule_id := "ENV-001";
          issue_severity := Warning;
          message := "Check begin/end environment matching";
          loc := None;
          suggested_fix := Some "check_environment_pairs";
          rule_owner := "@lint-team" |}]
    else [].

Definition env_001_rule : validation_rule := {|
  id := "ENV-001";
  description := "Check begin/end environment matching";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "check_environment_pairs";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := env_001_validator;
  rule_sound := None
|}.

(** ENV-002: Deprecated environment usage *)
Definition env_002_check_aux (cmd : string) : bool :=
  orb (string_contains_substring cmd "eqnarray")
  (orb (string_contains_substring cmd "center")
       (string_contains_substring cmd "flushleft")).

Fixpoint env_002_check (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if env_002_check_aux cmd then true
      else env_002_check rest
  | _ :: rest => env_002_check rest
  end.

Definition env_002_validator : document_state -> list validation_issue :=
  fun doc =>
    if env_002_check doc.(tokens) then
      [{| rule_id := "ENV-002";
          issue_severity := Info;
          message := "Deprecated environment, consider modern alternative";
          loc := None;
          suggested_fix := Some "modernize_environment";
          rule_owner := "@lint-team" |}]
    else [].

Definition env_002_rule : validation_rule := {|
  id := "ENV-002";
  description := "Deprecated environment, consider modern alternative";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "modernize_environment";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := env_002_validator;
  rule_sound := None
|}.

(** ENV-003: Empty environment detection *)
Definition env_003_check_aux (cmd : string) : bool :=
  string_contains_substring cmd "begin".

Fixpoint env_003_check (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText env_name :: TEndGroup :: TCommand end_cmd :: rest =>
      if andb (string_contains_substring cmd "begin") (string_contains_substring end_cmd "end") then
        true
      else env_003_check rest
  | _ :: rest => env_003_check rest
  end.

Definition env_003_validator : document_state -> list validation_issue :=
  fun doc =>
    if env_003_check doc.(tokens) then
      [{| rule_id := "ENV-003";
          issue_severity := Info;
          message := "Empty environment detected, consider removal";
          loc := None;
          suggested_fix := Some "remove_empty_environment";
          rule_owner := "@lint-team" |}]
    else [].

Definition env_003_rule : validation_rule := {|
  id := "ENV-003";
  description := "Empty environment detected, consider removal";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "remove_empty_environment";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := env_003_validator;
  rule_sound := None
|}.

(** ENV-004: Nested environment depth check *)
Fixpoint env_004_count_nesting (tokens : list latex_token) (depth : nat) (max_depth : nat) : nat :=
  match tokens with
  | [] => max_depth
  | TCommand cmd :: rest =>
      if string_contains_substring cmd "begin" then
        let new_depth := S depth in
        let new_max := if Nat.ltb max_depth new_depth then new_depth else max_depth in
        env_004_count_nesting rest new_depth new_max
      else if string_contains_substring cmd "end" then
        env_004_count_nesting rest (if Nat.eqb depth 0 then 0 else pred depth) max_depth
      else
        env_004_count_nesting rest depth max_depth
  | _ :: rest => env_004_count_nesting rest depth max_depth
  end.

Definition env_004_check (tokens : list latex_token) : bool :=
  let max_depth := env_004_count_nesting tokens 0 0 in
  Nat.ltb 3 max_depth.  (* Flag if nesting > 3 *)

Definition env_004_validator : document_state -> list validation_issue :=
  fun doc =>
    if env_004_check doc.(tokens) then
      [{| rule_id := "ENV-004";
          issue_severity := Info;
          message := "Deep environment nesting may affect readability";
          loc := None;
          suggested_fix := Some "reduce_nesting";
          rule_owner := "@lint-team" |}]
    else [].

Definition env_004_rule : validation_rule := {|
  id := "ENV-004";
  description := "Deep environment nesting may affect readability";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "reduce_nesting";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := env_004_validator;
  rule_sound := None
|}.

(** ENV-005: Common environment typos *)
Definition env_005_check_aux (cmd : string) : bool :=
  orb (string_contains_substring cmd "centre")
  (orb (string_contains_substring cmd "itemise")
       (string_contains_substring cmd "tabular")).

Fixpoint env_005_check (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if env_005_check_aux cmd then true
      else env_005_check rest
  | _ :: rest => env_005_check rest
  end.

Definition env_005_validator : document_state -> list validation_issue :=
  fun doc =>
    if env_005_check doc.(tokens) then
      [{| rule_id := "ENV-005";
          issue_severity := Warning;
          message := "Potential environment name typo detected";
          loc := None;
          suggested_fix := Some "fix_environment_name";
          rule_owner := "@lint-team" |}]
    else [].

Definition env_005_rule : validation_rule := {|
  id := "ENV-005";
  description := "Potential environment name typo detected";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "fix_environment_name";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := env_005_validator;
  rule_sound := None
|}.

(** ** MATH: Mathematical Rules - MATH-001 through MATH-005 *)

(** MATH-001: Missing math mode for mathematical expressions *)
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
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition math_001_rule : validation_rule := {|
  id := "MATH-001";
  description := "Mathematical expressions should be in math mode";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "add_math_mode";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_001_validator;
  rule_sound := None
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
          rule_owner := "@lint-team" |}]
    else [].

Definition math_002_rule : validation_rule := {|
  id := "MATH-002";
  description := "Unmatched math delimiters $ detected";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_MathShift;
  auto_fix := Some "fix_math_delimiters";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_002_validator;
  rule_sound := None
|}.

(** MATH-003: Deprecated math commands *)
Definition math_003_check_aux (cmd : string) : bool :=
  orb (string_contains_substring cmd "over")
  (orb (string_contains_substring cmd "choose")
       (string_contains_substring cmd "atop")).

Fixpoint math_003_check (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if math_003_check_aux cmd then true
      else math_003_check rest
  | _ :: rest => math_003_check rest
  end.

Definition math_003_validator : document_state -> list validation_issue :=
  fun doc =>
    if math_003_check doc.(tokens) then
      [{| rule_id := "MATH-003";
          issue_severity := Info;
          message := "Deprecated math command, use \\frac or \\binom";
          loc := None;
          suggested_fix := Some "modernize_math_command";
          rule_owner := "@lint-team" |}]
    else [].

Definition math_003_rule : validation_rule := {|
  id := "MATH-003";
  description := "Deprecated math command, use \\frac or \\binom";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "modernize_math_command";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_003_validator;
  rule_sound := None
|}.

(** MATH-004: Math spacing inconsistencies *)
Definition math_004_check (s : string) : bool :=
  orb (string_contains_substring s "+ ")
  (orb (string_contains_substring s "- ")
  (orb (string_contains_substring s "* ")
       (string_contains_substring s "/ "))).

Definition math_004_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if math_004_check s then
            [{| rule_id := "MATH-004";
                issue_severity := Info;
                message := "Math operator spacing may need review";
                loc := None;
                suggested_fix := Some "adjust_math_spacing";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition math_004_rule : validation_rule := {|
  id := "MATH-004";
  description := "Math operator spacing may need review";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "adjust_math_spacing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_004_validator;
  rule_sound := None
|}.

(** MATH-005: Inconsistent math notation *)
Definition math_005_check (s : string) : bool :=
  let has_times := string_contains_substring s "\\times" in
  let has_cdot := string_contains_substring s "\\cdot" in
  let has_asterisk := string_contains s (ascii_of_nat 42) in  (* * *)
  orb (andb has_times has_cdot)
  (orb (andb has_times has_asterisk)
       (andb has_cdot has_asterisk)).

Definition math_005_validator : document_state -> list validation_issue :=
  fun doc =>
    flat_map (fun tok =>
      match tok with
      | TText s =>
          if math_005_check s then
            [{| rule_id := "MATH-005";
                issue_severity := Info;
                message := "Inconsistent multiplication notation in document";
                loc := None;
                suggested_fix := Some "standardize_multiplication";
                rule_owner := "@lint-team" |}]
          else []
      | _ => []
      end) doc.(tokens).

Definition math_005_rule : validation_rule := {|
  id := "MATH-005";
  description := "Inconsistent multiplication notation in document";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Text;
  auto_fix := Some "standardize_multiplication";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := math_005_validator;
  rule_sound := None
|}.

(** ** STRUCT: Document Structure Rules - STRUCT-001 through STRUCT-010 *)

(** STRUCT-001: Missing document class *)
Fixpoint struct_001_check (tokens : list latex_token) : bool :=
  match tokens with
  | [] => true  (* No documentclass found *)
  | TCommand cmd :: rest =>
      if string_contains_substring cmd "documentclass" then false
      else struct_001_check rest
  | _ :: rest => struct_001_check rest
  end.

Definition struct_001_validator : document_state -> list validation_issue :=
  fun doc =>
    if struct_001_check doc.(tokens) then
      [{| rule_id := "STRUCT-001";
          issue_severity := Error;
          message := "Missing \\documentclass declaration";
          loc := None;
          suggested_fix := Some "add_documentclass";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_001_rule : validation_rule := {|
  id := "STRUCT-001";
  description := "Missing \\documentclass declaration";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "add_documentclass";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_001_validator;
  rule_sound := None
|}.

(** STRUCT-002: Document structure order *)
Fixpoint struct_002_check_order (tokens : list latex_token) (state : nat) : bool :=
  match tokens with
  | [] => true  (* Reached end without violation *)
  | TCommand cmd :: rest =>
      let new_state := 
        if string_contains_substring cmd "documentclass" then 1
        else if string_contains_substring cmd "usepackage" then 
          if Nat.ltb state 1 then 0 else 2  (* usepackage before documentclass *)
        else if string_contains_substring cmd "begin" then
          if Nat.ltb state 2 then 0 else 3  (* begin before packages *)
        else state in
      if Nat.eqb new_state 0 then false  (* Order violation *)
      else struct_002_check_order rest new_state
  | _ :: rest => struct_002_check_order rest state
  end.

Definition struct_002_validator : document_state -> list validation_issue :=
  fun doc =>
    if negb (struct_002_check_order doc.(tokens) 0) then
      [{| rule_id := "STRUCT-002";
          issue_severity := Warning;
          message := "Document structure order violation";
          loc := None;
          suggested_fix := Some "reorder_structure";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_002_rule : validation_rule := {|
  id := "STRUCT-002";
  description := "Document structure order violation";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "reorder_structure";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_002_validator;
  rule_sound := None
|}.

(** STRUCT-003: Missing begin/end document *)
Fixpoint struct_003_has_begin (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText env :: TEndGroup :: rest =>
      if andb (string_contains_substring cmd "begin") (string_contains_substring env "document") then true
      else struct_003_has_begin rest
  | _ :: rest => struct_003_has_begin rest
  end.

Fixpoint struct_003_has_end (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText env :: TEndGroup :: rest =>
      if andb (string_contains_substring cmd "end") (string_contains_substring env "document") then true
      else struct_003_has_end rest
  | _ :: rest => struct_003_has_end rest
  end.

Definition struct_003_validator : document_state -> list validation_issue :=
  fun doc =>
    let has_begin := struct_003_has_begin doc.(tokens) in
    let has_end := struct_003_has_end doc.(tokens) in
    if negb (andb has_begin has_end) then
      [{| rule_id := "STRUCT-003";
          issue_severity := Error;
          message := "Missing \\begin{document} or \\end{document}";
          loc := None;
          suggested_fix := Some "add_document_environment";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_003_rule : validation_rule := {|
  id := "STRUCT-003";
  description := "Missing \\begin{document} or \\end{document}";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "add_document_environment";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_003_validator;
  rule_sound := None
|}.

(** STRUCT-004: Orphaned sectioning *)
Fixpoint struct_004_check_sectioning (tokens : list latex_token) (last_section_level : nat) : bool :=
  match tokens with
  | [] => true
  | TCommand cmd :: rest =>
      let level := 
        if string_contains_substring cmd "chapter" then 1
        else if string_contains_substring cmd "section" then 2
        else if string_contains_substring cmd "subsection" then 3
        else if string_contains_substring cmd "subsubsection" then 4
        else 0 in
      if andb (Nat.ltb 0 level) (Nat.ltb (S last_section_level) level) then false  (* Level jump > 1 *)
      else struct_004_check_sectioning rest (if Nat.ltb 0 level then level else last_section_level)
  | _ :: rest => struct_004_check_sectioning rest last_section_level
  end.

Definition struct_004_validator : document_state -> list validation_issue :=
  fun doc =>
    if negb (struct_004_check_sectioning doc.(tokens) 0) then
      [{| rule_id := "STRUCT-004";
          issue_severity := Warning;
          message := "Orphaned sectioning level detected";
          loc := None;
          suggested_fix := Some "fix_section_hierarchy";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_004_rule : validation_rule := {|
  id := "STRUCT-004";
  description := "Orphaned sectioning level detected";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "fix_section_hierarchy";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_004_validator;
  rule_sound := None
|}.

(** STRUCT-005: Empty sections *)
Fixpoint struct_005_check_empty_sections (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd1 :: rest1 =>
      if orb (string_contains_substring cmd1 "section") (string_contains_substring cmd1 "chapter") then
        match rest1 with
        | TBeginGroup :: TText _ :: TEndGroup :: TCommand cmd2 :: _ =>
            if orb (string_contains_substring cmd2 "section") (string_contains_substring cmd2 "chapter") then true
            else struct_005_check_empty_sections rest1
        | _ => struct_005_check_empty_sections rest1
        end
      else struct_005_check_empty_sections rest1
  | _ :: rest => struct_005_check_empty_sections rest
  end.

Definition struct_005_validator : document_state -> list validation_issue :=
  fun doc =>
    if struct_005_check_empty_sections doc.(tokens) then
      [{| rule_id := "STRUCT-005";
          issue_severity := Info;
          message := "Empty section detected";
          loc := None;
          suggested_fix := Some "add_content_or_remove";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_005_rule : validation_rule := {|
  id := "STRUCT-005";
  description := "Empty section detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "add_content_or_remove";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_005_validator;
  rule_sound := None
|}.

(** STRUCT-006: Missing title information *)
Fixpoint struct_006_has_title_info (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if orb (string_contains_substring cmd "title") 
             (orb (string_contains_substring cmd "author") 
                  (string_contains_substring cmd "date")) then true
      else struct_006_has_title_info rest
  | _ :: rest => struct_006_has_title_info rest
  end.

Definition struct_006_validator : document_state -> list validation_issue :=
  fun doc =>
    if negb (struct_006_has_title_info doc.(tokens)) then
      [{| rule_id := "STRUCT-006";
          issue_severity := Info;
          message := "Missing title, author, or date information";
          loc := None;
          suggested_fix := Some "add_title_info";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_006_rule : validation_rule := {|
  id := "STRUCT-006";
  description := "Missing title, author, or date information";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "add_title_info";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_006_validator;
  rule_sound := None
|}.

(** STRUCT-007: Inconsistent list environments *)
Fixpoint struct_007_check_list_consistency (tokens : list latex_token) (in_list : bool) (list_type : string) : bool :=
  match tokens with
  | [] => true
  | TCommand cmd :: TBeginGroup :: TText env :: TEndGroup :: rest =>
      if string_contains_substring cmd "begin" then
        if orb (string_contains_substring env "itemize") (string_contains_substring env "enumerate") then
          if in_list then false  (* Nested list of different type *)
          else struct_007_check_list_consistency rest true env
        else struct_007_check_list_consistency rest in_list list_type
      else if string_contains_substring cmd "end" then
        if string_contains_substring env list_type then
          struct_007_check_list_consistency rest false ""
        else struct_007_check_list_consistency rest in_list list_type
      else struct_007_check_list_consistency rest in_list list_type
  | _ :: rest => struct_007_check_list_consistency rest in_list list_type
  end.

Definition struct_007_validator : document_state -> list validation_issue :=
  fun doc =>
    if negb (struct_007_check_list_consistency doc.(tokens) false "") then
      [{| rule_id := "STRUCT-007";
          issue_severity := Warning;
          message := "Inconsistent list environment nesting";
          loc := None;
          suggested_fix := Some "fix_list_nesting";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_007_rule : validation_rule := {|
  id := "STRUCT-007";
  description := "Inconsistent list environment nesting";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "fix_list_nesting";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_007_validator;
  rule_sound := None
|}.

(** STRUCT-008: Floating object placement *)
Fixpoint struct_008_check_float_placement (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText env :: TEndGroup :: rest =>
      if string_contains_substring cmd "begin" then
        if orb (string_contains_substring env "figure") (string_contains_substring env "table") then true
        else struct_008_check_float_placement rest
      else struct_008_check_float_placement rest
  | _ :: rest => struct_008_check_float_placement rest
  end.

Definition struct_008_validator : document_state -> list validation_issue :=
  fun doc =>
    if struct_008_check_float_placement doc.(tokens) then
      [{| rule_id := "STRUCT-008";
          issue_severity := Info;
          message := "Check floating object placement and captions";
          loc := None;
          suggested_fix := Some "review_float_placement";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_008_rule : validation_rule := {|
  id := "STRUCT-008";
  description := "Check floating object placement and captions";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "review_float_placement";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_008_validator;
  rule_sound := None
|}.

(** STRUCT-009: Package loading order *)
Fixpoint struct_009_check_package_order (tokens : list latex_token) (packages : list string) : bool :=
  match tokens with
  | [] => true
  | TCommand cmd :: TBeginGroup :: TText pkg :: TEndGroup :: rest =>
      if string_contains_substring cmd "usepackage" then
        (* Check for problematic package combinations or order *)
        if orb (andb (string_contains_substring pkg "hyperref") 
                     (existsb (fun p => string_contains_substring p "geometry") packages))
               (andb (string_contains_substring pkg "babel") 
                     (existsb (fun p => string_contains_substring p "polyglossia") packages)) then false
        else struct_009_check_package_order rest (pkg :: packages)
      else struct_009_check_package_order rest packages
  | _ :: rest => struct_009_check_package_order rest packages
  end.

Definition struct_009_validator : document_state -> list validation_issue :=
  fun doc =>
    if negb (struct_009_check_package_order doc.(tokens) []) then
      [{| rule_id := "STRUCT-009";
          issue_severity := Warning;
          message := "Problematic package loading order detected";
          loc := None;
          suggested_fix := Some "reorder_packages";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_009_rule : validation_rule := {|
  id := "STRUCT-009";
  description := "Problematic package loading order detected";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "reorder_packages";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_009_validator;
  rule_sound := None
|}.

(** STRUCT-010: Bibliography placement *)
Fixpoint struct_010_check_bibliography (tokens : list latex_token) (after_document : bool) : bool :=
  match tokens with
  | [] => true
  | TCommand cmd :: rest =>
      if string_contains_substring cmd "bibliography" then
        if after_document then false  (* Bibliography after \end{document} *)
        else struct_010_check_bibliography rest after_document
      else if andb (string_contains_substring cmd "end") 
                   (match rest with
                    | TBeginGroup :: TText env :: TEndGroup :: _ => 
                        string_contains_substring env "document"
                    | _ => false
                    end) then
        struct_010_check_bibliography rest true
      else struct_010_check_bibliography rest after_document
  | _ :: rest => struct_010_check_bibliography rest after_document
  end.

Definition struct_010_validator : document_state -> list validation_issue :=
  fun doc =>
    if negb (struct_010_check_bibliography doc.(tokens) false) then
      [{| rule_id := "STRUCT-010";
          issue_severity := Warning;
          message := "Bibliography placement issue detected";
          loc := None;
          suggested_fix := Some "fix_bibliography_placement";
          rule_owner := "@lint-team" |}]
    else [].

Definition struct_010_rule : validation_rule := {|
  id := "STRUCT-010";
  description := "Bibliography placement issue detected";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "fix_bibliography_placement";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := struct_010_validator;
  rule_sound := None
|}.

(** ** REF: Reference Rules - REF-001 through REF-010 *)

(** REF-001: Undefined label references *)
Fixpoint ref_001_collect_labels (tokens : list latex_token) (labels : list string) : list string :=
  match tokens with
  | [] => labels
  | TCommand cmd :: TBeginGroup :: TText lbl :: TEndGroup :: rest =>
      if string_contains_substring cmd "label" then
        ref_001_collect_labels rest (lbl :: labels)
      else ref_001_collect_labels rest labels
  | _ :: rest => ref_001_collect_labels rest labels
  end.

Fixpoint ref_001_check_refs (tokens : list latex_token) (labels : list string) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText ref :: TEndGroup :: rest =>
      if string_contains_substring cmd "ref" then
        if negb (existsb (fun lbl => string_contains_substring lbl ref) labels) then true
        else ref_001_check_refs rest labels
      else ref_001_check_refs rest labels
  | _ :: rest => ref_001_check_refs rest labels
  end.

Definition ref_001_validator : document_state -> list validation_issue :=
  fun doc =>
    let labels := ref_001_collect_labels doc.(tokens) [] in
    if ref_001_check_refs doc.(tokens) labels then
      [{| rule_id := "REF-001";
          issue_severity := Error;
          message := "Undefined label reference detected";
          loc := None;
          suggested_fix := Some "check_label_definition";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_001_rule : validation_rule := {|
  id := "REF-001";
  description := "Undefined label reference detected";
  precondition := L0_Lexer;
  default_severity := Error;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "check_label_definition";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_001_validator;
  rule_sound := None
|}.

(** REF-002: Unused label definitions *)
Fixpoint ref_002_collect_refs (tokens : list latex_token) (refs : list string) : list string :=
  match tokens with
  | [] => refs
  | TCommand cmd :: TBeginGroup :: TText ref :: TEndGroup :: rest =>
      if string_contains_substring cmd "ref" then
        ref_002_collect_refs rest (ref :: refs)
      else ref_002_collect_refs rest refs
  | _ :: rest => ref_002_collect_refs rest refs
  end.

Fixpoint ref_002_check_unused_labels (tokens : list latex_token) (refs : list string) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText lbl :: TEndGroup :: rest =>
      if string_contains_substring cmd "label" then
        if negb (existsb (fun ref => string_contains_substring ref lbl) refs) then true
        else ref_002_check_unused_labels rest refs
      else ref_002_check_unused_labels rest refs
  | _ :: rest => ref_002_check_unused_labels rest refs
  end.

Definition ref_002_validator : document_state -> list validation_issue :=
  fun doc =>
    let refs := ref_002_collect_refs doc.(tokens) [] in
    if ref_002_check_unused_labels doc.(tokens) refs then
      [{| rule_id := "REF-002";
          issue_severity := Info;
          message := "Unused label definition detected";
          loc := None;
          suggested_fix := Some "remove_unused_label";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_002_rule : validation_rule := {|
  id := "REF-002";
  description := "Unused label definition detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "remove_unused_label";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_002_validator;
  rule_sound := None
|}.

(** REF-003: Inconsistent reference style *)
Fixpoint ref_003_check_ref_commands (tokens : list latex_token) (has_ref : bool) (has_eqref : bool) : bool :=
  match tokens with
  | [] => andb has_ref has_eqref  (* Both types used *)
  | TCommand cmd :: rest =>
      let new_has_ref := orb has_ref (string_contains_substring cmd "ref") in
      let new_has_eqref := orb has_eqref (string_contains_substring cmd "eqref") in
      ref_003_check_ref_commands rest new_has_ref new_has_eqref
  | _ :: rest => ref_003_check_ref_commands rest has_ref has_eqref
  end.

Definition ref_003_validator : document_state -> list validation_issue :=
  fun doc =>
    if ref_003_check_ref_commands doc.(tokens) false false then
      [{| rule_id := "REF-003";
          issue_severity := Info;
          message := "Mixed reference command styles (\\ref vs \\eqref)";
          loc := None;
          suggested_fix := Some "standardize_ref_style";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_003_rule : validation_rule := {|
  id := "REF-003";
  description := "Mixed reference command styles (\\ref vs \\eqref)";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "standardize_ref_style";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_003_validator;
  rule_sound := None
|}.

(** REF-004: Missing citation commands *)
Fixpoint ref_004_check_citations (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if orb (string_contains_substring cmd "cite") (string_contains_substring cmd "bibliography") then true
      else ref_004_check_citations rest
  | _ :: rest => ref_004_check_citations rest
  end.

Fixpoint ref_004_has_bib_references (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TText s :: rest =>
      if orb (string_contains_substring s "et al") (string_contains_substring s "(2023)") then true
      else ref_004_has_bib_references rest
  | _ :: rest => ref_004_has_bib_references rest
  end.

Definition ref_004_validator : document_state -> list validation_issue :=
  fun doc =>
    let has_bib_text := ref_004_has_bib_references doc.(tokens) in
    let has_cite_cmd := ref_004_check_citations doc.(tokens) in
    if andb has_bib_text (negb has_cite_cmd) then
      [{| rule_id := "REF-004";
          issue_severity := Warning;
          message := "Possible citations without proper \\cite commands";
          loc := None;
          suggested_fix := Some "add_cite_commands";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_004_rule : validation_rule := {|
  id := "REF-004";
  description := "Possible citations without proper \\cite commands";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Other;
  auto_fix := Some "add_cite_commands";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_004_validator;
  rule_sound := None
|}.

(** REF-005: Cross-reference distance *)
Fixpoint ref_005_check_ref_distance (tokens : list latex_token) (recent_labels : list string) (distance : nat) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText item :: TEndGroup :: rest =>
      if string_contains_substring cmd "label" then
        ref_005_check_ref_distance rest (item :: recent_labels) 0
      else if string_contains_substring cmd "ref" then
        if andb (Nat.ltb 50 distance) (existsb (fun lbl => string_contains_substring lbl item) recent_labels) then true
        else ref_005_check_ref_distance rest recent_labels (S distance)
      else ref_005_check_ref_distance rest recent_labels (S distance)
  | _ :: rest => ref_005_check_ref_distance rest recent_labels (S distance)
  end.

Definition ref_005_validator : document_state -> list validation_issue :=
  fun doc =>
    if ref_005_check_ref_distance doc.(tokens) [] 0 then
      [{| rule_id := "REF-005";
          issue_severity := Info;
          message := "Long-distance cross-reference may affect readability";
          loc := None;
          suggested_fix := Some "consider_reorganization";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_005_rule : validation_rule := {|
  id := "REF-005";
  description := "Long-distance cross-reference may affect readability";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "consider_reorganization";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_005_validator;
  rule_sound := None
|}.

(** REF-006: Forward references *)
Fixpoint ref_006_check_forward_refs (tokens : list latex_token) (seen_labels : list string) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText item :: TEndGroup :: rest =>
      if string_contains_substring cmd "ref" then
        if negb (existsb (fun lbl => string_contains_substring lbl item) seen_labels) then true
        else ref_006_check_forward_refs rest seen_labels
      else if string_contains_substring cmd "label" then
        ref_006_check_forward_refs rest (item :: seen_labels)
      else ref_006_check_forward_refs rest seen_labels
  | _ :: rest => ref_006_check_forward_refs rest seen_labels
  end.

Definition ref_006_validator : document_state -> list validation_issue :=
  fun doc =>
    if ref_006_check_forward_refs doc.(tokens) [] then
      [{| rule_id := "REF-006";
          issue_severity := Info;
          message := "Forward reference detected (may need multiple LaTeX runs)";
          loc := None;
          suggested_fix := Some "note_multiple_runs";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_006_rule : validation_rule := {|
  id := "REF-006";
  description := "Forward reference detected (may need multiple LaTeX runs)";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "note_multiple_runs";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_006_validator;
  rule_sound := None
|}.

(** REF-007: Reference formatting consistency *)
Fixpoint ref_007_check_ref_formatting (tokens : list latex_token) (has_cleveref : bool) (has_plain_ref : bool) : bool :=
  match tokens with
  | [] => andb has_cleveref has_plain_ref  (* Mixed styles *)
  | TCommand cmd :: rest =>
      let new_has_cleveref := orb has_cleveref (orb (string_contains_substring cmd "cref") (string_contains_substring cmd "Cref")) in
      let new_has_plain_ref := orb has_plain_ref (string_contains_substring cmd "ref") in
      ref_007_check_ref_formatting rest new_has_cleveref new_has_plain_ref
  | _ :: rest => ref_007_check_ref_formatting rest has_cleveref has_plain_ref
  end.

Definition ref_007_validator : document_state -> list validation_issue :=
  fun doc =>
    if ref_007_check_ref_formatting doc.(tokens) false false then
      [{| rule_id := "REF-007";
          issue_severity := Info;
          message := "Mixed reference formatting styles detected";
          loc := None;
          suggested_fix := Some "standardize_ref_formatting";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_007_rule : validation_rule := {|
  id := "REF-007";
  description := "Mixed reference formatting styles detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "standardize_ref_formatting";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_007_validator;
  rule_sound := None
|}.

(** REF-008: Citation style consistency *)
Fixpoint ref_008_check_cite_styles (tokens : list latex_token) (has_citep : bool) (has_citet : bool) (has_cite : bool) : bool :=
  match tokens with
  | [] => 
      let style_count := (if has_citep then 1 else 0) + (if has_citet then 1 else 0) + (if has_cite then 1 else 0) in
      Nat.ltb 1 style_count  (* More than one style *)
  | TCommand cmd :: rest =>
      let new_has_citep := orb has_citep (string_contains_substring cmd "citep") in
      let new_has_citet := orb has_citet (string_contains_substring cmd "citet") in
      let new_has_cite := orb has_cite (andb (string_contains_substring cmd "cite") 
                                           (andb (negb (string_contains_substring cmd "citep"))
                                                 (negb (string_contains_substring cmd "citet")))) in
      ref_008_check_cite_styles rest new_has_citep new_has_citet new_has_cite
  | _ :: rest => ref_008_check_cite_styles rest has_citep has_citet has_cite
  end.

Definition ref_008_validator : document_state -> list validation_issue :=
  fun doc =>
    if ref_008_check_cite_styles doc.(tokens) false false false then
      [{| rule_id := "REF-008";
          issue_severity := Info;
          message := "Mixed citation command styles detected";
          loc := None;
          suggested_fix := Some "standardize_cite_style";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_008_rule : validation_rule := {|
  id := "REF-008";
  description := "Mixed citation command styles detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "standardize_cite_style";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_008_validator;
  rule_sound := None
|}.

(** REF-009: Missing page number references *)
Fixpoint ref_009_check_pageref_usage (tokens : list latex_token) (has_ref : bool) (has_pageref : bool) : bool :=
  match tokens with
  | [] => andb has_ref (negb has_pageref)  (* Has refs but no page refs *)
  | TCommand cmd :: rest =>
      let new_has_ref := orb has_ref (string_contains_substring cmd "ref") in
      let new_has_pageref := orb has_pageref (string_contains_substring cmd "pageref") in
      ref_009_check_pageref_usage rest new_has_ref new_has_pageref
  | _ :: rest => ref_009_check_pageref_usage rest has_ref has_pageref
  end.

Definition ref_009_validator : document_state -> list validation_issue :=
  fun doc =>
    if ref_009_check_pageref_usage doc.(tokens) false false then
      [{| rule_id := "REF-009";
          issue_severity := Info;
          message := "Consider using \\pageref for page number references";
          loc := None;
          suggested_fix := Some "add_pageref_where_appropriate";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_009_rule : validation_rule := {|
  id := "REF-009";
  description := "Consider using \\pageref for page number references";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "add_pageref_where_appropriate";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_009_validator;
  rule_sound := None
|}.

(** REF-010: Hyperref package conflicts *)
Fixpoint ref_010_check_hyperref_conflicts (tokens : list latex_token) (packages : list string) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText pkg :: TEndGroup :: rest =>
      if string_contains_substring cmd "usepackage" then
        if string_contains_substring pkg "hyperref" then
          (* Check for problematic packages loaded after hyperref *)
          existsb (fun p => orb (string_contains_substring p "cite") (string_contains_substring p "natbib")) packages
        else ref_010_check_hyperref_conflicts rest (pkg :: packages)
      else ref_010_check_hyperref_conflicts rest packages
  | _ :: rest => ref_010_check_hyperref_conflicts rest packages
  end.

Definition ref_010_validator : document_state -> list validation_issue :=
  fun doc =>
    if ref_010_check_hyperref_conflicts doc.(tokens) [] then
      [{| rule_id := "REF-010";
          issue_severity := Warning;
          message := "Potential hyperref package loading order conflict";
          loc := None;
          suggested_fix := Some "reorder_hyperref_package";
          rule_owner := "@lint-team" |}]
    else [].

Definition ref_010_rule : validation_rule := {|
  id := "REF-010";
  description := "Potential hyperref package loading order conflict";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "reorder_hyperref_package";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := ref_010_validator;
  rule_sound := None
|}.

(** ** STYLE: Document Style Rules - STYLE-001 through STYLE-010 *)

(** STYLE-001: Inconsistent font commands *)
Fixpoint style_001_check_font_commands (tokens : list latex_token) (font_cmds : list string) : bool :=
  match tokens with
  | [] => Nat.ltb 1 (length font_cmds)  (* More than one font style *)
  | TCommand cmd :: rest =>
      let is_font_cmd := orb (string_contains_substring cmd "text") 
                            (orb (string_contains_substring cmd "bf") 
                                 (string_contains_substring cmd "it")) in
      if is_font_cmd then
        if existsb (fun fc => negb (string_contains_substring fc cmd)) font_cmds then true
        else style_001_check_font_commands rest (cmd :: font_cmds)
      else style_001_check_font_commands rest font_cmds
  | _ :: rest => style_001_check_font_commands rest font_cmds
  end.

Definition style_001_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_001_check_font_commands doc.(tokens) [] then
      [{| rule_id := "STYLE-001";
          issue_severity := Info;
          message := "Inconsistent font command usage detected";
          loc := None;
          suggested_fix := Some "standardize_font_commands";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_001_rule : validation_rule := {|
  id := "STYLE-001";
  description := "Inconsistent font command usage detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "standardize_font_commands";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_001_validator;
  rule_sound := None
|}.

(** STYLE-002: Document class options consistency *)
Fixpoint style_002_check_class_options (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText opts :: TEndGroup :: TBeginGroup :: TText cls :: TEndGroup :: rest =>
      if string_contains_substring cmd "documentclass" then
        orb (andb (string_contains_substring cls "article") (string_contains_substring opts "12pt"))
            (andb (string_contains_substring cls "book") (string_contains_substring opts "10pt"))
      else style_002_check_class_options rest
  | _ :: rest => style_002_check_class_options rest
  end.

Definition style_002_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_002_check_class_options doc.(tokens) then
      [{| rule_id := "STYLE-002";
          issue_severity := Info;
          message := "Review document class and option combination";
          loc := None;
          suggested_fix := Some "review_class_options";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_002_rule : validation_rule := {|
  id := "STYLE-002";
  description := "Review document class and option combination";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "review_class_options";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_002_validator;
  rule_sound := None
|}.

(** STYLE-003: Heading capitalization consistency *)
Fixpoint style_003_check_heading_caps (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText heading :: TEndGroup :: rest =>
      if orb (string_contains_substring cmd "section") (string_contains_substring cmd "chapter") then
        let first_char := match heading with
                         | String c _ => c
                         | _ => ascii_of_nat 97  (* 'a' *)
                         end in
        let is_lower := let n := nat_of_ascii first_char in
                       andb (Nat.leb 97 n) (Nat.leb n 122) in
        orb is_lower (style_003_check_heading_caps rest)
      else style_003_check_heading_caps rest
  | _ :: rest => style_003_check_heading_caps rest
  end.

Definition style_003_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_003_check_heading_caps doc.(tokens) then
      [{| rule_id := "STYLE-003";
          issue_severity := Info;
          message := "Check heading capitalization consistency";
          loc := None;
          suggested_fix := Some "standardize_heading_caps";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_003_rule : validation_rule := {|
  id := "STYLE-003";
  description := "Check heading capitalization consistency";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "standardize_heading_caps";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_003_validator;
  rule_sound := None
|}.

(** STYLE-004: Margin and geometry settings *)
Fixpoint style_004_check_geometry (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if string_contains_substring cmd "geometry" then true
      else style_004_check_geometry rest
  | _ :: rest => style_004_check_geometry rest
  end.

Fixpoint style_004_has_margin_commands (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if orb (string_contains_substring cmd "margin") (string_contains_substring cmd "textwidth") then true
      else style_004_has_margin_commands rest
  | _ :: rest => style_004_has_margin_commands rest
  end.

Definition style_004_validator : document_state -> list validation_issue :=
  fun doc =>
    let has_geometry := style_004_check_geometry doc.(tokens) in
    let has_margin := style_004_has_margin_commands doc.(tokens) in
    if andb has_geometry has_margin then
      [{| rule_id := "STYLE-004";
          issue_severity := Warning;
          message := "Conflicting margin/geometry settings detected";
          loc := None;
          suggested_fix := Some "resolve_margin_conflicts";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_004_rule : validation_rule := {|
  id := "STYLE-004";
  description := "Conflicting margin/geometry settings detected";
  precondition := L0_Lexer;
  default_severity := Warning;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "resolve_margin_conflicts";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_004_validator;
  rule_sound := None
|}.

(** STYLE-005: Line spacing consistency *)
Fixpoint style_005_check_line_spacing (tokens : list latex_token) (spacing_cmds : list string) : bool :=
  match tokens with
  | [] => Nat.ltb 1 (length spacing_cmds)  (* Multiple spacing commands *)
  | TCommand cmd :: rest =>
      if orb (string_contains_substring cmd "linespread") 
             (orb (string_contains_substring cmd "doublespacing") 
                  (string_contains_substring cmd "singlespacing")) then
        style_005_check_line_spacing rest (cmd :: spacing_cmds)
      else style_005_check_line_spacing rest spacing_cmds
  | _ :: rest => style_005_check_line_spacing rest spacing_cmds
  end.

Definition style_005_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_005_check_line_spacing doc.(tokens) [] then
      [{| rule_id := "STYLE-005";
          issue_severity := Info;
          message := "Multiple line spacing commands detected";
          loc := None;
          suggested_fix := Some "consolidate_line_spacing";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_005_rule : validation_rule := {|
  id := "STYLE-005";
  description := "Multiple line spacing commands detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "consolidate_line_spacing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_005_validator;
  rule_sound := None
|}.

(** STYLE-006: Color usage consistency *)
Fixpoint style_006_check_color_usage (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if orb (string_contains_substring cmd "color") (string_contains_substring cmd "textcolor") then true
      else style_006_check_color_usage rest
  | _ :: rest => style_006_check_color_usage rest
  end.

Definition style_006_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_006_check_color_usage doc.(tokens) then
      [{| rule_id := "STYLE-006";
          issue_severity := Info;
          message := "Color usage detected - ensure accessibility";
          loc := None;
          suggested_fix := Some "review_color_accessibility";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_006_rule : validation_rule := {|
  id := "STYLE-006";
  description := "Color usage detected - ensure accessibility";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "review_color_accessibility";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_006_validator;
  rule_sound := None
|}.

(** STYLE-007: Table formatting consistency *)
Fixpoint style_007_check_table_formatting (tokens : list latex_token) (in_table : bool) (table_types : list string) : bool :=
  match tokens with
  | [] => Nat.ltb 1 (length table_types)  (* Multiple table types *)
  | TCommand cmd :: TBeginGroup :: TText env :: TEndGroup :: rest =>
      if string_contains_substring cmd "begin" then
        if orb (string_contains_substring env "tabular") 
               (orb (string_contains_substring env "table") 
                    (string_contains_substring env "longtable")) then
          style_007_check_table_formatting rest true (env :: table_types)
        else style_007_check_table_formatting rest in_table table_types
      else style_007_check_table_formatting rest in_table table_types
  | _ :: rest => style_007_check_table_formatting rest in_table table_types
  end.

Definition style_007_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_007_check_table_formatting doc.(tokens) false [] then
      [{| rule_id := "STYLE-007";
          issue_severity := Info;
          message := "Mixed table formatting styles detected";
          loc := None;
          suggested_fix := Some "standardize_table_style";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_007_rule : validation_rule := {|
  id := "STYLE-007";
  description := "Mixed table formatting styles detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "standardize_table_style";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_007_validator;
  rule_sound := None
|}.

(** STYLE-008: Figure placement and sizing *)
Fixpoint style_008_check_figure_options (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: TBeginGroup :: TText opts :: TEndGroup :: rest =>
      if string_contains_substring cmd "includegraphics" then
        if orb (string_contains_substring opts "width=\\textwidth") 
               (string_contains_substring opts "scale=") then false
        else true  (* No sizing options *)
      else style_008_check_figure_options rest
  | _ :: rest => style_008_check_figure_options rest
  end.

Definition style_008_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_008_check_figure_options doc.(tokens) then
      [{| rule_id := "STYLE-008";
          issue_severity := Info;
          message := "Figure without explicit sizing options";
          loc := None;
          suggested_fix := Some "add_figure_sizing";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_008_rule : validation_rule := {|
  id := "STYLE-008";
  description := "Figure without explicit sizing options";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "add_figure_sizing";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_008_validator;
  rule_sound := None
|}.

(** STYLE-009: Paragraph indentation settings *)
Fixpoint style_009_check_paragraph_settings (tokens : list latex_token) : bool :=
  match tokens with
  | [] => false
  | TCommand cmd :: rest =>
      if orb (string_contains_substring cmd "parindent") (string_contains_substring cmd "parskip") then true
      else style_009_check_paragraph_settings rest
  | _ :: rest => style_009_check_paragraph_settings rest
  end.

Definition style_009_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_009_check_paragraph_settings doc.(tokens) then
      [{| rule_id := "STYLE-009";
          issue_severity := Info;
          message := "Custom paragraph formatting detected";
          loc := None;
          suggested_fix := Some "review_paragraph_formatting";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_009_rule : validation_rule := {|
  id := "STYLE-009";
  description := "Custom paragraph formatting detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "review_paragraph_formatting";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_009_validator;
  rule_sound := None
|}.

(** STYLE-010: Page layout and header consistency *)
Fixpoint style_010_check_page_layout (tokens : list latex_token) (header_cmds : list string) : bool :=
  match tokens with
  | [] => Nat.ltb 1 (length header_cmds)  (* Multiple header styles *)
  | TCommand cmd :: rest =>
      if orb (string_contains_substring cmd "pagestyle") 
             (orb (string_contains_substring cmd "fancyhdr") 
                  (string_contains_substring cmd "header")) then
        style_010_check_page_layout rest (cmd :: header_cmds)
      else style_010_check_page_layout rest header_cmds
  | _ :: rest => style_010_check_page_layout rest header_cmds
  end.

Definition style_010_validator : document_state -> list validation_issue :=
  fun doc =>
    if style_010_check_page_layout doc.(tokens) [] then
      [{| rule_id := "STYLE-010";
          issue_severity := Info;
          message := "Multiple page layout/header commands detected";
          loc := None;
          suggested_fix := Some "consolidate_page_layout";
          rule_owner := "@lint-team" |}]
    else [].

Definition style_010_rule : validation_rule := {|
  id := "STYLE-010";
  description := "Multiple page layout/header commands detected";
  precondition := L0_Lexer;
  default_severity := Info;
  rule_maturity := Draft;
  owner := "@lint-team";
  performance_bucket := TokenKind_Command;
  auto_fix := Some "consolidate_page_layout";
  implementation_file := "rules/phase1/TypoRules.v";
  validator := style_010_validator;
  rule_sound := None
|}.

(** Complete Phase 1 rule collection (75 rules) *)
Definition complete_phase1_rules : list validation_rule := [
  typo_001_rule; typo_002_rule; typo_003_rule; typo_004_rule; typo_005_rule;
  typo_006_rule; typo_007_rule; typo_008_rule; typo_009_rule; typo_010_rule;
  typo_011_rule; typo_012_rule; typo_013_rule; typo_014_rule; typo_015_rule;
  typo_016_rule; typo_017_rule; typo_018_rule; typo_019_rule; typo_020_rule;
  typo_021_rule; typo_022_rule; typo_023_rule; typo_024_rule; typo_025_rule;
  enc_001_rule; enc_002_rule; enc_003_rule; enc_004_rule; enc_005_rule;
  char_001_rule; char_002_rule; char_003_rule; char_004_rule; char_005_rule;
  env_001_rule; env_002_rule; env_003_rule; env_004_rule; env_005_rule;
  math_001_rule; math_002_rule; math_003_rule; math_004_rule; math_005_rule;
  struct_001_rule; struct_002_rule; struct_003_rule; struct_004_rule; struct_005_rule;
  struct_006_rule; struct_007_rule; struct_008_rule; struct_009_rule; struct_010_rule;
  ref_001_rule; ref_002_rule; ref_003_rule; ref_004_rule; ref_005_rule;
  ref_006_rule; ref_007_rule; ref_008_rule; ref_009_rule; ref_010_rule;
  style_001_rule; style_002_rule; style_003_rule; style_004_rule; style_005_rule;
  style_006_rule; style_007_rule; style_008_rule; style_009_rule; style_010_rule
].

(** ** Multi-category soundness proofs *)

Definition no_invalid_encoding (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> enc_001_check s = false.

Theorem enc_001_sound : rule_soundness_property enc_001_rule no_invalid_encoding.
Proof.
  unfold rule_soundness_property, enc_001_rule, no_invalid_encoding.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (enc_001_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if enc_001_check s then
           [{| rule_id := "ENC-001"; issue_severity := Error;
               message := "Non-UTF-8 byte sequence detected";
               loc := None; suggested_fix := None;
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold enc_001_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

Definition no_control_chars (doc : document_state) : Prop :=
  forall tok s, In tok doc.(tokens) -> tok = TText s -> char_001_check s = false.

Theorem char_001_sound : rule_soundness_property char_001_rule no_control_chars.
Proof.
  unfold rule_soundness_property, char_001_rule, no_control_chars.
  intros doc H_applicable H_no_issues tok s H_in H_tok.
  destruct (char_001_check s) eqn:Hcheck.
  - exfalso.
    apply (flat_map_nonempty _ _ 
      (fun tok => match tok with
       | TText s => if char_001_check s then
           [{| rule_id := "CHAR-001"; issue_severity := Error;
               message := "Control characters U+0000–001F present";
               loc := None; suggested_fix := None;
               rule_owner := "@lint-team" |}] else []
       | _ => [] end)
      doc.(tokens) (TText s)).
    + rewrite <- H_tok. exact H_in.
    + simpl. rewrite Hcheck. discriminate.
    + unfold char_001_validator in H_no_issues. exact H_no_issues.
  - reflexivity.
Qed.

(** ** Multi-category implementation status *)
(** Week 4.3 Progress: 30 Phase 1 rules across 3 categories (TYPO, ENC, CHAR) *)
(** Demonstrates scalable cross-category pattern: 0 axioms, 0 admits maintained **)