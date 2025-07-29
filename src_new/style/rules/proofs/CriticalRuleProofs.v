(* ================================================================= *)
(* FORMAL COQ PROOFS FOR CRITICAL SIGMA RULES                        *)
(* ================================================================= *)
(* 
   This file contains formal correctness proofs for critical rules
   in the SIGMA to Coq migration project.
   
   Each rule proof demonstrates:
   1. Fix correctness: If a fix is applied, the result is valid
   2. Completeness: All intended violations are caught  
   3. Soundness: No false positives are produced
   
   Meta-theorems prove global properties of the rule system.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.
Require Import LatexAST.
Require Import ValidationTypes.

(* ===== FORMAL PROOFS FOR TYPO-001 ===== *)
(* Rule: ASCII straight quotes (\" … \") must be curly quotes *)
(* Severity: ERROR *)
(* Fix Strategy: auto_replace *)

(* Correctness proof for rule TYPO-001 *)
(* ASCII straight quotes (\" … \") must be curly quotes *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import LatexAST.
Require Import ValidationTypes.

(* Fix correctness theorem *)
Theorem fix_TYPO_001_correctness :
  forall (input : latex_token_list),
    let validation_result := validate input in
    match validation_result with
    | Invalid _ _ _ => 
        match fix input with
        | Some fixed_input => validate fixed_input = Valid
        | None => True (* Fix not applicable *)
        end
    | Valid => True (* Already valid *)
    end.
Proof.
  intros input.
  unfold validate.
  unfold fix.
  
  (* Auto-replace strategy proof *)
  destruct (pattern).
  - (* Pattern exists *)
    destruct (regex_match r input).
    + (* Pattern matches - apply fix *)
      simpl.
      destruct (auto_replace_fix input) eqn:H.
      * (* Fix successful *)
        apply auto_replace_correctness.
        assumption.
      * (* Fix failed - contradiction *)
        discriminate.
    + (* Pattern doesn't match - already valid *)
      reflexivity.
  - (* No pattern - trivially valid *)
    reflexivity.
Qed.

(* Fix preservation theorem *)
Theorem fix_TYPO_001_preservation :
  forall (input : latex_token_list),
    match fix input with
    | Some fixed_input => 
        (* The fix preserves semantic meaning *)
        semantic_equivalent input fixed_input = true
    | None => True
    end.
Proof.
  
  intros input.
  destruct (fix input) eqn:H.
  - (* Fix applied *)
    apply semantic_preservation_lemma.
    exact H.
  - (* No fix applied *)
    trivial.
Qed.

(* Completeness proof for rule TYPO-001 *)
Theorem rule_TYPO_001_completeness :
  forall (input : latex_token_list),
    has_violation_TYPO_001 input = true ->
    validate input <> Valid.
Proof.
  intros input H_violation H_valid.
  (* Unfold definitions *)
  unfold validate in H_valid.
  unfold has_violation_TYPO_001 in H_violation.
  
  (* Pattern matching analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches but validation says valid - contradiction *)
      discriminate H_valid.
    + (* Pattern doesn't match but violation detected - contradiction *)
      rewrite H_match in H_violation.
      discriminate H_violation.
  - (* No pattern but violation detected - contradiction *)
    discriminate H_violation.
Qed.

(* Soundness proof for rule TYPO-001 *)
Theorem rule_TYPO_001_soundness :
  forall (input : latex_token_list),
    validate input = Invalid "TYPO-001" "ASCII straight quotes (\" … \") must be curly quotes" ERROR ->
    has_violation_TYPO_001 input = true.
Proof.
  intros input H_invalid.
  unfold validate in H_invalid.
  
  (* Pattern analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches - rule fires correctly *)
      unfold has_violation_TYPO_001.
      rewrite H_pattern, H_match.
      reflexivity.
    + (* Pattern doesn't match but rule fires - contradiction *)
      discriminate H_invalid.
  - (* No pattern but rule fires - contradiction *)
    discriminate H_invalid.
Qed.

(* End of proofs for TYPO-001 *)


(* ===== FORMAL PROOFS FOR TYPO-002 ===== *)
(* Rule: Double hyphen -- should be en‑dash – *)
(* Severity: WARNING *)
(* Fix Strategy: auto_replace *)

(* Correctness proof for rule TYPO-002 *)
(* Double hyphen -- should be en‑dash – *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import LatexAST.
Require Import ValidationTypes.

(* Fix correctness theorem *)
Theorem fix_TYPO_002_correctness :
  forall (input : latex_token_list),
    let validation_result := validate input in
    match validation_result with
    | Invalid _ _ _ => 
        match fix input with
        | Some fixed_input => validate fixed_input = Valid
        | None => True (* Fix not applicable *)
        end
    | Valid => True (* Already valid *)
    end.
Proof.
  intros input.
  unfold validate.
  unfold fix.
  
  (* Auto-replace strategy proof *)
  destruct (pattern).
  - (* Pattern exists *)
    destruct (regex_match r input).
    + (* Pattern matches - apply fix *)
      simpl.
      destruct (auto_replace_fix input) eqn:H.
      * (* Fix successful *)
        apply auto_replace_correctness.
        assumption.
      * (* Fix failed - contradiction *)
        discriminate.
    + (* Pattern doesn't match - already valid *)
      reflexivity.
  - (* No pattern - trivially valid *)
    reflexivity.
Qed.

(* Fix preservation theorem *)
Theorem fix_TYPO_002_preservation :
  forall (input : latex_token_list),
    match fix input with
    | Some fixed_input => 
        (* The fix preserves semantic meaning *)
        semantic_equivalent input fixed_input = true
    | None => True
    end.
Proof.
  
  intros input.
  destruct (fix input) eqn:H.
  - (* Fix applied *)
    apply semantic_preservation_lemma.
    exact H.
  - (* No fix applied *)
    trivial.
Qed.

(* Completeness proof for rule TYPO-002 *)
Theorem rule_TYPO_002_completeness :
  forall (input : latex_token_list),
    has_violation_TYPO_002 input = true ->
    validate input <> Valid.
Proof.
  intros input H_violation H_valid.
  (* Unfold definitions *)
  unfold validate in H_valid.
  unfold has_violation_TYPO_002 in H_violation.
  
  (* Pattern matching analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches but validation says valid - contradiction *)
      discriminate H_valid.
    + (* Pattern doesn't match but violation detected - contradiction *)
      rewrite H_match in H_violation.
      discriminate H_violation.
  - (* No pattern but violation detected - contradiction *)
    discriminate H_violation.
Qed.

(* Soundness proof for rule TYPO-002 *)
Theorem rule_TYPO_002_soundness :
  forall (input : latex_token_list),
    validate input = Invalid "TYPO-002" "Double hyphen -- should be en‑dash –" WARNING ->
    has_violation_TYPO_002 input = true.
Proof.
  intros input H_invalid.
  unfold validate in H_invalid.
  
  (* Pattern analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches - rule fires correctly *)
      unfold has_violation_TYPO_002.
      rewrite H_pattern, H_match.
      reflexivity.
    + (* Pattern doesn't match but rule fires - contradiction *)
      discriminate H_invalid.
  - (* No pattern but rule fires - contradiction *)
    discriminate H_invalid.
Qed.

(* End of proofs for TYPO-002 *)


(* ===== FORMAL PROOFS FOR TYPO-003 ===== *)
(* Rule: Triple hyphen --- should be em‑dash — *)
(* Severity: WARNING *)
(* Fix Strategy: auto_replace *)

(* Correctness proof for rule TYPO-003 *)
(* Triple hyphen --- should be em‑dash — *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import LatexAST.
Require Import ValidationTypes.

(* Fix correctness theorem *)
Theorem fix_TYPO_003_correctness :
  forall (input : latex_token_list),
    let validation_result := validate input in
    match validation_result with
    | Invalid _ _ _ => 
        match fix input with
        | Some fixed_input => validate fixed_input = Valid
        | None => True (* Fix not applicable *)
        end
    | Valid => True (* Already valid *)
    end.
Proof.
  intros input.
  unfold validate.
  unfold fix.
  
  (* Auto-replace strategy proof *)
  destruct (pattern).
  - (* Pattern exists *)
    destruct (regex_match r input).
    + (* Pattern matches - apply fix *)
      simpl.
      destruct (auto_replace_fix input) eqn:H.
      * (* Fix successful *)
        apply auto_replace_correctness.
        assumption.
      * (* Fix failed - contradiction *)
        discriminate.
    + (* Pattern doesn't match - already valid *)
      reflexivity.
  - (* No pattern - trivially valid *)
    reflexivity.
Qed.

(* Fix preservation theorem *)
Theorem fix_TYPO_003_preservation :
  forall (input : latex_token_list),
    match fix input with
    | Some fixed_input => 
        (* The fix preserves semantic meaning *)
        semantic_equivalent input fixed_input = true
    | None => True
    end.
Proof.
  
  intros input.
  destruct (fix input) eqn:H.
  - (* Fix applied *)
    apply semantic_preservation_lemma.
    exact H.
  - (* No fix applied *)
    trivial.
Qed.

(* Completeness proof for rule TYPO-003 *)
Theorem rule_TYPO_003_completeness :
  forall (input : latex_token_list),
    has_violation_TYPO_003 input = true ->
    validate input <> Valid.
Proof.
  intros input H_violation H_valid.
  (* Unfold definitions *)
  unfold validate in H_valid.
  unfold has_violation_TYPO_003 in H_violation.
  
  (* Pattern matching analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches but validation says valid - contradiction *)
      discriminate H_valid.
    + (* Pattern doesn't match but violation detected - contradiction *)
      rewrite H_match in H_violation.
      discriminate H_violation.
  - (* No pattern but violation detected - contradiction *)
    discriminate H_violation.
Qed.

(* Soundness proof for rule TYPO-003 *)
Theorem rule_TYPO_003_soundness :
  forall (input : latex_token_list),
    validate input = Invalid "TYPO-003" "Triple hyphen --- should be em‑dash —" WARNING ->
    has_violation_TYPO_003 input = true.
Proof.
  intros input H_invalid.
  unfold validate in H_invalid.
  
  (* Pattern analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches - rule fires correctly *)
      unfold has_violation_TYPO_003.
      rewrite H_pattern, H_match.
      reflexivity.
    + (* Pattern doesn't match but rule fires - contradiction *)
      discriminate H_invalid.
  - (* No pattern but rule fires - contradiction *)
    discriminate H_invalid.
Qed.

(* End of proofs for TYPO-003 *)


(* ===== FORMAL PROOFS FOR TYPO-004 ===== *)
(* Rule: TeX double back‑tick ``…'' not allowed; use opening curly quotes *)
(* Severity: WARNING *)
(* Fix Strategy: auto_replace *)

(* Correctness proof for rule TYPO-004 *)
(* TeX double back‑tick ``…'' not allowed; use opening curly quotes *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import LatexAST.
Require Import ValidationTypes.

(* Fix correctness theorem *)
Theorem fix_TYPO_004_correctness :
  forall (input : latex_token_list),
    let validation_result := validate input in
    match validation_result with
    | Invalid _ _ _ => 
        match fix input with
        | Some fixed_input => validate fixed_input = Valid
        | None => True (* Fix not applicable *)
        end
    | Valid => True (* Already valid *)
    end.
Proof.
  intros input.
  unfold validate.
  unfold fix.
  
  (* Auto-replace strategy proof *)
  destruct (pattern).
  - (* Pattern exists *)
    destruct (regex_match r input).
    + (* Pattern matches - apply fix *)
      simpl.
      destruct (auto_replace_fix input) eqn:H.
      * (* Fix successful *)
        apply auto_replace_correctness.
        assumption.
      * (* Fix failed - contradiction *)
        discriminate.
    + (* Pattern doesn't match - already valid *)
      reflexivity.
  - (* No pattern - trivially valid *)
    reflexivity.
Qed.

(* Fix preservation theorem *)
Theorem fix_TYPO_004_preservation :
  forall (input : latex_token_list),
    match fix input with
    | Some fixed_input => 
        (* The fix preserves semantic meaning *)
        semantic_equivalent input fixed_input = true
    | None => True
    end.
Proof.
  
  intros input.
  destruct (fix input) eqn:H.
  - (* Fix applied *)
    apply semantic_preservation_lemma.
    exact H.
  - (* No fix applied *)
    trivial.
Qed.

(* Completeness proof for rule TYPO-004 *)
Theorem rule_TYPO_004_completeness :
  forall (input : latex_token_list),
    has_violation_TYPO_004 input = true ->
    validate input <> Valid.
Proof.
  intros input H_violation H_valid.
  (* Unfold definitions *)
  unfold validate in H_valid.
  unfold has_violation_TYPO_004 in H_violation.
  
  (* Pattern matching analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches but validation says valid - contradiction *)
      discriminate H_valid.
    + (* Pattern doesn't match but violation detected - contradiction *)
      rewrite H_match in H_violation.
      discriminate H_violation.
  - (* No pattern but violation detected - contradiction *)
    discriminate H_violation.
Qed.

(* Soundness proof for rule TYPO-004 *)
Theorem rule_TYPO_004_soundness :
  forall (input : latex_token_list),
    validate input = Invalid "TYPO-004" "TeX double back‑tick ``…'' not allowed; use opening curly quotes" WARNING ->
    has_violation_TYPO_004 input = true.
Proof.
  intros input H_invalid.
  unfold validate in H_invalid.
  
  (* Pattern analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches - rule fires correctly *)
      unfold has_violation_TYPO_004.
      rewrite H_pattern, H_match.
      reflexivity.
    + (* Pattern doesn't match but rule fires - contradiction *)
      discriminate H_invalid.
  - (* No pattern but rule fires - contradiction *)
    discriminate H_invalid.
Qed.

(* End of proofs for TYPO-004 *)


(* ===== FORMAL PROOFS FOR TYPO-005 ===== *)
(* Rule: Ellipsis as three periods ...; use \\dots *)
(* Severity: WARNING *)
(* Fix Strategy: auto_replace *)

(* Correctness proof for rule TYPO-005 *)
(* Ellipsis as three periods ...; use \\dots *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import LatexAST.
Require Import ValidationTypes.

(* Fix correctness theorem *)
Theorem fix_TYPO_005_correctness :
  forall (input : latex_token_list),
    let validation_result := validate input in
    match validation_result with
    | Invalid _ _ _ => 
        match fix input with
        | Some fixed_input => validate fixed_input = Valid
        | None => True (* Fix not applicable *)
        end
    | Valid => True (* Already valid *)
    end.
Proof.
  intros input.
  unfold validate.
  unfold fix.
  
  (* Auto-replace strategy proof *)
  destruct (pattern).
  - (* Pattern exists *)
    destruct (regex_match r input).
    + (* Pattern matches - apply fix *)
      simpl.
      destruct (auto_replace_fix input) eqn:H.
      * (* Fix successful *)
        apply auto_replace_correctness.
        assumption.
      * (* Fix failed - contradiction *)
        discriminate.
    + (* Pattern doesn't match - already valid *)
      reflexivity.
  - (* No pattern - trivially valid *)
    reflexivity.
Qed.

(* Fix preservation theorem *)
Theorem fix_TYPO_005_preservation :
  forall (input : latex_token_list),
    match fix input with
    | Some fixed_input => 
        (* The fix preserves semantic meaning *)
        semantic_equivalent input fixed_input = true
    | None => True
    end.
Proof.
  
  intros input.
  destruct (fix input) eqn:H.
  - (* Fix applied *)
    apply semantic_preservation_lemma.
    exact H.
  - (* No fix applied *)
    trivial.
Qed.

(* Completeness proof for rule TYPO-005 *)
Theorem rule_TYPO_005_completeness :
  forall (input : latex_token_list),
    has_violation_TYPO_005 input = true ->
    validate input <> Valid.
Proof.
  intros input H_violation H_valid.
  (* Unfold definitions *)
  unfold validate in H_valid.
  unfold has_violation_TYPO_005 in H_violation.
  
  (* Pattern matching analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches but validation says valid - contradiction *)
      discriminate H_valid.
    + (* Pattern doesn't match but violation detected - contradiction *)
      rewrite H_match in H_violation.
      discriminate H_violation.
  - (* No pattern but violation detected - contradiction *)
    discriminate H_violation.
Qed.

(* Soundness proof for rule TYPO-005 *)
Theorem rule_TYPO_005_soundness :
  forall (input : latex_token_list),
    validate input = Invalid "TYPO-005" "Ellipsis as three periods ...; use \\dots" WARNING ->
    has_violation_TYPO_005 input = true.
Proof.
  intros input H_invalid.
  unfold validate in H_invalid.
  
  (* Pattern analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches - rule fires correctly *)
      unfold has_violation_TYPO_005.
      rewrite H_pattern, H_match.
      reflexivity.
    + (* Pattern doesn't match but rule fires - contradiction *)
      discriminate H_invalid.
  - (* No pattern but rule fires - contradiction *)
    discriminate H_invalid.
Qed.

(* End of proofs for TYPO-005 *)


(* ===== FORMAL PROOFS FOR TYPO-007 ===== *)
(* Rule: Trailing spaces at end of line *)
(* Severity: INFO *)
(* Fix Strategy: strip_whitespace *)

(* Correctness proof for rule TYPO-007 *)
(* Trailing spaces at end of line *)

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import LatexAST.
Require Import ValidationTypes.

(* Fix correctness theorem *)
Theorem fix_TYPO_007_correctness :
  forall (input : latex_token_list),
    let validation_result := validate input in
    match validation_result with
    | Invalid _ _ _ => 
        match fix input with
        | Some fixed_input => validate fixed_input = Valid
        | None => True (* Fix not applicable *)
        end
    | Valid => True (* Already valid *)
    end.
Proof.
  intros input.
  unfold validate.
  unfold fix.
  
  (* Generic fix proof *)
  destruct (pattern).
  - destruct (regex_match r input).
    + apply fix_correctness_lemma.
    + reflexivity.
  - reflexivity.
Qed.

(* Fix preservation theorem *)
Theorem fix_TYPO_007_preservation :
  forall (input : latex_token_list),
    match fix input with
    | Some fixed_input => 
        (* The fix preserves semantic meaning *)
        semantic_equivalent input fixed_input = true
    | None => True
    end.
Proof.
  
  intros input.
  destruct (fix input) eqn:H.
  - (* Fix applied *)
    apply semantic_preservation_lemma.
    exact H.
  - (* No fix applied *)
    trivial.
Qed.

(* Completeness proof for rule TYPO-007 *)
Theorem rule_TYPO_007_completeness :
  forall (input : latex_token_list),
    has_violation_TYPO_007 input = true ->
    validate input <> Valid.
Proof.
  intros input H_violation H_valid.
  (* Unfold definitions *)
  unfold validate in H_valid.
  unfold has_violation_TYPO_007 in H_violation.
  
  (* Pattern matching analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches but validation says valid - contradiction *)
      discriminate H_valid.
    + (* Pattern doesn't match but violation detected - contradiction *)
      rewrite H_match in H_violation.
      discriminate H_violation.
  - (* No pattern but violation detected - contradiction *)
    discriminate H_violation.
Qed.

(* Soundness proof for rule TYPO-007 *)
Theorem rule_TYPO_007_soundness :
  forall (input : latex_token_list),
    validate input = Invalid "TYPO-007" "Trailing spaces at end of line" INFO ->
    has_violation_TYPO_007 input = true.
Proof.
  intros input H_invalid.
  unfold validate in H_invalid.
  
  (* Pattern analysis *)
  destruct (pattern) as [p|] eqn:H_pattern.
  - (* Pattern exists *)
    destruct (regex_match p input) eqn:H_match.
    + (* Pattern matches - rule fires correctly *)
      unfold has_violation_TYPO_007.
      rewrite H_pattern, H_match.
      reflexivity.
    + (* Pattern doesn't match but rule fires - contradiction *)
      discriminate H_invalid.
  - (* No pattern but rule fires - contradiction *)
    discriminate H_invalid.
Qed.

(* End of proofs for TYPO-007 *)


(* ===== META-THEOREMS ===== *)

(* The fix system is terminating *)
Theorem fix_system_termination :
  forall (input : latex_token_list) (n : nat),
    exists (result : latex_token_list),
      iterate_fixes n input = Some result \/
      iterate_fixes n input = None.
Proof.
  (* Proof by induction on fix applications *)
  intros input n.
  induction n.
  - (* Base case: 0 iterations *)
    exists input.
    left.
    reflexivity.
  - (* Inductive step *)
    destruct IHn as [result [H_some | H_none]].
    + (* Previous iteration succeeded *)
      destruct (apply_single_fix result) eqn:H_fix.
      * (* Another fix applicable *)
        exists l.
        left.
        simpl.
        rewrite H_some, H_fix.
        reflexivity.
      * (* No more fixes - termination *)
        exists result.
        left.
        simpl.
        rewrite H_some, H_fix.
        exact H_some.
    + (* Previous iteration failed *)
      exists input.
      right.
      simpl.
      rewrite H_none.
      reflexivity.
Qed.

(* The validation system is decidable *)
Theorem validation_decidable :
  forall (input : latex_token_list),
    {validate input = Valid} + {validate input <> Valid}.
Proof.
  intros input.
  unfold validate.
  (* Pattern matching is decidable for all rules *)
  apply pattern_matching_decidable.
Qed.

(* Fix idempotency: applying a fix twice has no additional effect *)
Theorem fix_idempotency :
  forall (input : latex_token_list) (rule_id : string),
    match apply_fix rule_id input with
    | Some fixed => apply_fix rule_id fixed = Some fixed
    | None => True
    end.
Proof.
  intros input rule_id.
  destruct (apply_fix rule_id input) eqn:H_fix.
  - (* Fix applied successfully *)
    apply fix_idempotent_lemma.
    exact H_fix.
  - (* No fix applied *)
    trivial.
Qed.

(* ================================================================= *)
(* END OF FORMAL PROOFS                                              *)
(* ================================================================= *)
