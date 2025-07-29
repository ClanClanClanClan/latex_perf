(* VSNA Core Module - Foundational Types and Definitions *)
(* VSNA: Verified Streaming Nested Automaton Architecture *)

From Coq Require Import String Ascii Lists.List Bool.Bool Arith.Arith Nat.
Import ListNotations.

(** * Core VSNA Types *)

(** ** Rule Identification *)
Definition rule_id := nat.

(** ** Document Representation *)
Definition document := string.

(** ** Position Tracking *)
Definition position := nat.

(** ** Error Messages *)
Definition error_message := string.

(** ** Validation Results *)
Definition validation_result := list (rule_id * position * error_message).

(** ** Rule Categories for VSNA Architecture *)
Inductive rule_category : Type :=
  | CategoryA  (* Regular patterns - DFA processable *)
  | CategoryB  (* Balanced constructs - VPA processable *)
  | CategoryC  (* Context-sensitive - Symbol table processable *).

(** ** Rule Abstract Syntax *)
Inductive rule_pattern : Type :=
  | CharPattern : ascii -> rule_pattern
  | StringPattern : string -> rule_pattern
  | RegexPattern : string -> rule_pattern  (* Regex string to be compiled *)
  | BalancedPattern : ascii -> ascii -> rule_pattern  (* Open/close pairs *)
  | ContextPattern : string -> rule_pattern.  (* Context-sensitive patterns *)

Record rule : Type := {
  rule_identifier : rule_id;
  rule_name : string;
  rule_cat : rule_category;
  rule_pat : rule_pattern;
  rule_message : error_message;
  rule_enabled : bool
}.

(** ** VSNA Processing State *)
Record vsna_state : Type := {
  dfa_state : nat;
  vpa_stack : list nat;
  symbol_table : list (string * position);
  current_position : position
}.

(** ** Main VSNA Validation Function Signature *)
(** This will be implemented across DFA.v, VPA.v, and SymbolTable.v *)
Parameter validate_document : list rule -> document -> validation_result.

(** * Core VSNA Properties *)

(** ** Soundness: No false positives *)
Definition sound_validation (results : validation_result) (doc : document) (rules : list rule) : Prop :=
  forall (r_id : rule_id) (pos : position) (msg : error_message),
    In (r_id, pos, msg) results ->
    exists r, In r rules /\ rule_identifier r = r_id /\ rule_enabled r = true.

(** ** Completeness: No false negatives for covered rules *)
Definition complete_validation (results : validation_result) (doc : document) (rules : list rule) : Prop :=
  forall (r : rule) (pos : position),
    In r rules -> rule_enabled r = true ->
    exists msg, In (rule_identifier r, pos, msg) results.

(** ** Performance Bounds *)
Definition time_complexity (f : document -> validation_result) (doc : document) : nat :=
  String.length doc.  (* O(|doc|) target complexity *)

Definition memory_usage (rules : list rule) (doc : document) : nat :=
  length rules + String.length doc.  (* O(|rules| + |doc|) target memory *)

(** * VSNA Architecture Constants *)

(** Performance targets from VSNA specification *)
Definition VSNA_SLA_LATENCY : nat := 42.  (* 42ms for 30KB document *)
Definition VSNA_TARGET_RULES : nat := 600.  (* Target rule count *)
Definition VSNA_TEST_DOC_SIZE : nat := (30 * 1000).  (* 30KB test document *)

(** Phase gate targets *)
Definition PHASE1_RULE_COUNT : nat := 60.   (* Category A rules *)
Definition PHASE2_RULE_COUNT : nat := 120.  (* Category A + B rules *)
Definition PHASE3_RULE_COUNT : nat := 144.  (* All L0 rules *)

Definition PHASE1_LATENCY_TARGET : nat := 5.   (* 5ms for Phase 1 *)
Definition PHASE2_LATENCY_TARGET : nat := 10.  (* 10ms for Phase 2 *)
Definition PHASE3_LATENCY_TARGET : nat := 20.  (* 20ms for Phase 3 *)

(** * Utility Functions *)

(** ** Rule Filtering by Category *)
(* Equality function for rule categories *)
Definition rule_category_eqb (c1 c2 : rule_category) : bool :=
  match c1, c2 with
  | CategoryA, CategoryA => true
  | CategoryB, CategoryB => true
  | CategoryC, CategoryC => true
  | _, _ => false
  end.

Definition filter_rules_by_category (rules : list rule) (cat : rule_category) : list rule :=
  filter (fun r => rule_category_eqb (rule_cat r) cat) rules.

Definition category_a_rules (rules : list rule) : list rule :=
  filter_rules_by_category rules CategoryA.

Definition category_b_rules (rules : list rule) : list rule :=
  filter_rules_by_category rules CategoryB.

Definition category_c_rules (rules : list rule) : list rule :=
  filter_rules_by_category rules CategoryC.

(** ** Enabled Rule Filtering *)
Definition enabled_rules (rules : list rule) : list rule :=
  filter (fun r => rule_enabled r) rules.

(** ** Error Result Construction *)
Definition make_error (r_id : rule_id) (pos : position) (msg : error_message) : 
  rule_id * position * error_message :=
  (r_id, pos, msg).

(** * VSNA Core Lemmas *)

(** ** Basic Properties *)
Lemma filter_preserves_membership : forall (A : Type) (f : A -> bool) (l : list A) (x : A),
  In x (filter f l) -> In x l.
Proof.
  intros A f l x H.
  induction l as [|h t IH].
  - simpl in H. contradiction.
  - simpl in H.
    destruct (f h) eqn:Hf.
    + simpl in H. destruct H as [H | H].
      * left. assumption.
      * right. apply IH. assumption.
    + right. apply IH. assumption.
Qed.

Lemma enabled_rules_subset : forall rules,
  forall r, In r (enabled_rules rules) -> In r rules.
Proof.
  intros rules r H.
  unfold enabled_rules in H.
  apply filter_preserves_membership in H.
  assumption.
Qed.

(** * VSNA Core Extraction Setup *)
(** Extraction directives will be placed in extraction/Extract.v *)

(** * VSNA Phase 0 Foundation Complete *)
(** 
This module provides the complete foundation for VSNA implementation:

1. Core types: rule_id, document, validation_result
2. Rule categorization: CategoryA/B/C for three-pass processing
3. Performance targets and phase gate constants
4. Soundness and completeness property definitions
5. Utility functions for rule filtering and result construction

Phase 1 will implement:
- DFA compilation for Category A rules in DFA.v
- Multi-rule DFA execution and correctness proofs
- OCaml extraction for performance benchmarking

The VSNA architecture ensures O(bytes + nesting) complexity through:
- Phase 1: DFA for regular patterns (Category A)
- Phase 2: VPA for balanced constructs (Category B) 
- Phase 3: Symbol table for context-sensitive rules (Category C)
*)