Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** * TIER 3 PROTECTION TESTS *)
(** Tests for \protect and \expandafter functionality *)

(** Test 1: \protect prevents expansion of protected macros *)
Example test_protect_blocks_expansion :
  let (output, state) := expand_document_with_def [
    TCommand "protect"; TCommand "section"; TBeginGroup; TText "title"; TEndGroup
  ] in
  output = [TCommand "section"; TBeginGroup; TText "title"; TEndGroup] /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 2: \protect allows expansion of non-protected macros *)
Example test_protect_allows_non_protected :
  let (output, state) := expand_document_with_def [
    TCommand "protect"; TCommand "LaTeX"
  ] in
  output = [TText "LaTeX"] /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 3: \expandafter basic functionality *)
Example test_expandafter_basic :
  let (output, state) := expand_document_with_def [
    TCommand "expandafter"; TCommand "textbf"; TCommand "LaTeX"
  ] in
  output = [TCommand "begingroup"; TCommand "bfseries"; TText "LaTeX"; TCommand "endgroup"] /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 4: \expandafter with user-defined macros *)
Example test_expandafter_user_macro :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "test"; TBeginGroup; TText "TEST"; TEndGroup;
    TCommand "expandafter"; TCommand "textbf"; TCommand "test"
  ] in
  output = [TCommand "begingroup"; TCommand "bfseries"; TText "TEST"; TCommand "endgroup"] /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 5: \expandafter error handling *)
Example test_expandafter_insufficient_tokens :
  let (output, state) := expand_document_with_def [
    TCommand "expandafter"; TCommand "textbf"
  ] in
  output = [TCommand "expandafter"; TCommand "textbf"] /\
  length state.(errors) = 1.
Proof. reflexivity. Qed.

(** Test 6: Protection level nesting *)
Example test_protection_nesting :
  let (output, state) := expand_document_with_def [
    TCommand "protect"; TCommand "protect"; TCommand "section"; TBeginGroup; TText "title"; TEndGroup
  ] in
  output = [TCommand "section"; TBeginGroup; TText "title"; TEndGroup] /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 7: Mixed \protect and \expandafter *)
Example test_mixed_protect_expandafter :
  let (output, state) := expand_document_with_def [
    TCommand "protect"; TCommand "expandafter"; TCommand "section"; TCommand "LaTeX"
  ] in
  output = [TCommand "expandafter"; TCommand "section"; TText "LaTeX"] /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Summary: 7 tests covering TIER 3 protection and expansion control *)
Definition TIER_3_PROTECT_VERIFIED : string := 
  "✅ TIER 3 PROTECTION FEATURES VERIFIED WITH 7 TESTS".