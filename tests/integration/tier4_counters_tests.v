Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** * TIER 4 COUNTERS TESTS *)
(** Tests for counter management functionality *)

(** Test 1: \newcounter creates a new counter *)
Example test_newcounter_basic :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "test"; TEndGroup;
    TCommand "arabic"; TBeginGroup; TCommand "test"; TEndGroup
  ] in
  output = [TText "0"] /\
  length state.(counters) = 1 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 2: \setcounter sets counter value *)
Example test_setcounter_basic :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "test"; TEndGroup;
    TCommand "setcounter"; TBeginGroup; TCommand "test"; TEndGroup; TBeginGroup; TText "5"; TEndGroup;
    TCommand "arabic"; TBeginGroup; TCommand "test"; TEndGroup
  ] in
  output = [TText "5"] /\
  length state.(counters) = 1 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 3: \stepcounter increments counter *)
Example test_stepcounter_basic :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "test"; TEndGroup;
    TCommand "setcounter"; TBeginGroup; TCommand "test"; TEndGroup; TBeginGroup; TText "3"; TEndGroup;
    TCommand "stepcounter"; TBeginGroup; TCommand "test"; TEndGroup;
    TCommand "arabic"; TBeginGroup; TCommand "test"; TEndGroup
  ] in
  output = [TText "4"] /\
  length state.(counters) = 1 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 4: \newcounter with parent counter *)
Example test_newcounter_with_parent :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "parent"; TEndGroup;
    TCommand "newcounter"; TBeginGroup; TCommand "child"; TEndGroup; TText "["; TCommand "parent"; TText "]";
    TCommand "arabic"; TBeginGroup; TCommand "child"; TEndGroup
  ] in
  output = [TText "0"] /\
  length state.(counters) = 2 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 5: Counter error handling - undefined counter *)
Example test_counter_undefined_error :
  let (output, state) := expand_document_with_def [
    TCommand "arabic"; TBeginGroup; TCommand "undefined"; TEndGroup
  ] in
  output = [TCommand "arabic"; TBeginGroup; TCommand "undefined"; TEndGroup] /\
  length state.(errors) = 1.
Proof. reflexivity. Qed.

(** Test 6: Multiple counters working together *)
Example test_multiple_counters :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "a"; TEndGroup;
    TCommand "newcounter"; TBeginGroup; TCommand "b"; TEndGroup;
    TCommand "setcounter"; TBeginGroup; TCommand "a"; TEndGroup; TBeginGroup; TText "2"; TEndGroup;
    TCommand "setcounter"; TBeginGroup; TCommand "b"; TEndGroup; TBeginGroup; TText "7"; TEndGroup;
    TCommand "arabic"; TBeginGroup; TCommand "a"; TEndGroup;
    TText "+";
    TCommand "arabic"; TBeginGroup; TCommand "b"; TEndGroup
  ] in
  output = [TText "2"; TText "+"; TText "7"] /\
  length state.(counters) = 2 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Test 7: Counter value persistence *)
Example test_counter_persistence :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "persistent"; TEndGroup;
    TCommand "stepcounter"; TBeginGroup; TCommand "persistent"; TEndGroup;
    TCommand "stepcounter"; TBeginGroup; TCommand "persistent"; TEndGroup;
    TCommand "stepcounter"; TBeginGroup; TCommand "persistent"; TEndGroup;
    TCommand "arabic"; TBeginGroup; TCommand "persistent"; TEndGroup
  ] in
  output = [TText "3"] /\
  length state.(counters) = 1 /\
  length state.(errors) = 0.
Proof. reflexivity. Qed.

(** Summary: 7 tests covering TIER 4 counter functionality *)
Definition TIER_4_COUNTERS_VERIFIED : string := 
  "✅ TIER 4 COUNTER FEATURES VERIFIED WITH 7 TESTS".