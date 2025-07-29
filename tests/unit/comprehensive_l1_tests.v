Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Require Import Arith.
Require Import Lia.
Open Scope string_scope.

(** * COMPREHENSIVE L1 INTEGRATION TESTS *)
(** Tests combining all TIER 1-4 features *)

(** Test 1: Complex macro with parameters and protection *)
Example test_complex_macro_protection :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "title"; TText "#"; TText "1"; TBeginGroup; 
      TCommand "protect"; TCommand "section"; TBeginGroup; TText "#"; TText "1"; TEndGroup;
    TEndGroup;
    TCommand "title"; TBeginGroup; TText "Introduction"; TEndGroup
  ] in
  output = [TCommand "section"; TBeginGroup; TText "Introduction"; TEndGroup] /\
  length state.(errors) = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Test 2: Counters with macro expansion *)
Example test_counters_with_macros :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "chapter"; TEndGroup;
    TCommand "def"; TCommand "nextchapter"; TBeginGroup; 
      TCommand "stepcounter"; TBeginGroup; TCommand "chapter"; TEndGroup;
      TCommand "arabic"; TBeginGroup; TCommand "chapter"; TEndGroup;
    TEndGroup;
    TCommand "nextchapter"; TText "."; TCommand "nextchapter"
  ] in
  output = [TText "1"; TText "."; TText "2"] /\
  length state.(counters) = 1 /\
  length state.(errors) = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Test 3: \expandafter with counter operations *)
Example test_expandafter_counters :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "test"; TEndGroup;
    TCommand "def"; TCommand "getValue"; TBeginGroup; TCommand "arabic"; TBeginGroup; TCommand "test"; TEndGroup; TEndGroup;
    TCommand "expandafter"; TCommand "textbf"; TCommand "getValue"
  ] in
  output = [TCommand "begingroup"; TCommand "bfseries"; TText "0"; TCommand "endgroup"] /\
  length state.(errors) = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Test 4: \renewcommand with debug tracing *)
Example test_renewcommand_debug :
  let (output, state) := expand_document_with_debug [
    TCommand "def"; TCommand "test"; TBeginGroup; TText "OLD"; TEndGroup;
    TCommand "renewcommand"; TBeginGroup; TCommand "test"; TEndGroup; TBeginGroup; TText "NEW"; TEndGroup;
    TCommand "test"
  ] 2 in
  output = [TText "NEW"] /\
  length state.(debug_log) > 0 /\
  state.(debug_trace) = true /\
  length state.(errors) = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Test 5: Complex nested expansion with protection *)
Example test_nested_expansion_protection :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "outer"; TText "#"; TText "1"; TBeginGroup; 
      TCommand "protect"; TCommand "inner"; TBeginGroup; TText "#"; TText "1"; TEndGroup;
    TEndGroup;
    TCommand "def"; TCommand "inner"; TText "#"; TText "1"; TBeginGroup; 
      TCommand "textbf"; TBeginGroup; TText "#"; TText "1"; TEndGroup;
    TEndGroup;
    TCommand "outer"; TBeginGroup; TText "test"; TEndGroup
  ] in
  output = [TCommand "inner"; TBeginGroup; TText "test"; TEndGroup] /\
  length state.(errors) = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Test 6: All enterprise commands working together *)
Example test_enterprise_commands_integration :
  let (output, state) := expand_document_with_def [
    TCommand "newcommand"; TBeginGroup; TCommand "base"; TEndGroup; TBeginGroup; TText "BASE"; TEndGroup;
    TCommand "let"; TCommand "copy"; TCommand "base";
    TCommand "renewcommand"; TBeginGroup; TCommand "base"; TEndGroup; TBeginGroup; TText "RENEWED"; TEndGroup;
    TCommand "providecommand"; TBeginGroup; TCommand "new"; TEndGroup; TBeginGroup; TText "PROVIDED"; TEndGroup;
    TCommand "base"; TText "|"; TCommand "copy"; TText "|"; TCommand "new"
  ] in
  output = [TText "RENEWED"; TText "|"; TText "BASE"; TText "|"; TText "PROVIDED"] /\
  length state.(user_defined_macros) = 3 /\
  length state.(errors) = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Test 7: Error handling across all features *)
Example test_comprehensive_error_handling :
  let (output, state) := expand_document_with_def [
    TCommand "arabic"; TBeginGroup; TCommand "undefined"; TEndGroup;
    TCommand "expandafter"; TCommand "textbf";
    TCommand "renewcommand"; TBeginGroup; TCommand "missing"; TEndGroup;
    TCommand "stepcounter"; TBeginGroup; TCommand "notdefined"; TEndGroup
  ] in
  output = [TCommand "arabic"; TBeginGroup; TCommand "undefined"; TEndGroup;
           TCommand "expandafter"; TCommand "textbf";
           TCommand "renewcommand"; TBeginGroup; TCommand "missing"; TEndGroup;
           TCommand "stepcounter"; TBeginGroup; TCommand "notdefined"; TEndGroup] /\
  length state.(errors) = 4.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Summary: 7 comprehensive integration tests *)
Definition COMPREHENSIVE_L1_VERIFIED : string := 
  "✅ COMPREHENSIVE L1 INTEGRATION VERIFIED WITH 7 TESTS".