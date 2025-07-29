Require Import String.
Require Import List.
Import ListNotations.
Require Import core.lexer.LatexLexer.
Require Import core.expander.LatexExpanderEnhanced.
Open Scope string_scope.

(** MINIMAL TESTS TO VERIFY BASIC FUNCTIONALITY *)

(** Test 1: Most basic expansion *)
Example test_basic_expansion :
  let (output, state) := expand_document_with_def [TCommand "LaTeX"] in
  output = [TText "LaTeX"].
Proof. vm_compute. reflexivity. Qed.

(** Test 2: Simple def *)
Example test_simple_def :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "test"; TBeginGroup; TText "HELLO"; TEndGroup;
    TCommand "test"
  ] in
  output = [TText "HELLO"].
Proof. vm_compute. reflexivity. Qed.

(** Test 3: Basic counter *)
Example test_basic_counter :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "test"; TEndGroup
  ] in
  length state.(counters) = 1.
Proof. vm_compute. reflexivity. Qed.

(** Test 4: Multi-digit counter *)
Example test_multidigit_counter :
  let (output, state) := expand_document_with_def [
    TCommand "newcounter"; TBeginGroup; TCommand "page"; TEndGroup;
    TCommand "setcounter"; TBeginGroup; TCommand "page"; TEndGroup; TBeginGroup; TText "123"; TEndGroup;
    TCommand "arabic"; TBeginGroup; TCommand "page"; TEndGroup
  ] in
  output = [TText "123"].
Proof. vm_compute. reflexivity. Qed.

(** Test 5: \expandafter *)
Example test_expandafter :
  let (output, state) := expand_document_with_def [
    TCommand "expandafter"; TCommand "textbf"; TCommand "LaTeX"
  ] in
  output = [TCommand "textbf"; TText "LaTeX"].
Proof. vm_compute. reflexivity. Qed.

(** Test 6: \protect *)
Example test_protect :
  let (output, state) := expand_document_with_def [
    TCommand "protect"; TCommand "section"; TBeginGroup; TText "Title"; TEndGroup
  ] in
  output = [TCommand "section"; TBeginGroup; TText "Title"; TEndGroup].
Proof. vm_compute. reflexivity. Qed.

(** Test 7: \renewcommand *)
Example test_renewcommand :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "test"; TBeginGroup; TText "OLD"; TEndGroup;
    TCommand "renewcommand"; TBeginGroup; TCommand "test"; TEndGroup; TBeginGroup; TText "NEW"; TEndGroup;
    TCommand "test"
  ] in
  output = [TText "NEW"].
Proof. vm_compute. reflexivity. Qed.

(** Test 8: \let *)
Example test_let :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "orig"; TBeginGroup; TText "ORIG"; TEndGroup;
    TCommand "let"; TCommand "copy"; TCommand "orig";
    TCommand "copy"
  ] in
  output = [TText "ORIG"].
Proof. vm_compute. reflexivity. Qed.

(** Test 9: Parameter substitution *)
Example test_param_subst :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "#"; TText "1"; TBeginGroup; 
      TText "Hello "; TText "#"; TText "1"; TText "!";
    TEndGroup;
    TCommand "test"; TBeginGroup; TText "World"; TEndGroup
  ] in
  output = [TText "Hello "; TText "World"; TText "!"].
Proof. vm_compute. reflexivity. Qed.

(** Test 10: Delimited parameters *)
Example test_delimited_params :
  let (output, state) := expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "to"; TText "#"; TText "1"; TBeginGroup; 
      TText "#"; TText "1";
    TEndGroup;
    TCommand "test"; TText "A"; TText "B"; TText "C"; TText "to"; TText "END"
  ] in
  output = [TText "A"; TText "B"; TText "C"; TText "END"].
Proof. vm_compute. reflexivity. Qed.

(** Summary: 10 minimal passing tests *)
Definition MINIMAL_TESTS_VERIFIED : string := 
  "✅ 10 MINIMAL TESTS PASS - BASIC FUNCTIONALITY VERIFIED".