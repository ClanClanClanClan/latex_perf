Require Import String List.
Import ListNotations.
Require Import LatexLexer.
Require Import LatexExpanderEnhanced.
Require Import LatexExpanderUltimate.
Open Scope string_scope.

(** Test cases to expose exponential complexity *)

(** Test 1: Simple single \def - should work fast *)
Definition simple_def_test : list latex_token := [
  TCommand "def"; TCommand "x"; TBeginGroup; TText "hi"; TEndGroup;
  TCommand "x"
].

(** Test 2: Nested macro definitions - potential exponential issue *)
Definition nested_def_test : list latex_token := [
  TCommand "def"; TCommand "a"; TBeginGroup; TCommand "b"; TEndGroup;
  TCommand "def"; TCommand "b"; TBeginGroup; TCommand "c"; TEndGroup;
  TCommand "def"; TCommand "c"; TBeginGroup; TText "result"; TEndGroup;
  TCommand "a"
].

(** Test 3: Multiple parameter substitution - complexity stress test *)
Definition multi_param_test : list latex_token := [
  TCommand "def"; TCommand "complex"; TText "#1"; TText "#2"; TText "#1"; TText "#2"; 
  TBeginGroup; TText "#1"; TCommand "x"; TText "#2"; TCommand "y"; TText "#1"; TEndGroup;
  TCommand "complex"; TBeginGroup; TText "arg1"; TEndGroup; TBeginGroup; TText "arg2"; TEndGroup
].

(** Test 4: Recursive definition pattern - should trigger infinite expansion protection *)
Definition recursive_pattern_test : list latex_token := [
  TCommand "def"; TCommand "loop"; TBeginGroup; TCommand "loop"; TText "text"; TEndGroup;
  TCommand "loop"
].

(** Enhanced vs Ultimate timing comparison *)
Goal True.
Proof.
(* Simple test - both should be fast *)
Timeout 1 Eval compute in expand_document_with_def simple_def_test.
Timeout 1 Eval compute in expand_document_ultimate simple_def_test.

(* Nested test - check for differences *)
Timeout 2 Eval compute in expand_document_with_def nested_def_test.
Timeout 2 Eval compute in expand_document_ultimate nested_def_test.

trivial.
Qed.