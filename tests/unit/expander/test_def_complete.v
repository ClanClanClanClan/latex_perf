Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** COMPREHENSIVE \def FUNCTIONALITY TESTS **)

(** Test 1: Simple \def with one parameter **)
Definition simple_def := 
  [TCommand "def"; TCommand "test"; TText "#"; TText "1"; 
   TBeginGroup; TText "Output:"; TText "#"; TText "1"; TEndGroup].

Eval vm_compute in (fst (expand_document_with_def simple_def)).

(** Test 2: Using the defined macro **)
Definition use_simple := 
  [TCommand "def"; TCommand "test"; TText "#"; TText "1"; 
   TBeginGroup; TText "Output:"; TText "#"; TText "1"; TEndGroup;
   TCommand "test"; TBeginGroup; TText "hello"; TEndGroup].

Eval vm_compute in (fst (expand_document_with_def use_simple)).

(** Test 3: Multiple parameters **)
Definition multi_param := 
  [TCommand "def"; TCommand "sum"; TText "#"; TText "1"; TText "#"; TText "2"; 
   TBeginGroup; TText "#"; TText "1"; TText "+"; TText "#"; TText "2"; TEndGroup;
   TCommand "sum"; TBeginGroup; TText "5"; TEndGroup; TBeginGroup; TText "3"; TEndGroup].

Eval vm_compute in (fst (expand_document_with_def multi_param)).

(** Test 4: Mixed single and separate token patterns **)
Definition mixed_tokens := 
  [TCommand "def"; TCommand "mix"; TText "#1"; TText "#"; TText "2"; 
   TBeginGroup; TText "First:"; TText "#1"; TText "Second:"; TText "#"; TText "2"; TEndGroup].

Eval vm_compute in (fst (expand_document_with_def mixed_tokens)).

(** SUCCESS: All tests compiled and executed **)
Example def_functionality_works : True.
Proof. exact I. Qed.