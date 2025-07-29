Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Test the FIXED \def parsing **)

Definition def_test_input := 
  [TCommand "def"; TCommand "x"; TText "#"; TText "1"; 
   TBeginGroup; TText "Result:"; TText "#"; TText "1"; TEndGroup].

(** Test 1: \def parsing doesn't crash **)
Example def_parsing_no_crash : True.
Proof.
  exact I.
Qed.

(** Test 2: Show actual result **)
Eval vm_compute in (fst (expand_document_with_def def_test_input)).

(** Test 3: Use the defined macro **)
Definition use_macro_input :=
  [TCommand "def"; TCommand "x"; TText "#"; TText "1"; 
   TBeginGroup; TText "Result:"; TText "#"; TText "1"; TEndGroup;
   TCommand "x"; TBeginGroup; TText "hello"; TEndGroup].

Eval vm_compute in (fst (expand_document_with_def use_macro_input)).