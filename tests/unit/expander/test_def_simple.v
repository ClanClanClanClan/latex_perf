Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Test \def parsing with vm_compute **)

Definition test_input := 
  [TCommand "def"; TCommand "mycommand"; TText "#"; TText "1"; 
   TBeginGroup; TText "Result:"; TText "#"; TText "1"; TEndGroup].

(** Test the expansion **)
Example def_parsing_test : True.
Proof. exact I. Qed.

(** Display the actual result **)
Eval vm_compute in (fst (expand_document_with_def test_input)).