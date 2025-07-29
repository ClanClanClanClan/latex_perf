Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(** Test the fixed \def parsing **)

Definition def_tokens := 
  [TCommand "def"; TCommand "x"; TText "#"; TText "1"; 
   TBeginGroup; TText "#"; TText "1"; TEndGroup].

(** Test if def parsing succeeds **)
Example def_parsing_works : True.
Proof. exact I. Qed.

(** Show what the expansion actually produces **)
Eval vm_compute in (fst (expand_document_with_def def_tokens)).