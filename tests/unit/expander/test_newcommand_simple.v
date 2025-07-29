Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderAlgorithm.
Open Scope string_scope.

(** Simple newcommand test **)

Definition simple_newcommand := 
  [TCommand "newcommand"; TBeginGroup; TCommand "test"; TEndGroup; 
   TBeginGroup; TText "output"; TEndGroup;
   TCommand "test"].

(* Use expand_spec instead of the missing expand_document_with_def *)
Eval vm_compute in (expand_spec 100 simple_newcommand).