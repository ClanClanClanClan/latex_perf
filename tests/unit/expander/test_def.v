Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(* Test \def functionality *)
Definition test_def := [
  TCommand "def"; TCommand "mycommand"; TText "#1"; TText "#2"; 
  TBeginGroup; TText "First: "; TText "#1"; TText ", Second: "; TText "#2"; TEndGroup;
  TCommand "mycommand"; TBeginGroup; TText "hello"; TEndGroup; TBeginGroup; TText "world"; TEndGroup
].

Compute expand_document_with_def test_def.

