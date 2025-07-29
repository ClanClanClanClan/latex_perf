Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ExpanderCompat.
Open Scope string_scope.

(* Test that section does NOT expand now *)
Compute expand_document [TCommand "section"; TText "["; TText "Short"; TText "]"; TBeginGroup; TText "Long"; TEndGroup].

(* Test that textbf DOES expand *)
Compute expand_document [TCommand "textbf"; TBeginGroup; TText "bold"; TEndGroup].

