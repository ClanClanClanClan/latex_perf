Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer ExpanderAlgorithm.
Open Scope string_scope.

(* Test 
ewcommand with required args *)
Definition test_newcommand_basic := [
  TCommand "newcommand"; TBeginGroup; TCommand "mytitle"; TEndGroup; 
  TText "["; TText "1"; TText "]";
  TBeginGroup; TCommand "textbf"; TBeginGroup; TText "#1"; TEndGroup; TEndGroup;
  TCommand "mytitle"; TBeginGroup; TText "Hello"; TEndGroup
].

Compute expand_v24 (100, test_newcommand_basic).

(* Test 
ewcommand with optional default *)
Definition test_newcommand_optional := [
  TCommand "newcommand"; TBeginGroup; TCommand "greet"; TEndGroup; 
  TText "["; TText "2"; TText "]"; TText "["; TText "Hi"; TText "]";
  TBeginGroup; TText "#1"; TText " "; TText "#2"; TEndGroup;
  TCommand "greet"; TBeginGroup; TText "World"; TEndGroup
].

Compute expand_v24 (100, test_newcommand_optional).

