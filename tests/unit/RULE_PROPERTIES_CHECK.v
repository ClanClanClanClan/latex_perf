Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import ValidationTypes.
Require Import TypoRules.
Open Scope string_scope.

(** Check actual rule properties **)
Compute typo_001_rule.(default_severity).
Compute typo_001_rule.(precondition).
Compute typo_001_rule.(id).
Compute typo_002_rule.(default_severity).
Compute typo_002_rule.(id).