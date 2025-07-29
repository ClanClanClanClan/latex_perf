Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.

(** Test if Coq decision procedures are really the issue *)

Definition simple_list := [TText "a"; TText "b"].
Definition same_list := [TText "a"; TText "b"].

(** Test simple list equality *)
Eval vm_compute in (if list_eq_dec latex_token_eq_dec simple_list same_list then "EQUAL" else "NOT EQUAL").

(** Test single token equality *)
Eval vm_compute in (if latex_token_eq_dec (TText "hello") (TText "hello") then "EQUAL" else "NOT EQUAL").