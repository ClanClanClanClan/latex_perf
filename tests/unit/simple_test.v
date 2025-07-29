(* Simple test to verify test framework *)

From Coq Require Import String List Bool Arith.
Import ListNotations.

(* Simple validator that always returns empty *)
Definition simple_validator (doc : string) : list nat := [].

(* Test that it returns empty *)
Example test_simple_validator_empty :
  simple_validator "any document" = [].
Proof. reflexivity. Qed.

(* Test with arithmetic to ensure Coq is working *)
Example test_arithmetic :
  2 + 2 = 4.
Proof. reflexivity. Qed.

(* Test list operations *)
Example test_list_length :
  length [1; 2; 3] = 3.
Proof. reflexivity. Qed.