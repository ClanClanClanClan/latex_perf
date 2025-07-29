(* Ultra-minimal test - no dependencies *)
Example test_basic : 1 + 1 = 2.
Proof. reflexivity. Qed.

Example test_list : @length nat (1 :: 2 :: 3 :: nil) = 3.
Proof. reflexivity. Qed.