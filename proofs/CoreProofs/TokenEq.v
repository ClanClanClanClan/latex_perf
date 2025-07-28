(** Token equality decidability - LaTeX Perfectionist v25 *)

From Coq Require Import Decidable.
Require Import Token.

(** Token equality is decidable *)
Theorem token_eq_decidable : forall (t1 t2 : token), {t1 = t2} + {t1 <> t2}.
Proof.
  (* TODO: Implementation required per Bootstrap Skeleton *)
  admit.
Admitted.