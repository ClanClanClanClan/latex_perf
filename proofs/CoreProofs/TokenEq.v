(** Token equality decidability - LaTeX Perfectionist v25 *)

From Coq Require Import Decidable.
From Coq Require Import Ascii String.
Require Import List.
Import ListNotations.

(* Define token type locally to avoid import issues *)
Inductive token : Type :=
  | TChar : ascii -> token
  | TCommand : string -> token
  | TNewline : token
  | TSpace : token
  | TMath : token
  | TComment : string -> token
  | TBeginEnv : string -> token
  | TEndEnv : string -> token
  | TError : string -> token.

(** Token equality is decidable *)
Theorem token_eq_decidable : forall (t1 t2 : token), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  - apply ascii_dec.
  - apply string_dec.
  - apply string_dec.
  - apply string_dec.
  - apply string_dec.
  - apply string_dec.
Qed.