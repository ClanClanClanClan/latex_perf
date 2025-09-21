From Coq Require Import List.
Import ListNotations.

(** Minimal predicate that every validator will instantiate. *)

Definition issue := nat.        (* placeholder *)

Definition detector_sound
           (detect : list nat -> list issue)
           (ground : list nat -> list issue) : Prop :=
  forall doc, incl (detect doc) (ground doc).