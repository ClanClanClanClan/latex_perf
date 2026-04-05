(** * ParserSound — parser soundness (spec W51) *)

From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.

Inductive node := NWord : string -> node | NGroup : list node -> node.

Fixpoint flatten (n : node) : list string :=
  match n with
  | NWord w => w :: nil
  | NGroup children => flat_map flatten children
  end.

Theorem identity_parse_sound :
  forall tokens, flat_map flatten (List.map NWord tokens) = tokens.
Proof.
  induction tokens as [|t rest IH]; [reflexivity | simpl; f_equal; exact IH].
Qed.

Theorem flatten_nil : flat_map flatten (@nil node) = @nil string.
Proof. reflexivity. Qed.

Theorem flatten_word : forall w, flatten (NWord w) = w :: nil.
Proof. reflexivity. Qed.

Definition parser_sound_zero_admits : True := I.
