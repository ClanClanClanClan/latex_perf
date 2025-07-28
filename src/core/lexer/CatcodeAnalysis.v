(* Helper lemmas for catcode analysis *)

Require Import Bool Arith List String Ascii.
Require Import LatexCatcodes.
Require Import LatexLexer.

(* If a character has CatSpace catcode, then it's whitespace *)
Lemma catspace_is_whitespace : forall c,
  default_catcodes c = CatSpace -> is_whitespace c = true.
Proof.
  intros c H.
  (* Analyze the definition of default_catcodes *)
  unfold default_catcodes in H.
  (* Go through the decision tree *)
  destruct (ascii_dec c ascii_backslash); [discriminate|].
  destruct (ascii_dec c ascii_lbrace); [discriminate|].
  destruct (ascii_dec c ascii_rbrace); [discriminate|].
  destruct (ascii_dec c ascii_dollar); [discriminate|].
  destruct (ascii_dec c ascii_ampersand); [discriminate|].
  destruct (ascii_dec c ascii_hash); [discriminate|].
  destruct (ascii_dec c ascii_caret); [discriminate|].
  destruct (ascii_dec c ascii_underscore); [discriminate|].
  destruct (ascii_dec c ascii_space) as [H_eq|H_neq].
  - (* c = ascii_space *)
    subst c.
    unfold is_whitespace, ascii_space.
    simpl. reflexivity.
  - (* c ≠ ascii_space, continue checking *)
    destruct (ascii_dec c ascii_percent); [discriminate|].
    (* At this point, catcode depends on is_letter c *)
    destruct (is_letter c) eqn:E_letter.
    + (* is_letter c = true => CatLetter *)
      discriminate H.
    + (* is_letter c = false => CatOther *)
      discriminate H.
Qed.

(* If a character has CatComment catcode, then it's percent *)
Lemma catcomment_is_percent : forall c,
  default_catcodes c = CatComment -> c = ascii_percent.
Proof.
  intros c H.
  unfold default_catcodes in H.
  destruct (ascii_dec c ascii_backslash); [discriminate|].
  destruct (ascii_dec c ascii_lbrace); [discriminate|].
  destruct (ascii_dec c ascii_rbrace); [discriminate|].
  destruct (ascii_dec c ascii_dollar); [discriminate|].
  destruct (ascii_dec c ascii_ampersand); [discriminate|].
  destruct (ascii_dec c ascii_hash); [discriminate|].
  destruct (ascii_dec c ascii_caret); [discriminate|].
  destruct (ascii_dec c ascii_underscore); [discriminate|].
  destruct (ascii_dec c ascii_space); [discriminate|].
  destruct (ascii_dec c ascii_percent) as [H_eq|H_neq].
  - (* c = ascii_percent *)
    exact H_eq.
  - (* c ≠ ascii_percent *)
    destruct (is_letter c); discriminate H.
Qed.

(* If a character has CatEscape catcode, then it's backslash *)
Lemma catescape_is_backslash : forall c,
  default_catcodes c = CatEscape -> c = ascii_backslash.
Proof.
  intros c H.
  unfold default_catcodes in H.
  destruct (ascii_dec c ascii_backslash) as [H_eq|H_neq].
  - (* c = ascii_backslash *)
    exact H_eq.
  - (* c ≠ ascii_backslash *)
    destruct (ascii_dec c ascii_lbrace); [discriminate|].
    destruct (ascii_dec c ascii_rbrace); [discriminate|].
    destruct (ascii_dec c ascii_dollar); [discriminate|].
    destruct (ascii_dec c ascii_ampersand); [discriminate|].
    destruct (ascii_dec c ascii_hash); [discriminate|].
    destruct (ascii_dec c ascii_caret); [discriminate|].
    destruct (ascii_dec c ascii_underscore); [discriminate|].
    destruct (ascii_dec c ascii_space); [discriminate|].
    destruct (ascii_dec c ascii_percent); [discriminate|].
    destruct (is_letter c); discriminate H.
Qed.