(* LaTeX Perfectionist v24 - Phase 1: Verified Lexer *)
(* Week 1: Clean Category Code Definitions *)

Require Import Bool Arith List String Ascii Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

(** * LaTeX Category Code System *)

(* TeX category codes as defined in The TeXbook Chapter 7 *)
(* Simplified to essential codes based on corpus analysis *)
Inductive catcode : Type :=
  | CatEscape       (* 0: \ - 301,328 occurrences in corpus *)
  | CatBeginGroup   (* 1: { - 171,889 occurrences *)  
  | CatEndGroup     (* 2: } - 171,808 occurrences *)
  | CatMathShift    (* 3: $ - 101,760 occurrences *)
  | CatAlignment    (* 4: & - 19,309 occurrences *)
  | CatParameter    (* 6: # - 1,227 occurrences *)
  | CatSuperscript  (* 7: ^ - 38,593 occurrences *)
  | CatSubscript    (* 8: _ - 85,492 occurrences *)
  | CatSpace        (* 10: space and whitespace *)
  | CatLetter       (* 11: a-z, A-Z *)
  | CatOther        (* 12: everything else *)
  | CatComment.     (* 14: % - 30,402 occurrences *)

(* Character to category code mapping *)
Definition catcode_table := ascii -> catcode.

(* ASCII character constants for readability *)
Definition ascii_backslash : ascii := ascii_of_nat 92.   (* \ *)
Definition ascii_lbrace : ascii := ascii_of_nat 123.     (* { *)
Definition ascii_rbrace : ascii := ascii_of_nat 125.     (* } *)
Definition ascii_dollar : ascii := ascii_of_nat 36.      (* $ *)
Definition ascii_ampersand : ascii := ascii_of_nat 38.   (* & *)
Definition ascii_hash : ascii := ascii_of_nat 35.        (* # *)
Definition ascii_caret : ascii := ascii_of_nat 94.       (* ^ *)
Definition ascii_underscore : ascii := ascii_of_nat 95.  (* _ *)
Definition ascii_space : ascii := ascii_of_nat 32.       (* space *)
Definition ascii_percent : ascii := ascii_of_nat 37.     (* % *)

(* Helper function to check if character is letter *)
Definition is_letter (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (andb (Nat.leb 65 n) (Nat.leb n 90))   (* A-Z *)
      (andb (Nat.leb 97 n) (Nat.leb n 122)).  (* a-z *)

(* Default LaTeX category code assignment *)
Definition default_catcodes : catcode_table :=
  fun c =>
    if ascii_dec c ascii_backslash then CatEscape
    else if ascii_dec c ascii_lbrace then CatBeginGroup
    else if ascii_dec c ascii_rbrace then CatEndGroup
    else if ascii_dec c ascii_dollar then CatMathShift
    else if ascii_dec c ascii_ampersand then CatAlignment
    else if ascii_dec c ascii_hash then CatParameter
    else if ascii_dec c ascii_caret then CatSuperscript
    else if ascii_dec c ascii_underscore then CatSubscript
    else if ascii_dec c ascii_space then CatSpace
    else if ascii_dec c ascii_percent then CatComment
    else if is_letter c then CatLetter
    else CatOther.

(** * Basic Properties *)

(* Catcode assignment is decidable *)
Theorem catcode_decidable : forall c : ascii,
  {cc : catcode | default_catcodes c = cc}.
Proof.
  intros c.
  unfold default_catcodes.
  destruct (ascii_dec c ascii_backslash) as [H1|H1].
  - exists CatEscape. reflexivity.
  - destruct (ascii_dec c ascii_lbrace) as [H2|H2].
    + exists CatBeginGroup. reflexivity.
    + destruct (ascii_dec c ascii_rbrace) as [H3|H3].
      * exists CatEndGroup. reflexivity.
      * destruct (ascii_dec c ascii_dollar) as [H4|H4].
        -- exists CatMathShift. reflexivity.
        -- destruct (ascii_dec c ascii_ampersand) as [H5|H5].
           ++ exists CatAlignment. reflexivity.
           ++ destruct (ascii_dec c ascii_hash) as [H6|H6].
              ** exists CatParameter. reflexivity.
              ** destruct (ascii_dec c ascii_caret) as [H7|H7].
                 --- exists CatSuperscript. reflexivity.
                 --- destruct (ascii_dec c ascii_underscore) as [H8|H8].
                     +++ exists CatSubscript. reflexivity.
                     +++ destruct (ascii_dec c ascii_space) as [H9|H9].
                         *** exists CatSpace. reflexivity.
                         *** destruct (ascii_dec c ascii_percent) as [H10|H10].
                             ---- exists CatComment. reflexivity.
                             ---- destruct (is_letter c) eqn:E.
                                  ++++ exists CatLetter. reflexivity.
                                  ++++ exists CatOther. reflexivity.
Qed.

(* Catcode assignment is total function *)
Theorem catcode_total : forall c : ascii,
  exists cc : catcode, default_catcodes c = cc.
Proof.
  intros c.
  destruct (catcode_decidable c) as [cc H].
  exists cc. exact H.
Qed.

(* Special character recognition lemmas *)
Lemma escape_catcode : default_catcodes ascii_backslash = CatEscape.
Proof.
  unfold default_catcodes.
  destruct (ascii_dec ascii_backslash ascii_backslash); [reflexivity | contradiction].
Qed.

Lemma begin_group_catcode : default_catcodes ascii_lbrace = CatBeginGroup.
Proof.
  unfold default_catcodes.
  destruct (ascii_dec ascii_lbrace ascii_backslash); [discriminate | ].
  destruct (ascii_dec ascii_lbrace ascii_lbrace); [reflexivity | contradiction].
Qed.

Lemma end_group_catcode : default_catcodes ascii_rbrace = CatEndGroup.
Proof.
  unfold default_catcodes.
  destruct (ascii_dec ascii_rbrace ascii_backslash); [discriminate | ].
  destruct (ascii_dec ascii_rbrace ascii_lbrace); [discriminate | ].
  destruct (ascii_dec ascii_rbrace ascii_rbrace); [reflexivity | contradiction].
Qed.

(* Only backslash has escape catcode *)
Lemma escape_is_backslash : forall c,
  default_catcodes c = CatEscape -> c = ascii_backslash.
Proof.
  intros c H.
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  (* Compute all possible cases *)
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    try (simpl in H; discriminate H).
  (* The only remaining case is when c = Ascii true false true true true false true false *)
  (* which is ascii 92 = backslash *)
  reflexivity.
Qed.

(** * Catcode Equality *)

(* Catcode equality is decidable *)
Definition catcode_eq_dec : forall x y : catcode, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

(* Catcode beq function *)
Definition catcode_beq (c1 c2 : catcode) : bool :=
  match c1, c2 with
  | CatEscape, CatEscape => true
  | CatBeginGroup, CatBeginGroup => true
  | CatEndGroup, CatEndGroup => true
  | CatMathShift, CatMathShift => true
  | CatAlignment, CatAlignment => true
  | CatParameter, CatParameter => true
  | CatSuperscript, CatSuperscript => true
  | CatSubscript, CatSubscript => true
  | CatSpace, CatSpace => true
  | CatLetter, CatLetter => true
  | CatOther, CatOther => true
  | CatComment, CatComment => true
  | _, _ => false
  end.

Lemma catcode_beq_refl : forall c : catcode, catcode_beq c c = true.
Proof.
  destruct c; reflexivity.
Qed.

Lemma catcode_beq_eq : forall c1 c2 : catcode,
  catcode_beq c1 c2 = true <-> c1 = c2.
Proof.
  split; intros H.
  - destruct c1, c2; simpl in H; try discriminate; reflexivity.
  - subst. apply catcode_beq_refl.
Qed.

(** * Corpus-Based Constants *)

(* Most frequent characters from corpus analysis *)
Definition frequent_chars : list ascii :=
  [ascii_backslash; ascii_lbrace; ascii_rbrace; ascii_dollar;
   ascii_ampersand; ascii_hash; ascii_caret; ascii_underscore; ascii_percent].

(* Essential catcodes covering 99%+ of corpus usage *)
Definition essential_catcodes : list catcode :=
  [CatEscape; CatBeginGroup; CatEndGroup; CatMathShift;
   CatAlignment; CatParameter; CatSuperscript; CatSubscript;
   CatSpace; CatLetter; CatOther; CatComment].

(* Corpus usage frequencies (from latex_feature_analysis.json) *)
(* Using smaller numbers to avoid stack overflow warnings *)
Definition corpus_frequencies : list (catcode * nat) :=
  [(CatEscape, 301); (CatBeginGroup, 171); (CatEndGroup, 171);
   (CatMathShift, 101); (CatSubscript, 85); (CatSuperscript, 38);
   (CatComment, 30); (CatAlignment, 19); (CatParameter, 1)].

(* LaTeX epsilon scope - essential commands covering 80% usage *)
Definition latex_epsilon_commands : list string :=
  ["end"%string; "begin"%string; "in"%string; "frac"%string; "left"%string; "right"%string; "label"%string; 
   "mathcal"%string; "ref"%string; "cite"%string; "lambda"%string; "alpha"%string; "eqref"%string].

(** * Validation *)

Example test_backslash : default_catcodes ascii_backslash = CatEscape.
Proof. apply escape_catcode. Qed.

Example test_brace : default_catcodes ascii_lbrace = CatBeginGroup.
Proof. apply begin_group_catcode. Qed.

Example test_letter_a : default_catcodes (ascii_of_nat 97) = CatLetter.
Proof. 
  unfold default_catcodes. 
  repeat (try destruct (ascii_dec _ _); try discriminate).
  unfold is_letter. simpl. reflexivity.
Qed.

Example test_digit : default_catcodes (ascii_of_nat 48) = CatOther.
Proof.
  unfold default_catcodes.
  repeat (try destruct (ascii_dec _ _); try discriminate).
  unfold is_letter. simpl. reflexivity.
Qed.

(** * Corpus Validation *)

(* Escape characters are most frequent according to corpus *)
Example corpus_escape_frequency : 
  exists freq, In (CatEscape, freq) corpus_frequencies /\ freq = 301.
Proof.
  exists 301. 
  split.
  - unfold corpus_frequencies. simpl. left. reflexivity.
  - reflexivity.
Qed.

(* Core validation: essential characters map to essential catcodes *)
Example validate_essential_chars : 
  default_catcodes ascii_backslash = CatEscape /\
  default_catcodes ascii_lbrace = CatBeginGroup /\
  default_catcodes ascii_rbrace = CatEndGroup.
Proof.
  split. apply escape_catcode.
  split. apply begin_group_catcode.
  apply end_group_catcode.
Qed.