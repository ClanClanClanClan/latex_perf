(* Catcode Coq Proofs - Week 1-2 Deliverable *)
(* LaTeX Perfectionist v25 - PLANNER.yaml Section 3.1.3 *)

From Coq Require Import Nat Bool List Arith Lia.
From Coq Require Import Decidable.
Import ListNotations.

(** LaTeX character category codes *)
Inductive catcode : Type :=
  | Escape      (* 0: Starts commands like \ *)
  | BeginGroup  (* 1: Begin group { *)
  | EndGroup    (* 2: End group } *)
  | MathShift   (* 3: Math mode $ *)
  | AlignTab    (* 4: Alignment & *)
  | EndLine     (* 5: Line ending *)
  | Param       (* 6: Parameter # *)
  | Superscript (* 7: Superscript ^ *)
  | Subscript   (* 8: Subscript _ *)
  | Ignored     (* 9: Ignored characters *)
  | Space       (* 10: Space characters *)
  | Letter      (* 11: Letters a-z A-Z *)
  | Other       (* 12: Other characters *)
  | Active      (* 13: Active characters *)
  | Comment     (* 14: Comment % *)
  | Invalid.    (* 15: Invalid characters *)

(** TeX engine types *)
Inductive engine : Type :=
  | PdfTeX 
  | XeTeX 
  | LuaTeX
  | ConTeXt
  | PlainTeX
  | ETeX
  | Omega
  | Aleph.

(** Convert catcode to nat for easier reasoning *)
Definition catcode_to_nat (c : catcode) : nat :=
  match c with
  | Escape => 0
  | BeginGroup => 1
  | EndGroup => 2
  | MathShift => 3
  | AlignTab => 4
  | EndLine => 5
  | Param => 6
  | Superscript => 7
  | Subscript => 8
  | Ignored => 9
  | Space => 10
  | Letter => 11
  | Other => 12
  | Active => 13
  | Comment => 14
  | Invalid => 15
  end.

(** Convert nat to catcode (partial function) *)
Definition nat_to_catcode (n : nat) : option catcode :=
  match n with
  | 0 => Some Escape
  | 1 => Some BeginGroup
  | 2 => Some EndGroup
  | 3 => Some MathShift
  | 4 => Some AlignTab
  | 5 => Some EndLine
  | 6 => Some Param
  | 7 => Some Superscript
  | 8 => Some Subscript
  | 9 => Some Ignored
  | 10 => Some Space
  | 11 => Some Letter
  | 12 => Some Other
  | 13 => Some Active
  | 14 => Some Comment
  | 15 => Some Invalid
  | _ => None
  end.

(** Theorem: catcode has decidable equality *)
Theorem catcode_eq_dec : forall (c1 c2 : catcode), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
Qed.

(** Theorem: catcode_to_nat is injective *)
Theorem catcode_to_nat_injective : forall c1 c2,
  catcode_to_nat c1 = catcode_to_nat c2 -> c1 = c2.
Proof.
  intros c1 c2.
  destruct c1; destruct c2; simpl; intro H;
  try reflexivity; try discriminate.
Qed.

(** Theorem: nat_to_catcode is left inverse of catcode_to_nat *)
Theorem nat_catcode_inverse : forall c,
  nat_to_catcode (catcode_to_nat c) = Some c.
Proof.
  intros c.
  destruct c; simpl; reflexivity.
Qed.

(** Theorem: catcode_to_nat produces values < 16 *)
Theorem catcode_to_nat_bounded : forall c,
  catcode_to_nat c < 16.
Proof.
  intros c.
  destruct c; simpl; lia.
Qed.

(** Default catcode lookup table for ASCII characters *)
Definition default_catcode_table : list (nat * catcode) :=
  (92, Escape) ::      (* \ *)
  (123, BeginGroup) :: (* { *)
  (125, EndGroup) ::   (* } *)
  (36, MathShift) ::   (* $ *)
  (38, AlignTab) ::    (* & *)
  (13, EndLine) ::     (* \r *)
  (10, EndLine) ::     (* \n *)
  (35, Param) ::       (* # *)
  (94, Superscript) :: (* ^ *)
  (95, Subscript) ::   (* _ *)
  (0, Ignored) ::      (* null *)
  (32, Space) ::       (* space *)
  (9, Space) ::        (* tab *)
  (37, Comment) ::     (* % *)
  nil.

(** Check if a character code is a letter in ASCII *)
Definition is_ascii_letter (n : nat) : bool :=
  ((65 <=? n) && (n <=? 90)) ||  (* A-Z *)
  ((97 <=? n) && (n <=? 122)).   (* a-z *)

(** Get catcode for ASCII character *)
Definition ascii_catcode (n : nat) : catcode :=
  match find (fun p => Nat.eqb (fst p) n) default_catcode_table with
  | Some (_, cat) => cat
  | None => 
      if is_ascii_letter n then Letter
      else if n <? 128 then Other
      else Invalid
  end.

(** Unicode letter ranges for XeTeX/LuaTeX *)
(* Suppress large number warnings for Unicode ranges *)
#[warnings="-abstract-large-number"]
Definition is_unicode_letter (code : nat) : bool :=
  (* Simplified for proof - actual implementation would check all ranges *)
  ((192 <=? code) && (code <=? 214)) ||    (* Latin-1 Supplement *)
  ((216 <=? code) && (code <=? 246)) ||    (* Latin-1 Supplement cont. *)
  ((248 <=? code) && (code <=? 767)) ||    (* Latin Extended-A, B *)
  ((880 <=? code) && (code <=? 893)) ||    (* Greek *)
  ((12289 <=? code) && (code <=? 55295)).  (* CJK *)

(** Main catcode lookup function *)
Definition catcode_of (eng : engine) (code : nat) : catcode :=
  if code <? 256 then
    ascii_catcode code
  else
    match eng with
    | XeTeX | LuaTeX =>
        if is_unicode_letter code then Letter
        else Other
    | _ => Invalid
    end.

(** Theorem: catcode_of is total (always returns a value) *)
Theorem catcode_of_total : forall eng code,
  exists c, catcode_of eng code = c.
Proof.
  intros eng code.
  exists (catcode_of eng code).
  reflexivity.
Qed.

(** Theorem: For ASCII range, all engines give same result *)
Theorem ascii_engine_independent : forall eng1 eng2 code,
  code < 256 ->
  catcode_of eng1 code = catcode_of eng2 code.
Proof.
  intros eng1 eng2 code H.
  unfold catcode_of.
  destruct (code <? 256) eqn:Hlt.
  - reflexivity.
  - apply Nat.ltb_lt in H.
    rewrite H in Hlt.
    discriminate.
Qed.

(** Helper: Check if n is in the list of special character codes *)
Definition is_special_char (n : nat) : bool :=
  match n with
  | 92 | 123 | 125 | 36 | 38 | 13 | 10 | 35 | 94 | 95 | 0 | 32 | 9 | 37 => true
  | _ => false
  end.

(** Lemma: ASCII letters are not special characters *)
Lemma ascii_letters_not_special : forall c,
  (65 <= c <= 90 \/ 97 <= c <= 122) ->
  is_special_char c = false.
Proof.
  intros c Hletter.
  destruct Hletter as [H_upper | H_lower];
  destruct c as [|c']; try lia;
  destruct c' as [|c'']; try lia;
  (* Continue case analysis until we reach the range *)
  repeat (destruct c'' as [|c'']; try lia);
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* 1.  A concise predicate for the ASCII–letter ranges               *)
(* ----------------------------------------------------------------- *)
Definition is_ascii_letter_prop (c : nat) : Prop :=
        65 <= c <= 90 \/ 97 <= c <= 122.

(* ----------------------------------------------------------------- *)
(* 2.  The *only* keys that appear in [default_catcode_table].       *)
(*     NOTE: if you ever touch the table, update this list ‑ CI      *)
(*     now checks that the two stay in perfect sync.                 *)
(* ----------------------------------------------------------------- *)
Definition default_catcode_keys : list nat :=
  [92; 123; 125; 36; 38; 13; 10; 35; 94; 95; 0; 32; 9; 37].

Lemma keys_exact :
  forall k v, In (k,v) default_catcode_table -> In k default_catcode_keys.
Proof.
  intros k v Hin.
  unfold default_catcode_table in Hin.
  repeat (destruct Hin as [H|Hin]; [injection H; intro; subst; simpl; auto 20 |]).
  destruct Hin.
Qed.

(* ----------------------------------------------------------------- *)
(* 3.  Range separation lemma – *none* of the table keys is a letter *)
(* ----------------------------------------------------------------- *)
Lemma key_not_letter :
  forall k, In k default_catcode_keys -> ~ is_ascii_letter_prop k.
Proof.
  intros k Hk Hin.
  unfold is_ascii_letter_prop in Hin.
  repeat
    (destruct Hk as [<-|Hk];
     [now (destruct Hin as [[? ?]|[? ?]]; lia) | ]).
  contradiction.
Qed.

(* ----------------------------------------------------------------- *)
(* 4.  FINAL LEMMA – previously admitted                             *)
(* ----------------------------------------------------------------- *)
Lemma ascii_letters_not_in_table :
  forall c,
    (65 <= c <= 90 \/ 97 <= c <= 122) ->
    find (fun p => Nat.eqb (fst p) c) default_catcode_table = None.
Proof.
  intros c Hc.
  change (65 <= c <= 90 \/ 97 <= c <= 122) with (is_ascii_letter_prop c) in Hc.
  (* Proof by contradiction: assume find returns Some, derive contradiction *)
  destruct (find (fun p => Nat.eqb (fst p) c) default_catcode_table) as [[k v]|] eqn:Hfind.
  - (* find returns Some (k,v) *)
    apply find_some in Hfind.
    destruct Hfind as [Hin Heqb].
    simpl in Heqb.
    apply Nat.eqb_eq in Heqb.
    (* k is in the table, so k is in default_catcode_keys *)
    pose proof (keys_exact _ _ Hin) as Hin_keys.
    (* But k = c and c is a letter, contradiction *)
    subst c.
    apply (key_not_letter _ Hin_keys) in Hc.
    contradiction.
  - (* find returns None - this is what we want *)
    reflexivity.
Qed.

(** Theorem: catcode_of preserves Letter for ASCII letters in all engines *)
Theorem ascii_letters_preserved : forall eng c,
  (65 <= c <= 90 \/ 97 <= c <= 122) ->
  catcode_of eng c = Letter.
Proof.
  intros eng c Hletter.
  (* ASCII letters always get catcode Letter regardless of engine *)
  
  unfold catcode_of.
  (* Since ASCII letters have c < 256, we use ascii_catcode *)
  assert (c < 256) as H_ascii.
  { destruct Hletter; lia. }
  
  (* Use ltb reflection *)
  assert (c <? 256 = true) as H_ltb.
  { apply Nat.ltb_lt. exact H_ascii. }
  
  rewrite H_ltb.
  
  (* Now we need to show ascii_catcode c = Letter *)
  unfold ascii_catcode.
  
  (* Use our lemma to show find returns None *)
  rewrite (ascii_letters_not_in_table c Hletter).
  simpl.
  
  (* Now check is_ascii_letter c *)
  unfold is_ascii_letter.
  
  (* Both uppercase and lowercase letters satisfy is_ascii_letter *)
  (* This follows from the definition of is_ascii_letter and the hypothesis *)
  destruct Hletter as [H_upper | H_lower].
  - (* Uppercase: 65 <= c <= 90 *)
    (* These satisfy the first disjunct of is_ascii_letter *)
    assert ((65 <=? c) && (c <=? 90) = true).
    { apply andb_true_intro. split; apply Nat.leb_le; lia. }
    rewrite H. reflexivity.
    
  - (* Lowercase: 97 <= c <= 122 *)
    (* These satisfy the second disjunct of is_ascii_letter *)
    assert ((97 <=? c) && (c <=? 122) = true) as H.
    { apply andb_true_intro. split; apply Nat.leb_le; lia. }
    (* The goal is ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)) *)
    (* We know the second part is true *)
    rewrite H.
    rewrite orb_comm. simpl. reflexivity.
Qed.

(** Engine equality is decidable *)
Theorem engine_eq_dec : forall (e1 e2 : engine), {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
Qed.

(** Module summary: 
    - Defined 16 catcode categories (0-15)
    - Defined 8 TeX engine types
    - Proved decidable equality for catcodes
    - Proved totality of catcode lookup function
    - Proved injectivity of catcode_to_nat
    - Proved boundedness of catcode values
    - Proved engine-independence for ASCII range
    - Proved ASCII letters preservation across engines
    
    Per PLANNER.yaml Section 3.4: "All proofs scaffolded; target Y1-Q2 to eliminate Admitted."
    Status: ✅ ALL PROOFS COMPLETE - 0 admits remaining
*)