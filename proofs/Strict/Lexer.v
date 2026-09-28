(** * Strict.Lexer — TeX's reader, from the bytes of a file to its tokens.

    ADR-012, milestone M2 phase 2 (docs/v27/STRICT_TIER_DESIGN.md §A.2: "the
    lexer works bytes -> tokens under the fixed catcode table ... It strips
    comments exactly as TeX does, and turns a blank line into par").  Phase 1
    (Syntax.v .. Bridge.v) decided documents given as TREES and printed by
    [render]; a user's file is arbitrary bytes.  This file is the first half
    of closing that gap: a DECLARATIVE model of how pdfTeX, as built by TeX
    Live, reads a file ([LexFile]), an executable lexer ([lex]) and the proof
    that they agree in both directions ([lex_exact]).  Front.v maps the tokens
    to the kernel's token stream; DecideBytes.v decides the bytes.

    What is modelled (tex.web, parts 20-24, and TeX Live's [input_line]):
    - LINES ([Lines]): TeX Live ends a line at LF, at CR, and at CR LF; a
      last line without a terminator is a line; the empty remainder after a
      final terminator is not (texmfmp.c [input_line]).  Trailing SPACE bytes
      (byte 32 only) are removed and [\endlinechar] is appended (tex.web
      §31, §362).
    - STATES N/M/S ([LineLex]): every line starts in state N; a character of
      category 10 is skipped in states N and S and is one space token in
      state M (then S); a category-5 character ends the line and is a [\par]
      token in state N, a space in state M, nothing in state S (§347-348); a
      comment character discards the rest of the line, the end-of-line
      character included (§347); letters and others are character tokens
      (state M); a control word is the escape character and a maximal run of
      letters (state S after it), a control symbol the escape character and
      one non-letter (state S after a category-10 one, M otherwise;
      §354-356).
    - THE FIRST LINE ([FirstLine]): before pdfTeX reads anything, TeX Live
      reads the first line of the main file, and if its first two bytes are
      [%&] loads the format (or TCX file) it names (texmfmp.c
      [parse_first_line]; MEASURED: [%&latex] gives rc 0 and NO PDF, the
      DVI-producing format; [%&etex] gives "Undefined control sequence" on
      line 2; a space or tab before the [%] disables it).  Such a file is
      outside the fragment (correction C-89).
    - OUTSIDE the fragment, as a token [RBad] that stops the line (Front.v
      then has no rule for it): a character of category 4 (&), 6 (#), 9
      (ignored), 13 (active: ~, byte 12 and every byte >= 128 in [article])
      or 15 (invalid: bytes 0 and 127), TeX's [^^] notation (a category-7
      character followed by the same character, anywhere, including after
      the escape character and after a control word's letters: TeX would
      reduce it, §352-356), an escape character with nothing after it on the
      line, and a line longer than [max_line_bytes] (TeX Live stops with
      "Unable to read an entire line" beyond its buffer).  Being outside is
      never a verdict: DecideBytes.v answers NotStrict.

    Nothing is hand-coded about the configuration.  The category of every
    byte, [\endlinechar] and the structural names come from the lexical
    contract [lexcon], a PARAMETER of every theorem; its runtime value is the
    generated file corpora/contracts/strict/article-s0-lexical.json, which
    scripts/tools/gen_strict_lexical.py dumps from the pinned image at body
    start of [article].  The only constants here are TeX Live's line
    terminators LF and CR and the byte it trims (space), all properties of
    the engine's input routine, not of the format.

    Probe families.  Every constructor below cites [probe L0/<constructor>]:
    the documents of that family in corpora/strict_s0/bytes_probes.json,
    graded by the pinned oracle through the extracted decider
    (scripts/tools/strict_differential.py --bytes-rules). *)

From Coq Require Import List Ascii Bool Arith Lia.
Import ListNotations.
From LaTeXPerfectionist.Strict Require Import Syntax Decide.

(** ** The lexical contract *)

(** TeX's sixteen category codes, in TeX's order (0 .. 15). *)
Inductive cat :=
| CEscape | CBgroup | CEgroup | CMath | CAlign | CEol | CParam | CSup | CSub
| CIgnored | CSpacer | CLetter | COther | CActive | CComment | CInvalid.

Definition cat_eqb (a b : cat) : bool :=
  match a, b with
  | CEscape, CEscape | CBgroup, CBgroup | CEgroup, CEgroup | CMath, CMath
  | CAlign, CAlign | CEol, CEol | CParam, CParam | CSup, CSup | CSub, CSub
  | CIgnored, CIgnored | CSpacer, CSpacer | CLetter, CLetter | COther, COther
  | CActive, CActive | CComment, CComment | CInvalid, CInvalid => true
  | _, _ => false
  end.

Lemma cat_eqb_eq : forall a b, cat_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

(** The configuration's reading regime at body start, and the names the
    front matter and the body's structure are made of (Front.v).  All of it
    is generated data (see the header). *)
Record lexcon := mkLex {
  lx_cat : ascii -> cat;          (* \catcode of every byte *)
  lx_endline : option ascii;      (* \endlinechar; None when outside 0..255 *)
  lx_par : name;                  (* the token of an empty line (tex.web par_loc) *)
  lx_end : name;                  (* \end *)
  lx_begin : name;                (* \begin *)
  lx_docclass : name;             (* \documentclass *)
  lx_class : list ascii;          (* the configuration's class *)
  lx_docenv : list ascii;         (* the document environment's name *)
  lx_mopen_inline : ascii;        (* the control symbols of the four *)
  lx_mclose_inline : ascii;       (* math delimiters of Syntax.tok    *)
  lx_mopen_display : ascii;
  lx_mclose_display : ascii
}.

(** ** Raw tokens *)

Inductive bad :=
| BadCat        (* a character of a category outside the fragment *)
| BadHatHat     (* TeX's ^^ notation *)
| BadNullCs     (* an escape character with nothing after it *)
| BadLongLine   (* a line longer than max_line_bytes *)
| BadFirstLine. (* a first line starting with %& (TeX Live's parse_first_line) *)

Inductive rtok :=
| RChar (c : ascii)     (* category 11 or 12 *)
| RSpace
| RPar                  (* the par token of an empty line *)
| RBgroup | REgroup | RMath | RSup | RSub
| RWord (n : name)      (* control word *)
| RSym (c : ascii)      (* control symbol *)
| RBad (why : bad).

(** A token with the line it was read on (1-based) and the offset of its
    first byte in the file (0-based). *)
Record lt := mkLt { lt_tok : rtok; lt_line : nat; lt_off : nat }.

(** ** Lines (TeX Live's input_line) *)

(* The bytes TeX Live's input routine treats specially: LF, CR, space. *)
Definition lf : ascii := ascii_of_nat 10.
Definition cr : ascii := ascii_of_nat 13.
Definition sp : ascii := ascii_of_nat 32.
(* Kept folded by [simpl], so that proofs reason about them symbolically. *)
Arguments lf : simpl never.
Arguments cr : simpl never.
Arguments sp : simpl never.

Definition not_term (c : ascii) : Prop := c <> lf /\ c <> cr.

(** Bytes paired with their offsets. *)
Fixpoint index (o : nat) (l : list ascii) : list (ascii * nat) :=
  match l with
  | [] => []
  | c :: r => (c, o) :: index (S o) r
  end.

(** A line: its bytes with their offsets, and the offset of its terminator
    (the end of the file for a last line without one), which is the offset
    given to the appended end-of-line character. *)
Definition line := (list (ascii * nat) * nat)%type.

Inductive Lines : nat -> list ascii -> list line -> Prop :=
(* probe L0/Lines_nil: the empty remainder after the last terminator is not
   a line. *)
| Lines_nil : forall o, Lines o [] []
(* probe L0/Lines_lf *)
| Lines_lf : forall o l rest ls,
    Forall not_term l ->
    Lines (o + length l + 1) rest ls ->
    Lines o (l ++ lf :: rest) ((index o l, o + length l) :: ls)
(* probe L0/Lines_crlf: CR LF is ONE terminator (measured: CR LF CR LF in
   math is one blank line, "Missing $ inserted" on the empty line). *)
| Lines_crlf : forall o l rest ls,
    Forall not_term l ->
    Lines (o + length l + 2) rest ls ->
    Lines o (l ++ cr :: lf :: rest) ((index o l, o + length l) :: ls)
(* probe L0/Lines_cr: CR alone ends a line. *)
| Lines_cr : forall o l rest ls,
    Forall not_term l ->
    hd_error rest <> Some lf ->
    Lines (o + length l + 1) rest ls ->
    Lines o (l ++ cr :: rest) ((index o l, o + length l) :: ls)
(* probe L0/Lines_last: a last line without a terminator is a line. *)
| Lines_last : forall o l,
    Forall not_term l -> l <> [] ->
    Lines o l [(index o l, o + length l)].

(** Trailing spaces removed (only byte 32, as TeX Live's input_line). *)
Fixpoint rtrim (l : list (ascii * nat)) : list (ascii * nat) :=
  match l with
  | [] => []
  | p :: r =>
      match rtrim r with
      | [] => if Ascii.eqb (fst p) sp then [] else [p]
      | r' => p :: r'
      end
  end.

(** The buffer TeX tokenizes for a line: the trimmed bytes, then
    [\endlinechar] at the terminator's offset. *)
Definition buffer (L : lexcon) (l : list (ascii * nat)) (eo : nat) : list (ascii * nat) :=
  rtrim l ++ match lx_endline L with Some e => [(e, eo)] | None => [] end.

(** ** One line, states N/M/S *)

Inductive lstate := SN | SM | SS.

(** TeX's [^^] test at a category-7 character [c] (§355): the next byte is
    [c] itself.  (TeX also needs a byte after that; with [\endlinechar]
    appended there always is one.  Treating every such pair as outside is
    conservative.) *)
Definition hathat (L : lexcon) (c : ascii) (rest : list (ascii * nat)) : bool :=
  cat_eqb (lx_cat L c) CSup
  && match rest with (d, _) :: _ => Ascii.eqb d c | [] => false end.

Definition is_letter (L : lexcon) (p : ascii * nat) : Prop := lx_cat L (fst p) = CLetter.

(** The byte after a control word's letters ends the word, and does not
    start a [^^] that TeX would read as part of the name (§356). *)
Definition word_end (L : lexcon) (rest : list (ascii * nat)) : Prop :=
  match rest with
  | [] => True
  | (d, _) :: r => lx_cat L d <> CLetter /\ hathat L d r = false
  end.

Definition bad_cat (k : cat) : bool :=
  match k with CAlign | CParam | CIgnored | CActive | CInvalid => true | _ => false end.

Definition sym_state (L : lexcon) (c : ascii) : lstate :=
  if cat_eqb (lx_cat L c) CSpacer then SS else SM.

Inductive LineLex (L : lexcon) (ln : nat) : lstate -> list (ascii * nat) -> list lt -> Prop :=
(* probe L0/LL_end: the buffer is exhausted. *)
| LL_end : forall st, LineLex L ln st [] []
(* probe L0/LL_eol_new: an end-of-line character in state N (an empty or
   blank line): the par token; the rest of the line is discarded. *)
| LL_eol_new : forall c o rest,
    lx_cat L c = CEol -> LineLex L ln SN ((c, o) :: rest) [mkLt RPar ln o]
(* probe L0/LL_eol_mid: in state M: one space token. *)
| LL_eol_mid : forall c o rest,
    lx_cat L c = CEol -> LineLex L ln SM ((c, o) :: rest) [mkLt RSpace ln o]
(* probe L0/LL_eol_skip: in state S (after a space or a control word):
   nothing. *)
| LL_eol_skip : forall c o rest,
    lx_cat L c = CEol -> LineLex L ln SS ((c, o) :: rest) []
(* probe L0/LL_space_skip: a category-10 character (space, tab) in state N
   or S is skipped. *)
| LL_space_skip : forall st c o rest out,
    lx_cat L c = CSpacer -> st <> SM ->
    LineLex L ln st rest out -> LineLex L ln st ((c, o) :: rest) out
(* probe L0/LL_space_emit: in state M it is one space token, then state S
   (a run of spaces is one space). *)
| LL_space_emit : forall c o rest out,
    lx_cat L c = CSpacer ->
    LineLex L ln SS rest out ->
    LineLex L ln SM ((c, o) :: rest) (mkLt RSpace ln o :: out)
(* probe L0/LL_comment: the rest of the line, its end-of-line character
   included, is discarded (so a comment joins two lines). *)
| LL_comment : forall st c o rest,
    lx_cat L c = CComment -> LineLex L ln st ((c, o) :: rest) []
(* probe L0/LL_char: a letter or an other character. *)
| LL_char : forall st c o rest out,
    (lx_cat L c = CLetter \/ lx_cat L c = COther) ->
    LineLex L ln SM rest out ->
    LineLex L ln st ((c, o) :: rest) (mkLt (RChar c) ln o :: out)
(* probe L0/LL_bgroup *)
| LL_bgroup : forall st c o rest out,
    lx_cat L c = CBgroup -> LineLex L ln SM rest out ->
    LineLex L ln st ((c, o) :: rest) (mkLt RBgroup ln o :: out)
(* probe L0/LL_egroup *)
| LL_egroup : forall st c o rest out,
    lx_cat L c = CEgroup -> LineLex L ln SM rest out ->
    LineLex L ln st ((c, o) :: rest) (mkLt REgroup ln o :: out)
(* probe L0/LL_math *)
| LL_math : forall st c o rest out,
    lx_cat L c = CMath -> LineLex L ln SM rest out ->
    LineLex L ln st ((c, o) :: rest) (mkLt RMath ln o :: out)
(* probe L0/LL_sub *)
| LL_sub : forall st c o rest out,
    lx_cat L c = CSub -> LineLex L ln SM rest out ->
    LineLex L ln st ((c, o) :: rest) (mkLt RSub ln o :: out)
(* probe L0/LL_sup: a category-7 character not followed by itself. *)
| LL_sup : forall st c o rest out,
    lx_cat L c = CSup -> hathat L c rest = false ->
    LineLex L ln SM rest out ->
    LineLex L ln st ((c, o) :: rest) (mkLt RSup ln o :: out)
(* probe L0/LL_hathat: ^^ (outside the fragment). *)
| LL_hathat : forall st c o rest,
    lx_cat L c = CSup -> hathat L c rest = true ->
    LineLex L ln st ((c, o) :: rest) [mkLt (RBad BadHatHat) ln o]
(* probe L0/LL_word: the escape character, a maximal run of letters, then
   state S (the spaces and the end of the line after a control word produce
   nothing). *)
| LL_word : forall st e o w rest out,
    lx_cat L e = CEscape -> w <> [] -> Forall (is_letter L) w ->
    word_end L rest ->
    LineLex L ln SS rest out ->
    LineLex L ln st ((e, o) :: w ++ rest) (mkLt (RWord (map fst w)) ln o :: out)
(* probe L0/LL_word_hathat: ^^ right after a control word's letters (TeX
   would read it as part of the name; outside the fragment). *)
| LL_word_hathat : forall st e o w d od rest,
    lx_cat L e = CEscape -> w <> [] -> Forall (is_letter L) w ->
    hathat L d rest = true ->
    LineLex L ln st ((e, o) :: w ++ (d, od) :: rest) [mkLt (RBad BadHatHat) ln o]
(* probe L0/LL_sym: the escape character and one non-letter: a control
   symbol; state S after a category-10 one, M otherwise. *)
| LL_sym : forall st e o c oc rest out,
    lx_cat L e = CEscape -> lx_cat L c <> CLetter -> hathat L c rest = false ->
    LineLex L ln (sym_state L c) rest out ->
    LineLex L ln st ((e, o) :: (c, oc) :: rest) (mkLt (RSym c) ln o :: out)
(* probe L0/LL_sym_hathat: the escape character then ^^ (outside). *)
| LL_sym_hathat : forall st e o c oc rest,
    lx_cat L e = CEscape -> hathat L c rest = true ->
    LineLex L ln st ((e, o) :: (c, oc) :: rest) [mkLt (RBad BadHatHat) ln o]
(* probe L0/LL_nullcs: the escape character last in the buffer (outside). *)
| LL_nullcs : forall st e o,
    lx_cat L e = CEscape -> LineLex L ln st [(e, o)] [mkLt (RBad BadNullCs) ln o]
(* probe L0/LL_bad: a character of category 4, 6, 9, 13 or 15 (outside). *)
| LL_bad : forall st c o rest,
    bad_cat (lx_cat L c) = true ->
    LineLex L ln st ((c, o) :: rest) [mkLt (RBad BadCat) ln o].

(** ** The file *)

(** TeX Live's buffer holds 200,000 bytes; a longer line stops pdflatex
    ("Unable to read an entire line", measured: rc 1 at 300,000 bytes,
    rc 0 at 150,000).  The fragment admits lines of at most 10,000 bytes
    (the bound is attested by the probe family L0/bounds). *)
Definition max_line_bytes : nat := Nat.mul ten (Nat.mul ten (Nat.mul ten ten)).

Example max_line_bytes_is_10000 : max_line_bytes = Nat.mul 100 100.
Proof. reflexivity. Qed.

Definition line_start (l : list (ascii * nat)) (eo : nat) : nat :=
  match l with (_, o) :: _ => o | [] => eo end.

Inductive LinesLex (L : lexcon) : nat -> list line -> list lt -> Prop :=
(* probe L0/LX_nil *)
| LX_nil : forall ln, LinesLex L ln [] []
(* probe L0/LX_line: each line is read from state N, with its number. *)
| LX_line : forall ln l eo r t1 t2,
    length l <= max_line_bytes ->
    LineLex L ln SN (buffer L l eo) t1 ->
    LinesLex L (S ln) r t2 ->
    LinesLex L ln ((l, eo) :: r) (t1 ++ t2)
(* probe L0/LX_long: a line beyond the bound (outside the fragment when it
   is read, i.e. before \end{document}). *)
| LX_long : forall ln l eo r t2,
    max_line_bytes < length l ->
    LinesLex L (S ln) r t2 ->
    LinesLex L ln ((l, eo) :: r) (mkLt (RBad BadLongLine) ln (line_start l eo) :: t2).

(** TeX Live's first-line directive: the first two bytes of the main file
    are [%&] (texmfmp.c [parse_first_line], an engine property like the line
    terminators, not a property of the format). *)
Definition pct : ascii := ascii_of_nat 37.
Definition amp : ascii := ascii_of_nat 38.
Arguments pct : simpl never.
Arguments amp : simpl never.

Inductive FirstLine : list ascii -> list lt -> Prop :=
(* probe L0/FL_directive: MEASURED, %&latex: rc 0 and no PDF (a false READY
   if it were read as a comment); %&etex: "! Undefined control sequence." on
   line 2.  Outside the fragment (correction C-89). *)
| FL_directive : forall rest,
    FirstLine (pct :: amp :: rest) [mkLt (RBad BadFirstLine) 1 0]
(* probe L0/FL_none: any other start of the file (MEASURED: " %&latex" and
   "%&" on the second line are read as comments). *)
| FL_none : forall b,
    (forall rest, b <> pct :: amp :: rest) -> FirstLine b [].

(** The declarative reading of a whole file: the first-line directive, then
    the lines. *)
Definition LexFile (L : lexcon) (b : list ascii) (ts : list lt) : Prop :=
  exists t0 ls t1, FirstLine b t0 /\ Lines 0 b ls /\ LinesLex L 1 ls t1 /\ ts = t0 ++ t1.

(** ** The executable lexer *)

Fixpoint split_line (b : list ascii) : list ascii * option (list ascii * nat) :=
  match b with
  | [] => ([], None)
  | c :: r =>
      if Ascii.eqb c lf then ([], Some (r, 1))
      else if Ascii.eqb c cr then
        match r with
        | d :: r' => if Ascii.eqb d lf then ([], Some (r', 2)) else ([], Some (r, 1))
        | [] => ([], Some ([], 1))
        end
      else let '(l, t) := split_line r in (c :: l, t)
  end.

Fixpoint lines_f (fuel o : nat) (b : list ascii) : list line :=
  match fuel with
  | O => []
  | S f =>
      match b with
      | [] => []
      | _ :: _ =>
          let '(l, t) := split_line b in
          match t with
          | None => [(index o l, o + length l)]
          | Some (rest, k) => (index o l, o + length l) :: lines_f f (o + length l + k) rest
          end
      end
  end.

Definition split_lines (b : list ascii) : list line := lines_f (S (length b)) 0 b.

Fixpoint split_letters (L : lexcon) (buf : list (ascii * nat))
  : list (ascii * nat) * list (ascii * nat) :=
  match buf with
  | [] => ([], [])
  | p :: r =>
      if cat_eqb (lx_cat L (fst p)) CLetter
      then let '(w, rest) := split_letters L r in (p :: w, rest)
      else ([], buf)
  end.

Fixpoint lexl (L : lexcon) (ln fuel : nat) (st : lstate) (buf : list (ascii * nat)) : list lt :=
  match fuel with
  | O => []
  | S f =>
  match buf with
  | [] => []
  | (c, o) :: rest =>
      match lx_cat L c with
      | CEol => match st with
                | SN => [mkLt RPar ln o]
                | SM => [mkLt RSpace ln o]
                | SS => []
                end
      | CSpacer => match st with
                   | SM => mkLt RSpace ln o :: lexl L ln f SS rest
                   | _ => lexl L ln f st rest
                   end
      | CComment => []
      | CLetter | COther => mkLt (RChar c) ln o :: lexl L ln f SM rest
      | CBgroup => mkLt RBgroup ln o :: lexl L ln f SM rest
      | CEgroup => mkLt REgroup ln o :: lexl L ln f SM rest
      | CMath => mkLt RMath ln o :: lexl L ln f SM rest
      | CSub => mkLt RSub ln o :: lexl L ln f SM rest
      | CSup => if hathat L c rest then [mkLt (RBad BadHatHat) ln o]
                else mkLt RSup ln o :: lexl L ln f SM rest
      | CEscape =>
          match rest with
          | [] => [mkLt (RBad BadNullCs) ln o]
          | (d, od) :: rest' =>
              if cat_eqb (lx_cat L d) CLetter then
                let '(w, after) := split_letters L rest in
                match after with
                | (x, _) :: after' =>
                    if hathat L x after' then [mkLt (RBad BadHatHat) ln o]
                    else mkLt (RWord (map fst w)) ln o :: lexl L ln f SS after
                | [] => [mkLt (RWord (map fst w)) ln o]
                end
              else if hathat L d rest' then [mkLt (RBad BadHatHat) ln o]
              else mkLt (RSym d) ln o :: lexl L ln f (sym_state L d) rest'
          end
      | CAlign | CParam | CIgnored | CActive | CInvalid => [mkLt (RBad BadCat) ln o]
      end
  end
  end.

Definition lex_line (L : lexcon) (ln : nat) (buf : list (ascii * nat)) : list lt :=
  lexl L ln (S (length buf)) SN buf.

Fixpoint lex_lines (L : lexcon) (ln : nat) (ls : list line) : list lt :=
  match ls with
  | [] => []
  | (l, eo) :: r =>
      (if Nat.leb (length l) max_line_bytes
       then lex_line L ln (buffer L l eo)
       else [mkLt (RBad BadLongLine) ln (line_start l eo)])
      ++ lex_lines L (S ln) r
  end.

Definition first_directive (b : list ascii) : bool :=
  match b with
  | c1 :: c2 :: _ => Ascii.eqb c1 pct && Ascii.eqb c2 amp
  | _ => false
  end.

Definition first_toks (b : list ascii) : list lt :=
  if first_directive b then [mkLt (RBad BadFirstLine) 1 0] else [].

Definition lex (L : lexcon) (b : list ascii) : list lt :=
  first_toks b ++ lex_lines L 1 (split_lines b).

(** ** Exactness: [lex] and [LexFile] agree, both ways *)

(* --- lines --- *)

Lemma index_app : forall l1 l2 o,
  index o (l1 ++ l2) = index o l1 ++ index (o + length l1) l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2 o; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. do 3 f_equal. lia.
Qed.

Lemma lf_cr : lf <> cr.
Proof. discriminate. Qed.

Lemma split_line_sound : forall b l t, split_line b = (l, t) ->
  Forall not_term l /\
  match t with
  | None => b = l
  | Some (rest, 1) => b = l ++ lf :: rest \/ (b = l ++ cr :: rest /\ hd_error rest <> Some lf)
  | Some (rest, 2) => b = l ++ cr :: lf :: rest
  | Some _ => False
  end.
Proof.
  induction b as [|c r IH]; intros l t H; simpl in H.
  - injection H as <- <-. split; [constructor|reflexivity].
  - destruct (Ascii.eqb c lf) eqn:Hlf.
    + apply Ascii.eqb_eq in Hlf. subst c. injection H as <- <-.
      split; [constructor|]. left. reflexivity.
    + destruct (Ascii.eqb c cr) eqn:Hcr.
      * apply Ascii.eqb_eq in Hcr. subst c.
        destruct r as [|d r'].
        -- injection H as <- <-. split; [constructor|]. right. split; [reflexivity|discriminate].
        -- destruct (Ascii.eqb d lf) eqn:Hd.
           ++ apply Ascii.eqb_eq in Hd. subst d. injection H as <- <-.
              split; [constructor|reflexivity].
           ++ injection H as <- <-. split; [constructor|]. right. split; [reflexivity|].
              simpl. intro E. injection E as E. subst d. rewrite Ascii.eqb_refl in Hd. discriminate.
      * destruct (split_line r) as [l' t'] eqn:Hs. injection H as <- <-.
        destruct (IH _ _ eq_refl) as [Hf Ht].
        assert (Hc : not_term c).
        { split; intro E; subst c; [rewrite Ascii.eqb_refl in Hlf|rewrite Ascii.eqb_refl in Hcr]; discriminate. }
        split; [constructor; assumption|].
        destruct t' as [[rest [|[|[|k]]]]|]; simpl; try contradiction;
          try (rewrite Ht; reflexivity);
          (destruct Ht as [->|[-> Hh]]; [left|right]; [reflexivity|split; [reflexivity|exact Hh]]).
Qed.

Lemma split_line_lf : forall rest, split_line (lf :: rest) = ([], Some (rest, 1)).
Proof. intros rest. cbn [split_line]. rewrite Ascii.eqb_refl. reflexivity. Qed.

Lemma split_line_cr : forall rest, split_line (cr :: rest) =
  ([], match rest with
       | d :: r' => if Ascii.eqb d lf then Some (r', 2) else Some (rest, 1)
       | [] => Some ([], 1)
       end).
Proof.
  intros rest. cbn [split_line].
  rewrite (proj2 (Ascii.eqb_neq cr lf) (fun e => lf_cr (eq_sym e))).
  rewrite Ascii.eqb_refl. destruct rest as [|d r']; [reflexivity|].
  destruct (Ascii.eqb d lf); reflexivity.
Qed.

Lemma split_line_app_term : forall l x rest,
  Forall not_term l -> (x = lf \/ x = cr) ->
  split_line (l ++ x :: rest) =
    (l, snd (split_line (x :: rest))).
Proof.
  induction l as [|c l IH]; intros x rest Hf Hx.
  - simpl app. destruct Hx as [-> | ->].
    + rewrite split_line_lf. reflexivity.
    + rewrite split_line_cr. reflexivity.
  - inversion Hf as [|? ? [Hl Hc] Hf']; subst. simpl.
    destruct (Ascii.eqb c lf) eqn:E1; [apply Ascii.eqb_eq in E1; contradiction|].
    destruct (Ascii.eqb c cr) eqn:E2; [apply Ascii.eqb_eq in E2; contradiction|].
    rewrite (IH x rest Hf' Hx). reflexivity.
Qed.

Lemma split_line_all : forall l, Forall not_term l -> split_line l = (l, None).
Proof.
  induction l as [|c l IH]; intros Hf; [reflexivity|].
  inversion Hf as [|? ? [Hl Hc] Hf']; subst. simpl.
  destruct (Ascii.eqb c lf) eqn:E1; [apply Ascii.eqb_eq in E1; contradiction|].
  destruct (Ascii.eqb c cr) eqn:E2; [apply Ascii.eqb_eq in E2; contradiction|].
  rewrite (IH Hf'). reflexivity.
Qed.

Lemma app_length_le : forall {A} (l r : list A) x, length r < length (l ++ x :: r).
Proof. intros. rewrite app_length. simpl. lia. Qed.

Lemma lines_f_sound : forall fuel o b, length b < fuel -> Lines o b (lines_f fuel o b).
Proof.
  induction fuel as [|f IH]; intros o b Hlen; [lia|].
  simpl. destruct b as [|c r]; [constructor|].
  destruct (split_line (c :: r)) as [l t] eqn:Hs.
  destruct (split_line_sound _ _ _ Hs) as [Hf Ht].
  destruct t as [[rest [|[|[|k]]]]|]; try contradiction.
  - destruct Ht as [Hb|[Hb Hh]]; rewrite Hb in *.
    + apply Lines_lf; [exact Hf|]. apply IH. pose proof (app_length_le l rest lf). lia.
    + apply Lines_cr; [exact Hf|exact Hh|]. apply IH. pose proof (app_length_le l rest cr). lia.
  - rewrite Ht in *. apply Lines_crlf; [exact Hf|]. apply IH.
    rewrite app_length in Hlen. simpl in Hlen. lia.
  - rewrite Ht. apply Lines_last; [exact Hf|]. intro E. subst l. discriminate.
Qed.

Lemma split_line_app_lf : forall l rest, Forall not_term l ->
  split_line (l ++ lf :: rest) = (l, Some (rest, 1)).
Proof.
  intros l rest Hf. rewrite (split_line_app_term l lf rest Hf (or_introl eq_refl)).
  rewrite split_line_lf. reflexivity.
Qed.

Lemma split_line_app_crlf : forall l rest, Forall not_term l ->
  split_line (l ++ cr :: lf :: rest) = (l, Some (rest, 2)).
Proof.
  intros l rest Hf. rewrite (split_line_app_term l cr (lf :: rest) Hf (or_intror eq_refl)).
  rewrite split_line_cr. cbn [snd]. rewrite Ascii.eqb_refl. reflexivity.
Qed.

Lemma split_line_app_cr : forall l rest, Forall not_term l -> hd_error rest <> Some lf ->
  split_line (l ++ cr :: rest) = (l, Some (rest, 1)).
Proof.
  intros l rest Hf Hh. rewrite (split_line_app_term l cr rest Hf (or_intror eq_refl)).
  rewrite split_line_cr. cbn [snd]. destruct rest as [|d r']; [reflexivity|].
  destruct (Ascii.eqb d lf) eqn:Ed; [|reflexivity].
  apply Ascii.eqb_eq in Ed. subst d. simpl in Hh. contradiction.
Qed.

Lemma lines_f_cons : forall f o b, b <> [] ->
  lines_f (S f) o b =
  match split_line b with
  | (l, None) => [(index o l, o + length l)]
  | (l, Some (rest, k)) => (index o l, o + length l) :: lines_f f (o + length l + k) rest
  end.
Proof.
  intros f o b Hb. destruct b as [|c r]; [contradiction|].
  cbn [lines_f]. destruct (split_line (c :: r)) as [l [[rest k]|]]; reflexivity.
Qed.

Lemma lines_f_complete : forall o b ls, Lines o b ls ->
  forall fuel, length b < fuel -> lines_f fuel o b = ls.
Proof.
  intros o b ls H. induction H; intros fuel Hlen; (destruct fuel as [|f]; [lia|]).
  - reflexivity.
  - rewrite lines_f_cons by (intro E; symmetry in E; exact (app_cons_not_nil _ _ _ E)).
    rewrite split_line_app_lf by exact H. f_equal. apply IHLines.
    rewrite app_length in Hlen. simpl in Hlen. lia.
  - rewrite lines_f_cons by (intro E; symmetry in E; exact (app_cons_not_nil _ _ _ E)).
    rewrite split_line_app_crlf by exact H. f_equal. apply IHLines.
    rewrite app_length in Hlen. simpl in Hlen. lia.
  - rewrite lines_f_cons by (intro E; symmetry in E; exact (app_cons_not_nil _ _ _ E)).
    rewrite split_line_app_cr by assumption. f_equal. apply IHLines.
    rewrite app_length in Hlen. simpl in Hlen. lia.
  - rewrite lines_f_cons by exact H0.
    rewrite (split_line_all _ H). reflexivity.
Qed.

Lemma split_lines_exact : forall b ls, split_lines b = ls <-> Lines 0 b ls.
Proof.
  intros b ls. unfold split_lines. split.
  - intros <-. apply lines_f_sound. lia.
  - intro H. apply (lines_f_complete _ _ _ H). lia.
Qed.

(* --- one line --- *)

Lemma split_letters_sound : forall L buf w rest, split_letters L buf = (w, rest) ->
  buf = w ++ rest /\ Forall (is_letter L) w /\
  match rest with [] => True | (d, _) :: _ => lx_cat L d <> CLetter end.
Proof.
  intros L. induction buf as [|[c o] r IH]; intros w rest H; simpl in H.
  - injection H as <- <-. repeat split; constructor.
  - destruct (cat_eqb (lx_cat L c) CLetter) eqn:E.
    + destruct (split_letters L r) as [w' rest'] eqn:Hs. injection H as <- <-.
      destruct (IH _ _ eq_refl) as [-> [Hw Hr]]. split; [reflexivity|]. split; [|exact Hr].
      constructor; [|exact Hw]. apply cat_eqb_eq. exact E.
    + injection H as <- <-. split; [reflexivity|]. split; [constructor|].
      intro X. rewrite X in E. discriminate.
Qed.

Lemma split_letters_complete : forall L w rest,
  Forall (is_letter L) w ->
  match rest with [] => True | (d, _) :: _ => lx_cat L d <> CLetter end ->
  split_letters L (w ++ rest) = (w, rest).
Proof.
  intros L w rest Hw Hr. induction Hw as [|[c o] w Hc Hw IH]; simpl.
  - destruct rest as [|[d od] r]; [reflexivity|].
    simpl. destruct (cat_eqb (lx_cat L d) CLetter) eqn:E; [|reflexivity].
    apply cat_eqb_eq in E. contradiction.
  - unfold is_letter in Hc. simpl in Hc. rewrite Hc. simpl. rewrite IH. reflexivity.
Qed.

Lemma lexl_sound : forall L ln fuel st buf, length buf < fuel ->
  LineLex L ln st buf (lexl L ln fuel st buf).
Proof.
  intros L ln fuel. induction fuel as [|f IH]; intros st buf Hlen; [lia|].
  destruct buf as [|[c o] rest]; simpl; [constructor|].
  simpl in Hlen.
  destruct (lx_cat L c) eqn:Hc.
  - (* CEscape *)
    destruct rest as [|[d od] rest'].
    + apply LL_nullcs; exact Hc.
    + destruct (cat_eqb (lx_cat L d) CLetter) eqn:Hd.
      * destruct (split_letters L ((d, od) :: rest')) as [w after] eqn:Hs.
        destruct (split_letters_sound _ _ _ _ Hs) as [Hb [Hw Ha]].
        assert (Hwne : w <> []).
        { intro E. subst w. simpl in Hb. subst after. simpl in Ha.
          apply cat_eqb_eq in Hd. contradiction. }
        rewrite Hb.
        destruct after as [|[x ox] after'].
        -- apply (LL_word L ln st c o w [] []); [exact Hc|exact Hwne|exact Hw|exact I|constructor].
        -- destruct (hathat L x after') eqn:Hh.
           ++ apply LL_word_hathat; assumption.
           ++ apply LL_word; try assumption.
              ** split; assumption.
              ** apply IH. rewrite Hb in Hlen. rewrite app_length in Hlen. simpl in *.
                 destruct w; [contradiction|simpl in Hlen; lia].
      * destruct (hathat L d rest') eqn:Hh.
        -- apply LL_sym_hathat; assumption.
        -- apply LL_sym; try assumption.
           ++ intro X. rewrite X in Hd. discriminate.
           ++ apply IH. simpl in Hlen. lia.
  - apply LL_bgroup; [exact Hc|]. apply IH; lia.
  - apply LL_egroup; [exact Hc|]. apply IH; lia.
  - apply LL_math; [exact Hc|]. apply IH; lia.
  - apply LL_bad. rewrite Hc. reflexivity.
  - destruct st; [apply LL_eol_new|apply LL_eol_mid|apply LL_eol_skip]; exact Hc.
  - apply LL_bad. rewrite Hc. reflexivity.
  - destruct (hathat L c rest) eqn:Hh.
    + apply LL_hathat; assumption.
    + apply LL_sup; try assumption. apply IH; lia.
  - apply LL_sub; [exact Hc|]. apply IH; lia.
  - apply LL_bad. rewrite Hc. reflexivity.
  - destruct st.
    + apply LL_space_skip; [exact Hc|discriminate|]. apply IH; lia.
    + apply LL_space_emit; [exact Hc|]. apply IH; lia.
    + apply LL_space_skip; [exact Hc|discriminate|]. apply IH; lia.
  - apply LL_char; [left; exact Hc|]. apply IH; lia.
  - apply LL_char; [right; exact Hc|]. apply IH; lia.
  - apply LL_bad. rewrite Hc. reflexivity.
  - apply LL_comment. exact Hc.
  - apply LL_bad. rewrite Hc. reflexivity.
Qed.

Lemma lexl_complete : forall L ln st buf out, LineLex L ln st buf out ->
  forall fuel, length buf < fuel -> lexl L ln fuel st buf = out.
Proof.
  intros L ln st buf out H.
  induction H; intros fuel Hlen; (destruct fuel as [|f]; [simpl in Hlen; lia|]); simpl.
  - reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H. destruct st; [| contradiction H0; reflexivity |];
      apply IHLineLex; simpl in Hlen; lia.
  - rewrite H. f_equal. apply IHLineLex. simpl in Hlen. lia.
  - rewrite H. reflexivity.
  - destruct H as [H|H]; rewrite H; f_equal; apply IHLineLex; simpl in Hlen; lia.
  - rewrite H. f_equal. apply IHLineLex. simpl in Hlen. lia.
  - rewrite H. f_equal. apply IHLineLex. simpl in Hlen. lia.
  - rewrite H. f_equal. apply IHLineLex. simpl in Hlen. lia.
  - rewrite H. f_equal. apply IHLineLex. simpl in Hlen. lia.
  - rewrite H, H0. f_equal. apply IHLineLex. simpl in Hlen. lia.
  - rewrite H, H0. reflexivity.
  - (* LL_word *)
    destruct w as [|[d od] w']; [contradiction|].
    assert (Hr : match rest with [] => True | (x, _) :: _ => lx_cat L x <> CLetter end)
      by (destruct rest as [|[x ox] r]; [exact I|exact (proj1 H2)]).
    pose proof (Forall_inv H1) as Hd. unfold is_letter in Hd. simpl in Hd.
    cbn [lexl app]. rewrite H. cbn beta iota zeta.
    rewrite Hd. cbn beta iota zeta delta [cat_eqb].
    rewrite (split_letters_complete L ((d, od) :: w') rest H1 Hr
             : split_letters L ((d, od) :: w' ++ rest) = ((d, od) :: w', rest)).
    cbn beta iota zeta.
    destruct rest as [|[x ox] r].
    + inversion H3; subst. reflexivity.
    + destruct H2 as [_ Hh]. rewrite Hh. f_equal. apply IHLineLex.
      simpl in Hlen. rewrite app_length in Hlen. simpl in Hlen. simpl. lia.
  - (* LL_word_hathat *)
    destruct w as [|[d0 od0] w']; [contradiction|].
    assert (Hx : lx_cat L d <> CLetter).
    { unfold hathat in H2. destruct (cat_eqb (lx_cat L d) CSup) eqn:E; [|discriminate].
      apply cat_eqb_eq in E. rewrite E. discriminate. }
    pose proof (Forall_inv H1) as Hd. unfold is_letter in Hd. simpl in Hd.
    cbn [lexl app]. rewrite H. cbn beta iota zeta.
    rewrite Hd. cbn beta iota zeta delta [cat_eqb].
    rewrite (split_letters_complete L ((d0, od0) :: w') ((d, od) :: rest) H1 Hx
             : split_letters L ((d0, od0) :: w' ++ (d, od) :: rest)
               = ((d0, od0) :: w', (d, od) :: rest)).
    cbn beta iota zeta. rewrite H2. reflexivity.
  - (* LL_sym *)
    rewrite H. destruct (cat_eqb (lx_cat L c) CLetter) eqn:E.
    + apply cat_eqb_eq in E. contradiction.
    + rewrite H1. f_equal. apply IHLineLex. simpl in Hlen. lia.
  - (* LL_sym_hathat *)
    rewrite H. destruct (cat_eqb (lx_cat L c) CLetter) eqn:E.
    + apply cat_eqb_eq in E. unfold hathat in H0. rewrite E in H0. discriminate.
    + rewrite H0. reflexivity.
  - rewrite H. reflexivity.
  - destruct (lx_cat L c) eqn:Hc; simpl in H; try discriminate; reflexivity.
Qed.

Lemma lex_line_exact : forall L ln buf out,
  lex_line L ln buf = out <-> LineLex L ln SN buf out.
Proof.
  intros L ln buf out. unfold lex_line. split.
  - intros <-. apply lexl_sound. lia.
  - intro H. apply (lexl_complete _ _ _ _ _ H). lia.
Qed.

Lemma lex_lines_exact : forall L ln ls ts, lex_lines L ln ls = ts <-> LinesLex L ln ls ts.
Proof.
  intros L ln ls. revert ln. induction ls as [|[l eo] r IH]; intros ln ts; simpl.
  - split; [intros <-; constructor|intro H; inversion H; reflexivity].
  - split.
    + intros <-. destruct (Nat.leb (length l) max_line_bytes) eqn:E.
      * apply Nat.leb_le in E. apply LX_line; [exact E| |apply IH; reflexivity].
        apply lex_line_exact. reflexivity.
      * apply Nat.leb_gt in E. simpl. apply LX_long; [exact E|]. apply IH. reflexivity.
    + intro H. inversion H as [|? ? ? ? t1 t2 Hle Hl Hr|? ? ? ? t2 Hgt Hr]; subst.
      * apply Nat.leb_le in Hle. rewrite Hle. f_equal.
        -- apply lex_line_exact. exact Hl.
        -- apply IH. exact Hr.
      * apply Nat.leb_gt in Hgt. rewrite Hgt. simpl. f_equal. apply IH. exact Hr.
Qed.

Lemma first_toks_exact : forall b t0, first_toks b = t0 <-> FirstLine b t0.
Proof.
  intros b t0. unfold first_toks, first_directive. split.
  - intros <-. destruct b as [|c1 [|c2 r]].
    + apply FL_none. intros rest E. discriminate.
    + apply FL_none. intros rest E. discriminate.
    + destruct (Ascii.eqb c1 pct) eqn:E1; destruct (Ascii.eqb c2 amp) eqn:E2; simpl.
      * apply Ascii.eqb_eq in E1, E2. subst. apply FL_directive.
      * apply FL_none. intros rest E. injection E as -> -> _.
        rewrite Ascii.eqb_refl in E2. discriminate.
      * apply FL_none. intros rest E. injection E as -> -> _.
        rewrite Ascii.eqb_refl in E1. discriminate.
      * apply FL_none. intros rest E. injection E as -> -> _.
        rewrite Ascii.eqb_refl in E1. discriminate.
  - intro H. destruct H as [rest|b Hn].
    + rewrite !Ascii.eqb_refl. reflexivity.
    + destruct b as [|c1 [|c2 r]]; try reflexivity.
      destruct (Ascii.eqb c1 pct) eqn:E1; destruct (Ascii.eqb c2 amp) eqn:E2;
        try reflexivity.
      apply Ascii.eqb_eq in E1, E2. subst. exfalso. exact (Hn r eq_refl).
Qed.

(** The executable lexer is the declarative reading, both ways. *)
Theorem lex_exact : forall L b ts, lex L b = ts <-> LexFile L b ts.
Proof.
  intros L b ts. unfold lex, LexFile. split.
  - intros <-. exists (first_toks b), (split_lines b), (lex_lines L 1 (split_lines b)).
    split; [apply first_toks_exact; reflexivity|].
    split; [apply split_lines_exact; reflexivity|].
    split; [apply lex_lines_exact; reflexivity|reflexivity].
  - intros [t0 [ls [t1 [Hf [Hl [Hx ->]]]]]]. apply split_lines_exact in Hl. subst ls.
    apply first_toks_exact in Hf. apply lex_lines_exact in Hx. subst. reflexivity.
Qed.

(** A file is read one way only. *)
Corollary lexfile_deterministic : forall L b t1 t2,
  LexFile L b t1 -> LexFile L b t2 -> t1 = t2.
Proof.
  intros L b t1 t2 H1 H2. apply lex_exact in H1, H2. congruence.
Qed.

(** Reading is total: every file has exactly one token list (a byte outside
    the fragment becomes a [RBad] token, never a failure of the reader). *)
Corollary lexfile_total : forall L b, exists ts, LexFile L b ts.
Proof. intros L b. exists (lex L b). apply lex_exact. reflexivity. Qed.
