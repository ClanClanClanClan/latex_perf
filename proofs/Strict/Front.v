(** * Strict.Front — from TeX's tokens to the kernel's token stream.

    ADR-012, milestone M2 phase 2.  Lexer.v reads a file into TeX's tokens
    ([LexFile]).  This file says which token lists are documents of the
    fragment and what the kernel (Semantics.v) executes for them:

    - THE FRONT MATTER ([Prologue]): the tokens of [\documentclass{article}]
      and of [\begin{document}], with only space and paragraph tokens before
      and between them (blank lines, spaces, tabs, comments and [\par] are
      all admitted there, because the lexer turns them into these tokens or
      into nothing).  No token may come between [\documentclass] and its
      brace: pdfTeX stops with "Paragraph ended before \@fileswith@ptions was
      complete" on a blank line there (measured), so that is outside the
      fragment.  Everything is decided at the TOKEN level, exactly as TeX
      reads it: [\documentclass{art%<newline>icle}] is the same token list
      and is admitted (measured to compile).
    - THE BODY ([Body]): each token is mapped to the kernel's [Syntax.tok];
      the four control symbols of the math delimiters to [TMOpenInline] ..
      [TMCloseDisplay]; the par token of an empty line to [TPar false] and
      the control word [\par] to [TPar true]; the tokens of
      [\end{document}] to [TEnd].  Reading STOPS there: pdfTeX never reads
      further (measured: any bytes after it, on its line or later lines,
      compile; the only effect of the rest of that line is TeX Live's buffer
      bound, which Lexer.v applies to every line read).
    - After [^] or [_], TeX's math scanner skips space tokens (tex.web
      §1151, "Get the next non-blank non-relax non-call token"); the kernel
      stream does not contain them ([B_space_script]).
    - A token with no rule here ([RBad], a control symbol other than the
      four delimiters, [\end] not followed by [{document}]) means the file is
      outside the fragment ([parse] answers [None]).

    Each kernel token carries the LINE on which TeX's reader stands after
    reading it: its own line, except [TEnd], whose tokens may span lines and
    whose line is the one of its closing brace (measured: [\end{docu%]
    newline [ment}] in math is reported on the second line).  DecideBytes.v
    reports a NOT-READY on the line of the last token the fatal depends on.

    Every constructor cites [probe L0/<constructor>] (see Lexer.v). *)

From Coq Require Import List Ascii Bool Arith Lia.
Import ListNotations.
From LaTeXPerfectionist.Strict Require Import Syntax Decide Lexer.

(** A kernel token with its line and the offset of its first byte. *)
Record ktok := mkK { k_tok : tok; k_line : nat; k_off : nat }.

Definition toks_of (ks : list ktok) : list tok := map k_tok ks.

(** ** Equality of names *)

Fixpoint name_eqb (a b : list ascii) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Ascii.eqb x y && name_eqb a' b'
  | _, _ => false
  end.

Lemma name_eqb_eq : forall a b, name_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; simpl; split; intro H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H1 H2]. apply Ascii.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - injection H as -> ->. rewrite Ascii.eqb_refl. simpl. apply IH. reflexivity.
Qed.

Lemma name_eqb_neq : forall a b, name_eqb a b = false <-> a <> b.
Proof.
  intros a b. split.
  - intros H E. apply name_eqb_eq in E. congruence.
  - intro H. destruct (name_eqb a b) eqn:E; [|reflexivity]. apply name_eqb_eq in E. contradiction.
Qed.

(** ** The front matter *)

(** Space and paragraph tokens, which the preamble ignores in vertical mode
    (measured: blank lines, spaces, tabs, comments and [\par] before and
    between the two commands compile). *)
Definition filler (L : lexcon) (t : lt) : Prop :=
  match lt_tok t with
  | RSpace | RPar => True
  | RWord n => n = lx_par L
  | _ => False
  end.

(** The tokens are exactly the characters of [w]. *)
Definition is_chars (w : list ascii) (ts : list lt) : Prop :=
  map lt_tok ts = map RChar w.

Inductive Prologue (L : lexcon) : list lt -> list lt -> Prop :=
(* probe L0/P_prologue *)
| P_prologue : forall f1 dc ob cls cb f2 bg ob2 env cb2 rest,
    Forall (filler L) f1 ->
    lt_tok dc = RWord (lx_docclass L) -> lx_docclass L <> lx_par L ->
    lt_tok ob = RBgroup -> is_chars (lx_class L) cls -> lt_tok cb = REgroup ->
    Forall (filler L) f2 ->
    lt_tok bg = RWord (lx_begin L) -> lx_begin L <> lx_par L ->
    lt_tok ob2 = RBgroup -> is_chars (lx_docenv L) env -> lt_tok cb2 = REgroup ->
    Prologue L (f1 ++ dc :: ob :: cls ++ cb :: f2 ++ bg :: ob2 :: env ++ cb2 :: rest) rest.

(** ** The body *)

(** The kernel token of a control symbol: the four math delimiters. *)
Definition sym_tok (L : lexcon) (c : ascii) : option tok :=
  if Ascii.eqb c (lx_mopen_inline L) then Some TMOpenInline
  else if Ascii.eqb c (lx_mclose_inline L) then Some TMCloseInline
  else if Ascii.eqb c (lx_mopen_display L) then Some TMOpenDisplay
  else if Ascii.eqb c (lx_mclose_display L) then Some TMCloseDisplay
  else None.

Definition kt (k : tok) (t : lt) : ktok := mkK k (lt_line t) (lt_off t).

(** [s]: the previous kernel token was [^] or [_] (TeX's math scanner then
    skips spaces). *)
Inductive Body (L : lexcon) : bool -> list lt -> list ktok -> Prop :=
(* probe L0/B_eof: the file ends (no \end{document}: Semantics.R_eof). *)
| B_eof : forall s, Body L s [] []
(* probe L0/B_end: \end{document}; reading stops. *)
| B_end : forall s e ob env cb rest,
    lt_tok e = RWord (lx_end L) -> lx_end L <> lx_par L ->
    lt_tok ob = RBgroup -> is_chars (lx_docenv L) env -> lt_tok cb = REgroup ->
    Body L s (e :: ob :: env ++ cb :: rest) [mkK TEnd (lt_line cb) (lt_off e)]
(* probe L0/B_space *)
| B_space : forall t rest ks,
    lt_tok t = RSpace -> Body L false rest ks ->
    Body L false (t :: rest) (kt TSpace t :: ks)
(* probe L0/B_space_script: a space after ^ or _ is skipped. *)
| B_space_script : forall t rest ks,
    lt_tok t = RSpace -> Body L true rest ks ->
    Body L true (t :: rest) ks
(* probe L0/B_par_line: an empty line. *)
| B_par_line : forall s t rest ks,
    lt_tok t = RPar -> Body L false rest ks ->
    Body L s (t :: rest) (kt (TPar false) t :: ks)
(* probe L0/B_par_word: the control word \par. *)
| B_par_word : forall s t rest ks,
    lt_tok t = RWord (lx_par L) -> Body L false rest ks ->
    Body L s (t :: rest) (kt (TPar true) t :: ks)
(* probe L0/B_word: any other control word but \end. *)
| B_word : forall s t n rest ks,
    lt_tok t = RWord n -> n <> lx_par L -> n <> lx_end L -> Body L false rest ks ->
    Body L s (t :: rest) (kt (TCs n) t :: ks)
(* probe L0/B_sym: \( \) \[ \]. *)
| B_sym : forall s t c k rest ks,
    lt_tok t = RSym c -> sym_tok L c = Some k -> Body L false rest ks ->
    Body L s (t :: rest) (kt k t :: ks)
(* probe L0/B_char *)
| B_char : forall s t c rest ks,
    lt_tok t = RChar c -> Body L false rest ks ->
    Body L s (t :: rest) (kt (TChar c) t :: ks)
(* probe L0/B_open *)
| B_open : forall s t rest ks,
    lt_tok t = RBgroup -> Body L false rest ks ->
    Body L s (t :: rest) (kt TOpen t :: ks)
(* probe L0/B_close *)
| B_close : forall s t rest ks,
    lt_tok t = REgroup -> Body L false rest ks ->
    Body L s (t :: rest) (kt TClose t :: ks)
(* probe L0/B_math *)
| B_math : forall s t rest ks,
    lt_tok t = RMath -> Body L false rest ks ->
    Body L s (t :: rest) (kt TDollar t :: ks)
(* probe L0/B_script: ^ and _. *)
| B_script : forall s t (up : bool) rest ks,
    lt_tok t = (if up then RSup else RSub) -> Body L true rest ks ->
    Body L s (t :: rest) (kt (TScript up) t :: ks).

(** The declarative parse of a file: its reading, its front matter, its
    body. *)
Definition Parse (L : lexcon) (b : list ascii) (ks : list ktok) : Prop :=
  exists ts rest, LexFile L b ts /\ Prologue L ts rest /\ Body L false rest ks.

(** ** The executable parser *)

Definition fillerb (L : lexcon) (t : lt) : bool :=
  match lt_tok t with
  | RSpace | RPar => true
  | RWord n => name_eqb n (lx_par L)
  | _ => false
  end.

Fixpoint skip_fill (L : lexcon) (ts : list lt) : list lt :=
  match ts with
  | t :: r => if fillerb L t then skip_fill L r else ts
  | [] => []
  end.

Definition is_char_tok (c : ascii) (t : lt) : bool :=
  match lt_tok t with RChar d => Ascii.eqb c d | _ => false end.

Fixpoint match_chars (w : list ascii) (ts : list lt) : option (list lt) :=
  match w, ts with
  | [], _ => Some ts
  | c :: w', t :: r => if is_char_tok c t then match_chars w' r else None
  | _ :: _, [] => None
  end.

Definition is_word (n : name) (t : lt) : bool :=
  match lt_tok t with RWord m => name_eqb m n | _ => false end.

Definition is_tok (k : rtok) (t : lt) : bool :=
  match k, lt_tok t with
  | RBgroup, RBgroup | REgroup, REgroup => true
  | _, _ => false
  end.

(** [\name{w}] at the head: the rest after the closing brace, and that
    brace. *)
Definition braced (n : name) (w : list ascii) (ts : list lt) : option (lt * list lt) :=
  match ts with
  | t :: ob :: r =>
      if is_word n t && is_tok RBgroup ob then
        match match_chars w r with
        | Some (cb :: rest) => if is_tok REgroup cb then Some (cb, rest) else None
        | _ => None
        end
      else None
  | _ => None
  end.

Definition prologue (L : lexcon) (ts : list lt) : option (list lt) :=
  if name_eqb (lx_docclass L) (lx_par L) || name_eqb (lx_begin L) (lx_par L) then None
  else
    match braced (lx_docclass L) (lx_class L) (skip_fill L ts) with
    | Some (_, r) =>
        match braced (lx_begin L) (lx_docenv L) (skip_fill L r) with
        | Some (_, rest) => Some rest
        | None => None
        end
    | None => None
    end.

Definition cons_k (k : ktok) (r : option (list ktok)) : option (list ktok) :=
  match r with Some ks => Some (k :: ks) | None => None end.

Fixpoint body (L : lexcon) (s : bool) (ts : list lt) : option (list ktok) :=
  match ts with
  | [] => Some []
  | t :: rest =>
      match lt_tok t with
      | RWord n =>
          if name_eqb n (lx_par L) then cons_k (kt (TPar true) t) (body L false rest)
          else if name_eqb n (lx_end L) then
            match braced (lx_end L) (lx_docenv L) ts with
            | Some (cb, _) => Some [mkK TEnd (lt_line cb) (lt_off t)]
            | None => None
            end
          else cons_k (kt (TCs n) t) (body L false rest)
      | RSpace => if s then body L true rest else cons_k (kt TSpace t) (body L false rest)
      | RPar => cons_k (kt (TPar false) t) (body L false rest)
      | RSym c =>
          match sym_tok L c with
          | Some k => cons_k (kt k t) (body L false rest)
          | None => None
          end
      | RChar c => cons_k (kt (TChar c) t) (body L false rest)
      | RBgroup => cons_k (kt TOpen t) (body L false rest)
      | REgroup => cons_k (kt TClose t) (body L false rest)
      | RMath => cons_k (kt TDollar t) (body L false rest)
      | RSup => cons_k (kt (TScript true) t) (body L true rest)
      | RSub => cons_k (kt (TScript false) t) (body L true rest)
      | RBad _ => None
      end
  end.

Definition front (L : lexcon) (ts : list lt) : option (list ktok) :=
  match prologue L ts with
  | Some rest => body L false rest
  | None => None
  end.

Definition parse (L : lexcon) (b : list ascii) : option (list ktok) := front L (lex L b).

(** ** Exactness *)

Lemma fillerb_spec : forall L t, fillerb L t = true <-> filler L t.
Proof.
  intros L [k l o]. unfold fillerb, filler. simpl.
  destruct k; simpl; split; intro H; try exact I; try discriminate; try contradiction; try reflexivity.
  - apply name_eqb_eq. exact H.
  - apply name_eqb_eq. exact H.
Qed.

Lemma skip_fill_app : forall L f r,
  Forall (filler L) f ->
  (match r with t :: _ => fillerb L t = false | [] => True end) ->
  skip_fill L (f ++ r) = r.
Proof.
  intros L f r Hf Hr. induction Hf as [|t f Ht Hf IH]; simpl.
  - destruct r as [|t r]; [reflexivity|]. simpl. rewrite Hr. reflexivity.
  - apply fillerb_spec in Ht. rewrite Ht. exact IH.
Qed.

Lemma skip_fill_sound : forall L ts, exists f,
  ts = f ++ skip_fill L ts /\ Forall (filler L) f /\
  match skip_fill L ts with t :: _ => fillerb L t = false | [] => True end.
Proof.
  intros L ts. induction ts as [|t r IH]; simpl.
  - exists []. repeat split; constructor.
  - destruct (fillerb L t) eqn:E.
    + destruct IH as [f [Hr [Hf Hh]]]. exists (t :: f). split; [simpl; f_equal; exact Hr|].
      split; [constructor; [apply fillerb_spec; exact E|exact Hf]|exact Hh].
    + exists []. split; [reflexivity|]. split; [constructor|exact E].
Qed.

Lemma match_chars_app : forall w cs r, is_chars w cs -> match_chars w (cs ++ r) = Some r.
Proof.
  induction w as [|c w IH]; intros cs r H; unfold is_chars in H.
  - destruct cs; [reflexivity|discriminate].
  - destruct cs as [|t cs]; [discriminate|]. simpl in H. injection H as Ht Hcs.
    simpl. unfold is_char_tok. rewrite Ht. rewrite Ascii.eqb_refl. apply IH. exact Hcs.
Qed.

Lemma match_chars_sound : forall w ts r, match_chars w ts = Some r ->
  exists cs, ts = cs ++ r /\ is_chars w cs.
Proof.
  induction w as [|c w IH]; intros ts r H; simpl in H.
  - injection H as <-. exists []. split; reflexivity.
  - destruct ts as [|t ts]; [discriminate|].
    destruct (is_char_tok c t) eqn:E; [|discriminate].
    destruct (IH _ _ H) as [cs [-> Hcs]]. exists (t :: cs). split; [reflexivity|].
    unfold is_chars. simpl. unfold is_char_tok in E.
    destruct (lt_tok t) eqn:Et; try discriminate. apply Ascii.eqb_eq in E. subst.
    f_equal. exact Hcs.
Qed.

Lemma is_word_spec : forall n t, is_word n t = true <-> lt_tok t = RWord n.
Proof.
  intros n [k l o]. unfold is_word. simpl. destruct k; split; intro H; try discriminate.
  - apply name_eqb_eq in H. subst. reflexivity.
  - injection H as ->. apply name_eqb_eq. reflexivity.
Qed.

Lemma is_tok_bg : forall t, is_tok RBgroup t = true <-> lt_tok t = RBgroup.
Proof. intros [k l o]. unfold is_tok. simpl. destruct k; split; intro H; congruence. Qed.

Lemma is_tok_eg : forall t, is_tok REgroup t = true <-> lt_tok t = REgroup.
Proof. intros [k l o]. unfold is_tok. simpl. destruct k; split; intro H; congruence. Qed.

Lemma braced_sound : forall n w ts cb rest, braced n w ts = Some (cb, rest) ->
  exists t ob cs, ts = t :: ob :: cs ++ cb :: rest /\ lt_tok t = RWord n /\
    lt_tok ob = RBgroup /\ is_chars w cs /\ lt_tok cb = REgroup.
Proof.
  intros n w ts cb rest H. unfold braced in H.
  destruct ts as [|t [|ob r]]; try discriminate.
  destruct (is_word n t) eqn:E1; [|discriminate].
  destruct (is_tok RBgroup ob) eqn:E2; [|discriminate]. cbn [andb] in H.
  destruct (match_chars w r) as [[|cb' rest']|] eqn:E3; try discriminate.
  destruct (is_tok REgroup cb') eqn:E4; [|discriminate]. injection H as <- <-.
  destruct (match_chars_sound _ _ _ E3) as [cs [-> Hcs]].
  exists t, ob, cs. repeat split; try assumption.
  - apply is_word_spec. exact E1.
  - apply is_tok_bg. exact E2.
  - apply is_tok_eg. exact E4.
Qed.

Lemma braced_complete : forall n w t ob cs cb rest,
  lt_tok t = RWord n -> lt_tok ob = RBgroup -> is_chars w cs -> lt_tok cb = REgroup ->
  braced n w (t :: ob :: cs ++ cb :: rest) = Some (cb, rest).
Proof.
  intros n w t ob cs cb rest H1 H2 H3 H4. unfold braced.
  rewrite (proj2 (is_word_spec n t) H1), (proj2 (is_tok_bg ob) H2). cbn [andb].
  rewrite (match_chars_app w cs (cb :: rest) H3).
  rewrite (proj2 (is_tok_eg cb) H4). reflexivity.
Qed.

Lemma not_filler_word : forall L t n, lt_tok t = RWord n -> n <> lx_par L -> fillerb L t = false.
Proof.
  intros L t n H1 H2. unfold fillerb. rewrite H1. apply name_eqb_neq. exact H2.
Qed.

Theorem prologue_exact : forall L ts rest, prologue L ts = Some rest <-> Prologue L ts rest.
Proof.
  intros L ts rest. split.
  - intro H. unfold prologue in H.
    destruct (name_eqb (lx_docclass L) (lx_par L)) eqn:N1; [discriminate|].
    destruct (name_eqb (lx_begin L) (lx_par L)) eqn:N2; [discriminate|]. simpl in H.
    destruct (braced (lx_docclass L) (lx_class L) (skip_fill L ts)) as [[cb r]|] eqn:B1;
      [|discriminate].
    destruct (braced (lx_begin L) (lx_docenv L) (skip_fill L r)) as [[cb2 r2]|] eqn:B2;
      [|discriminate].
    injection H as <-.
    destruct (skip_fill_sound L ts) as [f1 [E1 [F1 _]]].
    destruct (skip_fill_sound L r) as [f2 [E2 [F2 _]]].
    destruct (braced_sound _ _ _ _ _ B1) as [dc [ob [cls [S1 [D1 [O1 [C1 K1]]]]]]].
    destruct (braced_sound _ _ _ _ _ B2) as [bg [ob2 [env [S2 [D2 [O2 [C2 K2]]]]]]].
    rewrite S1 in E1. rewrite S2 in E2. rewrite E1, E2.
    apply P_prologue; try assumption; apply name_eqb_neq; assumption.
  - intro H. destruct H. unfold prologue.
    rewrite (proj2 (name_eqb_neq _ _) H1), (proj2 (name_eqb_neq _ _) H7). simpl.
    rewrite (skip_fill_app L f1 (dc :: ob :: cls ++ cb :: f2 ++ bg :: ob2 :: env ++ cb2 :: rest)
               H (not_filler_word L dc _ H0 H1)).
    rewrite (braced_complete _ _ dc ob cls cb _ H0 H2 H3 H4).
    rewrite (skip_fill_app L f2 (bg :: ob2 :: env ++ cb2 :: rest) H5 (not_filler_word L bg _ H6 H7)).
    rewrite (braced_complete _ _ bg ob2 env cb2 _ H6 H8 H9 H10). reflexivity.
Qed.

Lemma body_sound : forall L ts s ks, body L s ts = Some ks -> Body L s ts ks.
Proof.
  intros L ts. induction ts as [|t rest IH]; intros s ks H; cbn [body] in H.
  - injection H as <-. constructor.
  - destruct (lt_tok t) eqn:Et.
    + (* RChar *) destruct (body L false rest) eqn:B; [|discriminate].
      injection H as <-. apply B_char with (c := c); [exact Et|apply IH; exact B].
    + (* RSpace *) destruct s.
      * apply B_space_script; [exact Et|apply IH; exact H].
      * destruct (body L false rest) eqn:B; [|discriminate].
        injection H as <-. apply B_space; [exact Et|apply IH; exact B].
    + (* RPar *) destruct (body L false rest) eqn:B; [|discriminate].
      injection H as <-. apply B_par_line; [exact Et|apply IH; exact B].
    + destruct (body L false rest) eqn:B; [|discriminate].
      injection H as <-. apply B_open; [exact Et|apply IH; exact B].
    + destruct (body L false rest) eqn:B; [|discriminate].
      injection H as <-. apply B_close; [exact Et|apply IH; exact B].
    + destruct (body L false rest) eqn:B; [|discriminate].
      injection H as <-. apply B_math; [exact Et|apply IH; exact B].
    + destruct (body L true rest) eqn:B; [|discriminate].
      injection H as <-. apply (B_script L s t true); [exact Et|apply IH; exact B].
    + destruct (body L true rest) eqn:B; [|discriminate].
      injection H as <-. apply (B_script L s t false); [exact Et|apply IH; exact B].
    + (* RWord *)
      destruct (name_eqb n (lx_par L)) eqn:N1.
      * apply name_eqb_eq in N1. subst n.
        destruct (body L false rest) eqn:B; [|discriminate].
        injection H as <-. apply B_par_word; [exact Et|apply IH; exact B].
      * destruct (name_eqb n (lx_end L)) eqn:N2.
        -- apply name_eqb_eq in N2. subst n.
           destruct (braced (lx_end L) (lx_docenv L) (t :: rest)) as [[cb r]|] eqn:B;
             [|discriminate].
           injection H as <-.
           destruct (braced_sound _ _ _ _ _ B) as [t' [ob [cs [S1 [D1 [O1 [C1 K1]]]]]]].
           injection S1 as <- S1. rewrite S1.
           apply B_end; try assumption. apply name_eqb_neq. exact N1.
        -- destruct (body L false rest) eqn:B; [|discriminate].
           injection H as <-. apply B_word; try assumption.
           ++ apply name_eqb_neq. exact N1.
           ++ apply name_eqb_neq. exact N2.
           ++ apply IH. exact B.
    + (* RSym *)
      destruct (sym_tok L c) as [k|] eqn:Sk; [|discriminate].
      destruct (body L false rest) eqn:B; [|discriminate].
      injection H as <-. apply B_sym with (c := c); [exact Et|exact Sk|apply IH; exact B].
    + discriminate.
Qed.

Lemma body_complete : forall L s ts ks, Body L s ts ks -> body L s ts = Some ks.
Proof.
  intros L s ts ks H. induction H; cbn [body].
  - reflexivity.
  - rewrite H. rewrite (proj2 (name_eqb_neq _ _) H0).
    rewrite (proj2 (name_eqb_eq _ _) eq_refl).
    rewrite (braced_complete _ _ e ob env cb rest H H1 H2 H3). reflexivity.
  - rewrite H. rewrite IHBody. reflexivity.
  - rewrite H. exact IHBody.
  - rewrite H. rewrite IHBody. reflexivity.
  - rewrite H. rewrite (proj2 (name_eqb_eq _ _) eq_refl). rewrite IHBody. reflexivity.
  - rewrite H. rewrite (proj2 (name_eqb_neq _ _) H0), (proj2 (name_eqb_neq _ _) H1).
    rewrite IHBody. reflexivity.
  - rewrite H, H0. rewrite IHBody. reflexivity.
  - rewrite H. rewrite IHBody. reflexivity.
  - rewrite H. rewrite IHBody. reflexivity.
  - rewrite H. rewrite IHBody. reflexivity.
  - rewrite H. rewrite IHBody. reflexivity.
  - rewrite H. destruct up; rewrite IHBody; reflexivity.
Qed.

Theorem body_exact : forall L s ts ks, body L s ts = Some ks <-> Body L s ts ks.
Proof.
  intros L s ts ks. split; [apply body_sound|apply body_complete].
Qed.

(** The executable parser is the declarative parse, both ways. *)
Theorem parse_exact : forall L b ks, parse L b = Some ks <-> Parse L b ks.
Proof.
  intros L b ks. unfold parse, front, Parse. split.
  - intro H. destruct (prologue L (lex L b)) as [rest|] eqn:P; [|discriminate].
    exists (lex L b), rest. split; [apply lex_exact; reflexivity|].
    split; [apply prologue_exact; exact P|apply body_exact; exact H].
  - intros [ts [rest [Hl [Hp Hb]]]]. apply lex_exact in Hl. subst ts.
    apply prologue_exact in Hp. rewrite Hp. apply body_exact. exact Hb.
Qed.

(** A file parses one way at most. *)
Corollary parse_deterministic : forall L b k1 k2, Parse L b k1 -> Parse L b k2 -> k1 = k2.
Proof.
  intros L b k1 k2 H1 H2. apply parse_exact in H1, H2. congruence.
Qed.
