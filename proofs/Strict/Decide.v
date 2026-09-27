(** * Strict.Decide — the executable decider of L_S0, and its exactness.

    ADR-012 / STRICT_TIER_DESIGN.md §C.3, trust layer (2).  [decide] is an
    ordinary function (extracted to OCaml, Extract.v): a one-token transition
    function [step] iterated by [run].  [Runs] (Semantics.v) is the separate
    declarative relation it is proved equal to, in both directions:

      strict_decider_exact : in_strict_doc C d ->
        (decide C d = ProvenReady <-> Runs C init (flatten_doc d) Compiles) /\
        (forall r l, decide C d = ProvenNotReady r l <->
                     Runs C init (flatten_doc d) (Fatal r l)).

    [runs_deterministic] is proved about [Runs] ITSELF (by induction on the
    derivation, never by appeal to [decide]), and [runs_total] shows that a
    strict document always has an outcome, so [decide] never answers
    [NotStrict] inside the tier ([decide_total]).  [in_strict_dec] makes
    membership decidable.

    Why this is not the [decide = decide] tautology the design warns about
    (§A.2, [UserExpand.user_expand_deterministic]): [Runs] is an inductive
    relation over the token stream whose constructors are stated rule by
    rule, each tied to a probe family; [decide] is a total function that
    could disagree with it.  The exactness proof is a refinement proof in
    both directions, and it fails if a single [step] case differs from its
    constructor (the kill-test of the harness demonstrates one). *)

From Coq Require Import List Bool Ascii Lia.
Import ListNotations.
From LaTeXPerfectionist.Strict Require Import Syntax Contract Semantics.

(** ** Membership in the strict fragment *)

Local Open Scope char_scope.

Definition in_range (lo hi c : ascii) : bool :=
  match Ascii.compare lo c, Ascii.compare c hi with
  | Gt, _ => false
  | _, Gt => false
  | _, _ => true
  end.

Definition letter (c : ascii) : bool := in_range "A" "Z" c || in_range "a" "z" c.

(** The characters of [NText]: letters, digits and punctuation whose
    category code is 11 or 12 in [article] with no packages, that are not
    active in math, not a ligature trigger with a following [`] (none of
    [`] ['] is admitted), and that no admitted command can read as an
    argument delimiter ([[] []] [*] are excluded for that reason). *)
Definition safe_char (c : ascii) : bool :=
  letter c || in_range "0" "9" c
  || existsb (Ascii.eqb c) ["."; ","; ";"; ":"; "!"; "?"; "("; ")"; "/"; "+"; "-"; "="].

Local Close Scope char_scope.

Definition name_ok (n : name) : bool :=
  match n with [] => false | _ => forallb letter n end.

Definition is_some {A} (o : option A) : bool := match o with Some _ => true | None => false end.

(** A token is admitted: a safe character, or a control word that is either
    undefined in the contract's closed world (decided E1) or has an attested
    signature.  A defined name WITHOUT a signature is outside the tier
    (design §A.1.3: never guessed). *)
Definition tok_ok (C : contract) (t : tok) : bool :=
  match t with
  | TChar c => safe_char c
  | TCs n => name_ok n && (negb (c_defined C n) || is_some (c_sig C n))
  | _ => true
  end.

(** Every [^]/[_] is followed by a character or a [{] (the phase-1 script
    arguments; a control word as a script argument is phase 2). *)
Fixpoint scripts_ok (ts : list tok) : bool :=
  match ts with
  | [] => true
  | TScript _ :: rest =>
      match rest with
      | TChar _ :: _ | TOpen :: _ => scripts_ok rest
      | _ => false
      end
  | _ :: rest => scripts_ok rest
  end.

Definition in_strict_toks (C : contract) (ts : list tok) : Prop :=
  Forall (fun t => tok_ok C t = true) ts /\ scripts_ok ts = true.

Definition in_strict_doc (C : contract) (d : doc) : Prop :=
  in_strict_toks C (flatten_doc d).

Definition in_strict_b (C : contract) (d : doc) : bool :=
  forallb (tok_ok C) (flatten_doc d) && scripts_ok (flatten_doc d).

Lemma in_strict_b_spec : forall C d, in_strict_b C d = true <-> in_strict_doc C d.
Proof.
  intros C d. unfold in_strict_b, in_strict_doc, in_strict_toks.
  rewrite andb_true_iff, forallb_forall, Forall_forall. tauto.
Qed.

Theorem in_strict_dec : forall C d, {in_strict_doc C d} + {~ in_strict_doc C d}.
Proof.
  intros C d. destruct (in_strict_b C d) eqn:E.
  - left. apply in_strict_b_spec. exact E.
  - right. intro H. apply in_strict_b_spec in H. rewrite H in E. discriminate.
Qed.

(** ** The transition function *)

Inductive step_res :=
| Go1 (s : state)      (* consumed one token *)
| Go2 (s : state)      (* consumed this token and the next *)
| Stop (o : outcome)
| Stuck.               (* no rule: outside the tier *)

Definition step (C : contract) (s : state) (t : tok) (nx : option tok) : step_res :=
  let fs := s_frames s in
  let o := s_out s in
  let p := s_pos s in
  match t with
  | TEnd =>
      if in_math fs then Stop (Fatal E5 p)
      else if o then Stop Compiles else Stop (Fatal E0 p)
  | TChar _ =>
      if in_math fs then Go1 (mkState (fresh_tail fs) o (S p))
      else Go1 (mkState fs true (S p))
  | TSpace => Go1 (mkState fs o (S p))
  | TPar _ => if in_math fs then Stop (Fatal E6 p) else Go1 (mkState fs o (S p))
  | TOpen =>
      if in_math fs then Go1 (mkState (FMGroup false false false :: fresh_tail fs) o (S p))
      else Go1 (mkState (FSimple :: fs) o (S p))
  | TClose =>
      match fs with
      | FSimple :: r => Go1 (mkState r o (S p))
      | FMGroup _ _ _ :: r => Go1 (mkState r o (S p))
      | FShift _ _ _ :: _ => Stop (Fatal E5 p)
      | [] => Stop (Fatal E5 p)
      end
  | TDollar =>
      match fs with
      | FShift false _ _ :: r => Go1 (mkState r o (S p))
      | FShift true _ _ :: r =>
          match nx with
          | Some TDollar => Go2 (mkState r o (S (S p)))
          | Some (TCs n) =>
              if c_defined C n
              then (if is_some (c_sig C n) then Stop (Fatal E5 p) else Stuck)
              else Stop (Fatal E1 (S p))
          | Some _ => Stop (Fatal E5 p)
          | None => Stop (Fatal E5 p)
          end
      | FMGroup _ _ _ :: _ => Stop (Fatal E5 p)
      | _ =>
          match nx with
          | Some TDollar => Go2 (mkState (FShift true false false :: fs) true (S (S p)))
          | _ => Go1 (mkState (FShift false false false :: fs) true (S p))
          end
      end
  | TMOpenInline =>
      if in_math fs then Stop (Fatal E5 p)
      else Go1 (mkState (FShift false false false :: fs) true (S p))
  | TMCloseInline =>
      match fs with
      | FShift false _ _ :: r => Go1 (mkState r o (S p))
      | _ => Stop (Fatal E5 p)
      end
  | TMOpenDisplay =>
      if in_math fs then Stop (Fatal E5 p)
      else Go1 (mkState (FShift true false false :: fs) true (S p))
  | TMCloseDisplay =>
      match fs with
      | FShift true _ _ :: r => Go1 (mkState r o (S p))
      | _ => Stop (Fatal E5 p)
      end
  | TScript up =>
      if negb (in_math fs) then Stop (Fatal E3 p)
      else if tail_has up fs then Stop (Fatal E4 p)
      else
        match nx with
        | Some (TChar _) => Go2 (mkState (mark_script up fs) o (S (S p)))
        | Some TOpen => Go2 (mkState (FMGroup true false false :: mark_script up fs) o (S (S p)))
        | _ => Stuck
        end
  | TCs n =>
      if negb (c_defined C n) then Stop (Fatal E1 p)
      else
        match c_sig C n with
        | None => Stuck
        | Some sg =>
            if in_math fs then
              match sig_math sg with
              | MxNoad => Go1 (mkState (fresh_tail fs) o (S p))
              | MxNoop => Go1 (mkState fs o (S p))
              | MxFatal r => Stop (Fatal r p)
              end
            else
              match sig_text sg with
              | TxMaterial => Go1 (mkState fs true (S p))
              | TxNoop => Go1 (mkState fs o (S p))
              | TxFatal r => Stop (Fatal r p)
              end
        end
  end.

Fixpoint run (C : contract) (s : state) (ts : list tok) : option outcome :=
  match ts with
  | [] => Some (Fatal E5 (s_pos s))
  | t :: rest =>
      match step C s t (hd_error rest) with
      | Go1 s' => run C s' rest
      | Go2 s' => match rest with [] => None | _ :: rest' => run C s' rest' end
      | Stop o => Some o
      | Stuck => None
      end
  end.

Inductive verdict :=
| ProvenReady
| ProvenNotReady (r : reason) (l : nat)
| NotStrict.

Definition verdict_of (r : option outcome) : verdict :=
  match r with
  | Some Compiles => ProvenReady
  | Some (Fatal rs l) => ProvenNotReady rs l
  | None => NotStrict
  end.

Definition decide (C : contract) (d : doc) : verdict :=
  if in_strict_b C d then verdict_of (run C init (flatten_doc d)) else NotStrict.

(** ** Soundness: what [run] answers, [Runs] derives *)

Lemma run_sound_n : forall C k ts s o,
  length ts <= k -> run C s ts = Some o -> Runs C s ts o.
Proof.
  intros C k. induction k as [|k IH]; intros ts s o Hlen Hrun.
  - destruct ts; [|simpl in Hlen; lia].
    destruct s as [fs so p]. simpl in Hrun. injection Hrun as <-. constructor.
  - destruct ts as [|t rest].
    + destruct s as [fs so p]. simpl in Hrun. injection Hrun as <-. constructor.
    + simpl in Hlen.
      assert (Hl1 : length rest <= k) by lia.
      destruct s as [fs so p]. simpl in Hrun.
      destruct t; simpl in Hrun.
      * (* TChar *)
        destruct (in_math fs) eqn:Hm.
        -- apply R_char_math; [exact Hm|]. apply IH; assumption.
        -- apply R_char_text; [exact Hm|]. apply IH; assumption.
      * (* TSpace *) apply R_space. apply IH; assumption.
      * (* TPar *)
        destruct (in_math fs) eqn:Hm.
        -- injection Hrun as <-. apply R_par_math; exact Hm.
        -- apply R_par_text; [exact Hm|]. apply IH; assumption.
      * (* TOpen *)
        destruct (in_math fs) eqn:Hm.
        -- apply R_open_math; [exact Hm|]. apply IH; assumption.
        -- apply R_open_text; [exact Hm|]. apply IH; assumption.
      * (* TClose *)
        destruct fs as [|f fs'].
        -- injection Hrun as <-. apply R_close_top.
        -- destruct f.
           ++ apply R_close_simple. apply IH; assumption.
           ++ injection Hrun as <-. apply R_close_shift.
           ++ apply R_close_group. apply IH; assumption.
      * (* TDollar *)
        destruct fs as [|f fs'].
        -- (* text, no frame *)
           destruct rest as [|t2 rest2].
           ++ simpl in Hrun. apply R_dollar_inline_open; [reflexivity|exact I|].
              apply IH; [simpl; lia|exact Hrun].
           ++ simpl in Hrun. destruct t2;
              try (apply R_dollar_inline_open; [reflexivity|exact I|apply IH; assumption]).
              apply R_dollar_display_open; [reflexivity|]. apply IH; [simpl in Hl1; lia|exact Hrun].
        -- destruct f as [|d sp sb|g sp sb].
           ++ (* FSimple: text *)
              destruct rest as [|t2 rest2].
              ** simpl in Hrun. apply R_dollar_inline_open; [reflexivity|exact I|].
                 apply IH; [simpl; lia|exact Hrun].
              ** simpl in Hrun. destruct t2;
                 try (apply R_dollar_inline_open; [reflexivity|exact I|apply IH; assumption]).
                 apply R_dollar_display_open; [reflexivity|]. apply IH; [simpl in Hl1; lia|exact Hrun].
           ++ destruct d.
              ** (* display *)
                 destruct rest as [|t2 rest2].
                 --- simpl in Hrun. injection Hrun as <-. apply R_dollar_display_eof.
                 --- simpl in Hrun. destruct t2;
                     try (injection Hrun as <-; apply R_dollar_display_bad; exact I).
                     +++ apply R_dollar_display_close. apply IH; [simpl in Hl1; lia|exact Hrun].
                     +++ destruct (c_defined C n) eqn:Hd.
                         *** destruct (c_sig C n) eqn:Hs; simpl in Hrun; [|discriminate].
                             injection Hrun as <-. apply R_dollar_display_bad. simpl.
                             split; [exact Hd|]. rewrite Hs. discriminate.
                         *** injection Hrun as <-. apply R_dollar_display_undef. exact Hd.
              ** (* inline *) apply R_dollar_inline_close. apply IH; assumption.
           ++ injection Hrun as <-. apply R_dollar_group.
      * (* TMOpenInline *)
        destruct (in_math fs) eqn:Hm.
        -- injection Hrun as <-. apply R_mopen_inline_bad; exact Hm.
        -- apply R_mopen_inline; [exact Hm|]. apply IH; assumption.
      * (* TMCloseInline *)
        destruct fs as [|f fs'];
          [injection Hrun as <-; apply R_mclose_inline_bad; exact I|].
        destruct f as [|d sp sb|g sp sb];
          try (injection Hrun as <-; apply R_mclose_inline_bad; exact I).
        destruct d.
        -- injection Hrun as <-. apply R_mclose_inline_bad; exact I.
        -- apply R_mclose_inline. apply IH; assumption.
      * (* TMOpenDisplay *)
        destruct (in_math fs) eqn:Hm.
        -- injection Hrun as <-. apply R_mopen_display_bad; exact Hm.
        -- apply R_mopen_display; [exact Hm|]. apply IH; assumption.
      * (* TMCloseDisplay *)
        destruct fs as [|f fs'];
          [injection Hrun as <-; apply R_mclose_display_bad; exact I|].
        destruct f as [|d sp sb|g sp sb];
          try (injection Hrun as <-; apply R_mclose_display_bad; exact I).
        destruct d.
        -- apply R_mclose_display. apply IH; assumption.
        -- injection Hrun as <-. apply R_mclose_display_bad; exact I.
      * (* TScript *)
        destruct (in_math fs) eqn:Hm; simpl in Hrun.
        -- destruct (tail_has up fs) eqn:Ht.
           ++ injection Hrun as <-. apply R_script_double; assumption.
           ++ destruct rest as [|t2 rest2]; [discriminate|].
              simpl in Hrun. destruct t2; try discriminate.
              ** apply R_script_char; [exact Hm|exact Ht|].
                 apply IH; [simpl in Hl1; lia|exact Hrun].
              ** apply R_script_group; [exact Hm|exact Ht|].
                 apply IH; [simpl in Hl1; lia|exact Hrun].
        -- injection Hrun as <-. apply R_script_text; exact Hm.
      * (* TCs *)
        destruct (c_defined C n) eqn:Hd; simpl in Hrun.
        -- destruct (c_sig C n) as [sg|] eqn:Hs; [|discriminate].
           destruct (in_math fs) eqn:Hm.
           ++ destruct (sig_math sg) eqn:Hsm.
              ** eapply R_cs_math_noad; try eassumption. apply IH; assumption.
              ** eapply R_cs_math_noop; try eassumption. apply IH; assumption.
              ** injection Hrun as <-. eapply R_cs_math_fatal; eassumption.
           ++ destruct (sig_text sg) eqn:Hst.
              ** eapply R_cs_text_material; try eassumption. apply IH; assumption.
              ** eapply R_cs_text_noop; try eassumption. apply IH; assumption.
              ** injection Hrun as <-. eapply R_cs_text_fatal; eassumption.
        -- injection Hrun as <-. apply R_cs_undefined; exact Hd.
      * (* TEnd *)
        destruct (in_math fs) eqn:Hm.
        -- injection Hrun as <-. apply R_end_math; exact Hm.
        -- destruct so; injection Hrun as <-.
           ++ apply R_end_ok; exact Hm.
           ++ apply R_end_empty; exact Hm.
Qed.

Lemma run_sound : forall C ts s o, run C s ts = Some o -> Runs C s ts o.
Proof. intros C ts s o H. eapply run_sound_n; [apply le_n|exact H]. Qed.

(** ** Completeness: what [Runs] derives, [run] answers *)

Lemma run_complete : forall C s ts o, Runs C s ts o -> run C s ts = Some o.
Proof.
  intros C s ts o H. induction H; simpl.
  - (* R_eof *) reflexivity.
  - (* R_end_ok *) rewrite H. reflexivity.
  - (* R_end_empty *) rewrite H. reflexivity.
  - (* R_end_math *) rewrite H. reflexivity.
  - (* R_char_text *) rewrite H. exact IHRuns.
  - (* R_char_math *) rewrite H. exact IHRuns.
  - (* R_space *) exact IHRuns.
  - (* R_par_text *) rewrite H. exact IHRuns.
  - (* R_par_math *) rewrite H. reflexivity.
  - (* R_open_text *) rewrite H. exact IHRuns.
  - (* R_open_math *) rewrite H. exact IHRuns.
  - (* R_close_simple *) exact IHRuns.
  - (* R_close_group *) exact IHRuns.
  - (* R_close_shift *) reflexivity.
  - (* R_close_top *) reflexivity.
  - (* R_dollar_display_open *)
    destruct fs as [|[|d sp sb|g sp sb] fs']; simpl in H; try discriminate; exact IHRuns.
  - (* R_dollar_inline_open *)
    destruct fs as [|[|d sp sb|g sp sb] fs']; simpl in H; try discriminate;
      (destruct rest as [|[] rest']; simpl in H0; try contradiction; exact IHRuns).
  - (* R_dollar_inline_close *) exact IHRuns.
  - (* R_dollar_display_close *) exact IHRuns.
  - (* R_dollar_display_undef *) rewrite H. reflexivity.
  - (* R_dollar_display_bad *)
    destruct t; simpl in H; try contradiction; try reflexivity.
    destruct H as [Hd Hs]. rewrite Hd.
    destruct (c_sig C n); [reflexivity|]. exfalso. apply Hs. reflexivity.
  - (* R_dollar_display_eof *) reflexivity.
  - (* R_dollar_group *) reflexivity.
  - (* R_mopen_inline *) rewrite H. exact IHRuns.
  - (* R_mopen_inline_bad *) rewrite H. reflexivity.
  - (* R_mclose_inline *) exact IHRuns.
  - (* R_mclose_inline_bad *)
    destruct fs as [|[|[] sp sb|g sp sb] fs']; simpl in H; try contradiction; reflexivity.
  - (* R_mopen_display *) rewrite H. exact IHRuns.
  - (* R_mopen_display_bad *) rewrite H. reflexivity.
  - (* R_mclose_display *) exact IHRuns.
  - (* R_mclose_display_bad *)
    destruct fs as [|[|[] sp sb|g sp sb] fs']; simpl in H; try contradiction; reflexivity.
  - (* R_script_text *) rewrite H. reflexivity.
  - (* R_script_double *) rewrite H, H0. reflexivity.
  - (* R_script_char *) rewrite H, H0. exact IHRuns.
  - (* R_script_group *) rewrite H, H0. exact IHRuns.
  - (* R_cs_undefined *) rewrite H. reflexivity.
  - (* R_cs_text_material *) rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_text_noop *) rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_text_fatal *) rewrite H, H0, H2, H1. reflexivity.
  - (* R_cs_math_noad *) rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_math_noop *) rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_math_fatal *) rewrite H, H0, H2, H1. reflexivity.
Qed.

(** ** Determinism of the semantics, proved on [Runs] itself *)

Theorem runs_deterministic : forall C s ts o1 o2,
  Runs C s ts o1 -> Runs C s ts o2 -> o1 = o2.
Proof.
  intros C s ts o1 o2 Ha. revert o2.
  induction Ha; intros o2 Hb; inversion Hb; subst; simpl in *;
    first
      [ reflexivity
      | apply IHHa; assumption
      | contradiction
      | congruence
      | match goal with
        | [ Hc : _ /\ _ |- _ ] => destruct Hc; congruence
        end ].
Qed.

(** ** Exactness *)

Theorem strict_decider_exact : forall C d,
  in_strict_doc C d ->
  (decide C d = ProvenReady <-> Runs C init (flatten_doc d) Compiles) /\
  (forall r l, decide C d = ProvenNotReady r l <-> Runs C init (flatten_doc d) (Fatal r l)).
Proof.
  intros C d Hs. apply in_strict_b_spec in Hs.
  unfold decide. rewrite Hs. split.
  - split.
    + intro H. apply run_sound.
      destruct (run C init (flatten_doc d)) as [[|r l]|]; simpl in H;
        try discriminate. reflexivity.
    + intro H. apply run_complete in H. rewrite H. reflexivity.
  - intros r l. split.
    + intro H. apply run_sound.
      destruct (run C init (flatten_doc d)) as [[|r' l']|]; simpl in H;
        try discriminate. injection H as <- <-. reflexivity.
    + intro H. apply run_complete in H. rewrite H. reflexivity.
Qed.

(** ** Totality inside the tier *)

Local Ltac fin1 :=
  first [ discriminate
        | match goal with
          | [ H : forall s', run _ s' _ <> None |- _ ] => apply H
          end ].

Lemma run_total_n : forall C k ts s,
  length ts <= k -> in_strict_toks C ts -> run C s ts <> None.
Proof.
  intros C k. induction k as [|k IH]; intros ts s Hlen [Hok Hsc].
  - destruct ts; [|simpl in Hlen; lia]. destruct s; simpl; discriminate.
  - destruct ts as [|t rest]; [destruct s; simpl; discriminate|].
    simpl in Hlen. inversion Hok as [|t' rest' Ht Hrest]; subst.
    assert (Hl1 : length rest <= k) by lia.
    assert (Hsc1 : scripts_ok rest = true).
    { destruct t; simpl in Hsc; try exact Hsc.
      destruct rest as [|[] r]; try discriminate; exact Hsc. }
    assert (IH1 : forall s', run C s' rest <> None)
      by (intro s'; apply IH; [exact Hl1|split; assumption]).
    assert (IH2 : forall t2 rest2 s', rest = t2 :: rest2 -> run C s' rest2 <> None).
    { intros t2 rest2 s' ->. inversion Hrest; subst. apply IH.
      - simpl in Hl1. lia.
      - split; [assumption|]. destruct t2; simpl in Hsc1; try exact Hsc1.
        destruct rest2 as [|[] r]; try discriminate; exact Hsc1. }
    destruct s as [fs so p]. simpl.
    destruct t; simpl.
    + destruct (in_math fs); fin1.
    + fin1.
    + destruct (in_math fs); [discriminate|fin1].
    + destruct (in_math fs); fin1.
    + destruct fs as [|[] fs']; try discriminate; fin1.
    + destruct fs as [|[|d sp sb|g sp sb] fs'].
      * destruct rest as [|t2 rest2]; simpl; [fin1|].
        destruct t2; try fin1. apply (IH2 TDollar rest2); reflexivity.
      * destruct rest as [|t2 rest2]; simpl; [fin1|].
        destruct t2; try fin1. apply (IH2 TDollar rest2); reflexivity.
      * destruct d; [|fin1].
        destruct rest as [|t2 rest2]; simpl; [discriminate|].
        destruct t2; try discriminate.
        -- apply (IH2 TDollar rest2); reflexivity.
        -- inversion Hrest as [|? ? Ht2 _]; subst. simpl in Ht2.
           apply andb_true_iff in Ht2 as [_ Ht2].
           destruct (c_defined C n); [|discriminate].
           destruct (c_sig C n); simpl in *; discriminate.
      * discriminate.
    + destruct (in_math fs); [discriminate|fin1].
    + destruct fs as [|[|[] sp sb|g sp sb] fs']; try discriminate; fin1.
    + destruct (in_math fs); [discriminate|fin1].
    + destruct fs as [|[|[] sp sb|g sp sb] fs']; try discriminate; fin1.
    + destruct (in_math fs); simpl; [|discriminate].
      destruct (tail_has up fs); [discriminate|].
      destruct rest as [|t2 rest2]; [simpl in Hsc; discriminate|].
      simpl in Hsc. destruct t2; try discriminate; simpl;
        eapply IH2; reflexivity.
    + simpl in Ht. apply andb_true_iff in Ht as [_ Ht].
      destruct (c_defined C n); simpl; [|discriminate].
      destruct (c_sig C n) as [sg|]; [|discriminate].
      destruct (in_math fs).
      * destruct (sig_math sg); try discriminate; fin1.
      * destruct (sig_text sg); try discriminate; fin1.
    + destruct (in_math fs); [discriminate|]. destruct so; discriminate.
Qed.

Theorem runs_total : forall C d,
  in_strict_doc C d -> exists o, Runs C init (flatten_doc d) o.
Proof.
  intros C d Hs.
  destruct (run C init (flatten_doc d)) as [o|] eqn:E.
  - exists o. apply run_sound. exact E.
  - exfalso. eapply run_total_n; [apply le_n|exact Hs|exact E].
Qed.

Theorem decide_total : forall C d, in_strict_doc C d -> decide C d <> NotStrict.
Proof.
  intros C d Hs. pose proof Hs as Hs'. apply in_strict_b_spec in Hs'.
  unfold decide. rewrite Hs'.
  destruct (run C init (flatten_doc d)) as [[|r l]|] eqn:E; simpl; try discriminate.
  intros _. eapply run_total_n; [apply le_n|exact Hs|exact E].
Qed.
