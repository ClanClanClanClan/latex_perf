(** * Strict.Decide — the executable decider of L_S0, and its exactness.

    ADR-012 / STRICT_TIER_DESIGN.md §C.3, trust layer (2).  [decide] is an
    ordinary function (extracted to OCaml, Extract.v): a one-token transition
    function [step] iterated by [run] (with [scan_run], TeX's argument
    scanner, once an error inside an argument is deferred).  [Runs]
    (Semantics.v) is the separate declarative relation it is proved equal
    to, in both directions:

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

From Coq Require Import List Bool Ascii Arith Lia.
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
    signature (of a name without arguments, or of a one-argument command).
    A defined name WITHOUT a signature is outside the tier (design §A.1.3:
    never guessed). *)
Definition tok_ok (C : contract) (t : tok) : bool :=
  match t with
  | TChar c => safe_char c
  | TCs n => name_ok n && (negb (c_defined C n) || is_some (c_sig C n) || is_some (c_arg C n))
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

(** A one-argument command, as [step] reads the contract. *)
Definition is_argcmd (C : contract) (n : name) : bool :=
  c_defined C n && negb (is_some (c_sig C n)) && is_some (c_arg C n).

(** ARGUMENTS ARE WELL FORMED (step 2, slice A): every one-argument command
    is immediately followed by the [{] of its argument, and every argument
    closes before [\end{document}] and before the end of the stream.
    [need] counts the braces still to close before the outermost argument
    open at this point closes (0: none is open).  Measured: an argument
    that does not close before the end of the file gives "File ended while
    scanning use of", and one that holds [\end{document}] makes pdfTeX read
    on past it, which the fragment (Front.v) never models; both are outside
    the tier, never a verdict. *)
Fixpoint wfa (C : contract) (need : nat) (ts : list tok) : bool :=
  match ts with
  | [] => Nat.eqb need 0
  | t :: r =>
      match t with
      | TEnd => Nat.eqb need 0
      | TOpen => wfa C (if Nat.eqb need 0 then 0 else S need) r
      | TClose => wfa C (pred need) r
      | TCs n =>
          if is_argcmd C n then
            match r with
            | TOpen :: r' => wfa C (S need) r'
            | _ => false
            end
          else wfa C need r
      | _ => wfa C need r
      end
  end.

Definition in_strict_toks (C : contract) (ts : list tok) : Prop :=
  Forall (fun t => tok_ok C t = true) ts /\ scripts_ok ts = true /\ wfa C 0 ts = true.

(** ** The transition function *)

Inductive step_res :=
| Go1 (s : state)      (* consumed one token *)
| Go2 (s : state)      (* consumed this token and the next *)
| Stop (o : outcome)
| Stuck                (* no rule: outside the tier *)
| Defer (sc : scan)    (* an error inside an argument: scan from this token *)
| Defer2 (sc : scan).  (* read an argument, then stop: scan after this
                          token and the next (the argument's brace) *)

(** A token raises [r] at [l] ([Semantics.Stops]). *)
Definition halt (fs : list frame) (r : reason) (l : nat) : step_res :=
  if in_arg fs then Defer (start_scan fs r) else Stop (Fatal r l).

(** TeX's argument scanner ([Semantics.Scans]). *)
Fixpoint scan_run (sc : scan) (p : nat) (ts : list tok) : option outcome :=
  match ts with
  | [] => None
  | t :: rest =>
      match t with
      | TClose =>
          match sc_k sc with
          | O => None
          | S O => Some (Fatal (sc_r sc) p)
          | S (S k) =>
              scan_run (mkScan (sc_r sc) (S k) (close_sh (S k) (sc_sh sc)) (sc_ou sc)) (S p) rest
          end
      | TOpen => scan_run (mkScan (sc_r sc) (S (sc_k sc)) (sc_sh sc) (sc_ou sc)) (S p) rest
      | TPar _ =>
          if sc_ou sc then Some (Fatal E6 p)
          else if Nat.eqb (sc_sh sc) 0 then scan_run sc (S p) rest
          else scan_run (mkScan E6 (sc_k sc) (sc_sh sc) false) (S p) rest
      | TEnd => None
      | _ => scan_run sc (S p) rest
      end
  end.

Definition step (C : contract) (s : state) (t : tok) (nx : option tok) : step_res :=
  let fs := s_frames s in
  let o := s_out s in
  let p := s_pos s in
  match t with
  | TEnd =>
      if in_arg fs then Stuck
      else if in_math fs then Stop (Fatal E5 p)
      else if o then Stop Compiles else Stop (Fatal E0 p)
  | TChar _ =>
      if in_math fs then Go1 (mkState (fresh_tail fs) o (S p))
      else Go1 (mkState fs true (S p))
  | TSpace => Go1 (mkState fs o (S p))
  | TPar _ =>
      if negb (Nat.eqb (short_depth fs) 0) then halt fs E6 p
      else if in_math fs then halt fs E6 p
      else Go1 (mkState fs o (S p))
  | TOpen =>
      if in_math fs then Go1 (mkState (FMGroup false false false :: fresh_tail fs) o (S p))
      else Go1 (mkState (FSimple :: fs) o (S p))
  | TClose =>
      match fs with
      | FSimple :: r => Go1 (mkState r o (S p))
      | FMGroup _ _ _ :: r => Go1 (mkState r o (S p))
      | FArg _ _ _ _ _ :: r => Go1 (mkState r o (S p))
      | FShift _ _ _ :: _ => halt fs E5 p
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
              then (if is_some (c_sig C n) || is_some (c_arg C n) then halt fs E5 p else Stuck)
              else halt fs E1 (S p)
          | Some _ => halt fs E5 p
          | None => halt fs E5 p
          end
      | _ =>
          if mgroup_head fs then halt fs E5 p
          else if restricted fs then Go1 (mkState (FShift false false false :: fs) true (S p))
          else
            match nx with
            | Some TDollar => Go2 (mkState (FShift true false false :: fs) true (S (S p)))
            | _ => Go1 (mkState (FShift false false false :: fs) true (S p))
            end
      end
  | TMOpenInline =>
      if in_math fs then halt fs E5 p
      else Go1 (mkState (FShift false false false :: fs) true (S p))
  | TMCloseInline =>
      match fs with
      | FShift false _ _ :: r => Go1 (mkState r o (S p))
      | _ => halt fs E5 p
      end
  | TMOpenDisplay =>
      if in_math fs then halt fs E5 p
      else if restricted fs then Go1 (mkState fs o (S p))
      else Go1 (mkState (FShift true false false :: fs) true (S p))
  | TMCloseDisplay =>
      match fs with
      | FShift true _ _ :: r => Go1 (mkState r o (S p))
      | _ => halt fs E5 p
      end
  | TScript up =>
      if negb (in_math fs) then halt fs E3 p
      else if tail_has up fs then halt fs E4 p
      else
        match nx with
        | Some (TChar _) => Go2 (mkState (mark_script up fs) o (S (S p)))
        | Some TOpen => Go2 (mkState (FMGroup true false false :: mark_script up fs) o (S (S p)))
        | _ => Stuck
        end
  | TCs n =>
      if negb (c_defined C n) then halt fs E1 p
      else
        match c_sig C n with
        | Some sg =>
            if in_math fs then
              match sig_math sg with
              | MxNoad => Go1 (mkState (fresh_tail fs) o (S p))
              | MxNoop => Go1 (mkState fs o (S p))
              | MxFatal r => halt fs r p
              end
            else
              match sig_text sg with
              | TxMaterial => Go1 (mkState fs true (S p))
              | TxNoop => Go1 (mkState fs o (S p))
              | TxFatal r => halt fs r p
              end
        | None =>
            match c_arg C n with
            | None => Stuck
            | Some a =>
                if in_math fs then
                  match as_math a with
                  | MFatalNow r => halt fs r p
                  | MFatalAfter r =>
                      match nx with
                      | Some TOpen =>
                          Defer2 (start_scan (FArg (as_long a) (PText false) 0 false false :: fs) r)
                      | _ => Stuck
                      end
                  | MRun pl g =>
                      match nx with
                      | Some TOpen =>
                          Go2 (mkState (FArg (as_long a) pl g false false :: fresh_tail fs) o (S (S p)))
                      | _ => Stuck
                      end
                  end
                else
                  match as_text a with
                  | TFatalNow r => halt fs r p
                  | TFatalAfter r =>
                      match nx with
                      | Some TOpen =>
                          Defer2 (start_scan (FArg (as_long a) (PText false) 0 false false :: fs) r)
                      | _ => Stuck
                      end
                  | TRun m pl g =>
                      match nx with
                      | Some TOpen =>
                          Go2 (mkState (FArg (as_long a) pl g false false :: fs) (o || m) (S (S p)))
                      | _ => Stuck
                      end
                  end
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
      | Defer sc => scan_run sc (s_pos s) (t :: rest)
      | Defer2 sc =>
          match rest with [] => None | _ :: rest' => scan_run sc (S (S (s_pos s))) rest' end
      end
  end.

(** ** TeX's global capacities (corrections C-86, C-94)

    pdfTeX has fixed capacities that no rule of [Runs] models: a document
    that exceeds one stops with "! TeX capacity exceeded" whatever [Runs]
    says.  The fragment is therefore BOUNDED, each bound an account, in the
    model's own terms, of what the capacity counts, never a proxy that the
    grammar can outgrow.  The group account is EXACT (below); the memory and
    dimension accounts are UPPER BOUNDS built from measured per-token costs,
    attested on every graded document, not proved (corrections C-98,
    C-104).  Correction C-94: the first version (C-86) bounded the
    BRACE depth by 200, because 254 nested braces overflow TeX's 255
    grouping levels; but a formula is a TeX group too, and slice A let a
    formula open inside an argument, so [\mbox{$\mbox{$ ... $}$}] held two
    groups per brace and overflowed at 128 levels, inside the old bound
    (a PROVEN-READY that did not compile).  The accounting, with every
    number measured under the pinned oracle
    (corpora/strict_s0/capacity.json, docs/v27/STRICT_TIER_DESIGN.md §I.6):

    - GROUPING LEVELS.  Every frame of the state is ONE TeX group (a text
      brace group, a formula's math-shift group, a math brace group), except
      an argument frame, which is the [g] groups its command holds open
      while the argument runs ([frame_groups]; Contract.v [TRun]/[MRun]).
      So [groups fs] is TeX's grouping level above the body's own.  The body
      holds 254 groups and a 255th overflows, in every frame kind and every
      combination of kinds the capacity probes build; on top of the frames a
      construct adds at most 8 groups while it runs (the output routine, at
      a page break or at \end{document}; \[ adds 3, a paragraph start 1).
      [max_groups] = 200 leaves 54, and 46 above the largest transient.  In
      all 321 frame-kind pairs the model can stack, pdfTeX's first overflow
      is at exactly the account's 255 groups (254 with a paragraph start):
      the account is exact, not just an upper bound.  [peak] is the most groups any state of
      the run holds, the run being [step] iterated as [run] iterates it, up
      to where it stops: a stop halts pdfTeX (-halt-on-error), and the
      argument scanner that locates a deferred error opens no group (pdfTeX
      had read the whole argument before running any of it).
    - BUFFER, STRING POOL, NUMBER OF STRINGS, HASH.  Every control word
      pdfTeX reads is entered in its hash table and string pool, defined or
      not (an argument is read whole, so a stream can make it read up to
      [max_tokens] names).  A name of the fragment has at most [max_name]
      letters ([short_names]): the pool then needs at most
      [max_tokens * max_name] = 2,000,000 characters (5,408,265 are free at
      body start), the strings and the hash at most [max_tokens] entries
      (467,099 and 585,149 free), and a rendered line (Syntax.v [render])
      at most [max_tokens + max_name + 2] bytes (the buffer is 200,000).
    - MAIN MEMORY (correction C-98: the first account said "bounded through
      [max_tokens]", measured on flat documents; an argument nested in an
      argument is COPIED, so memory grows with depth x tokens, and 197
      [\mbox] levels around 6,427 [\frame{}] overflowed inside every other
      bound).  Bounded by its own account, [mem] <= [max_mem] (below): every
      token its measured cost, every argument's tokens its command's
      measured copy factor.  With the 435,796 words pdfTeX reports at body
      start, the account stays under half of main memory.  The costs are
      MEASURED, as slopes of pdfTeX's reported memory over the count (C-104:
      the first version divided by the count, which a high-water mark at
      body start hides up to 31,000 words of, and so under-counted up to
      1.25x), and pdfTeX's report is under the account on every graded
      document; the account is not proved to bound pdfTeX's memory, the
      bound leaves more than 2x for that (§I.6).
    - DIMENSIONS (correction C-104).  TeX stores a dimension as a signed
      32-bit count of sp and adds widths without an overflow check: a
      display of 3,277 [\quad] (32,770pt, just past 2^31 sp) wraps to a
      negative width, skips the squeeze of tex.web §1199, and LaTeX's
      shipout stops with "! Dimension too large" (the round-1 review's
      document, PROVEN-READY before this bound).  Every dimension pdfTeX
      stores or scans while it typesets a paragraph (a box's width, height
      and depth, a shift, a line's active width) is a sum of the dimensions
      of the nodes the paragraph's tokens make, each with a coefficient of
      at most one, plus constants of the layout; a page holds at most one
      item past its goal.  A glue's SETTING is not bounded by the account
      (C-105: stretch of opposite signs cancels, and a line forced by
      [\break] is set past a ratio of 20,000): tex.web keeps it as a ratio
      and computes a set width only at shipout, clamped (vet_glue) and never
      stored or scanned; that rests on this reading and on the rule probes'
      family GLUESET, not on [dim].  [dim] (below) is the largest
      sum, over the SEGMENTS of the run (the tokens between two paragraph
      breaks at the top level, where TeX ends the paragraph), of the
      tokens' measured [c_dim]; [bounded] requires [dim] <= [max_dim] =
      8,000pt, under half of TeX's largest dimension (16,383.99998pt).  The
      account is argued and attested (every name repeated to the bound in
      every mode compiles, one more is outside; every pair of tokens'
      dimensions is under the sum of their costs), not proved.
    - SAVE STACK, INPUT STACK, PARAMETER STACK, SEMANTIC NEST, EXPANSION
      DEPTH, FONTS.  Each grows at most by a constant per running frame or
      group (bounded by [max_groups]) or per token read (bounded by
      [max_tokens]), never by their product: the design's table gives the
      account of each and pdfTeX's own report of it, maximised over every
      graded document, the memory worst cases and the overflow searches past
      the bounds included (the semantic nest 26%, every other one at most
      10%).
    A document beyond a bound is outside the tier: never a verdict.  Every
    attested name is probed at the bounds (families R-NEST-*, R-BIG-* of
    gen_strict_signatures.py; A-R-*, A-CAP-* of gen_strict_arg_signatures.py),
    and every combination of frame kinds the model can stack at the bound
    and one group past it (S0/capacity, checked by check_strict_kernel.py). *)

(* Written as products so that the extraction (nat = OCaml int, successor
   chains for literals) stays short: 200, 20,000 and 100. *)
Definition ten : nat := 10.
Definition max_groups : nat := Nat.mul 2 (Nat.mul ten ten).
Definition max_tokens : nat := Nat.mul max_groups (Nat.mul ten ten).
Definition max_name : nat := Nat.mul ten ten.
Definition max_mem : nat := Nat.mul max_tokens (Nat.mul ten ten).
Definition max_dim : nat := Nat.mul 8 (Nat.mul ten (Nat.mul ten ten)).

Example max_groups_is_200 : max_groups = 200.
Proof. reflexivity. Qed.

Example max_tokens_is_20000 : max_tokens = Nat.mul 200 100.
Proof. reflexivity. Qed.

Example max_name_is_100 : max_name = 100.
Proof. reflexivity. Qed.

(* 2,000,000 words: with the 435,796 words pdfTeX reports at body start,
   under half of main memory (5,000,000) *)
Example max_mem_is_100_tokens : max_mem = Nat.mul max_tokens 100.
Proof. reflexivity. Qed.

(* 8,000pt: under half of TeX's largest dimension, 16,383.99998pt *)
Example max_dim_is_8000 : max_dim = Nat.mul 80 100.
Proof. reflexivity. Qed.

(** The TeX groups a frame holds. *)
Definition frame_groups (f : frame) : nat :=
  match f with
  | FArg _ _ g _ _ => g
  | _ => 1
  end.

(** TeX's grouping level above the body's own: the groups of every frame. *)
Fixpoint groups (fs : list frame) : nat :=
  match fs with
  | [] => 0
  | f :: r => frame_groups f + groups r
  end.

(** The most groups a state of the run from [s] holds ([run]'s steps). *)
Fixpoint peak (C : contract) (s : state) (ts : list tok) : nat :=
  match ts with
  | [] => groups (s_frames s)
  | t :: rest =>
      Nat.max (groups (s_frames s))
        (match step C s t (hd_error rest) with
         | Go1 s' => peak C s' rest
         | Go2 s' => match rest with [] => 0 | _ :: rest' => peak C s' rest' end
         | _ => 0
         end)
  end.

(** The states the run from [s] passes through, declaratively. *)
Inductive Reaches (C : contract) : state -> list tok -> state -> Prop :=
| Reach_here : forall s ts, Reaches C s ts s
| Reach_go1 : forall s t rest s' s'',
    step C s t (hd_error rest) = Go1 s' -> Reaches C s' rest s'' ->
    Reaches C s (t :: rest) s''
| Reach_go2 : forall s t t2 rest s' s'',
    step C s t (Some t2) = Go2 s' -> Reaches C s' rest s'' ->
    Reaches C s (t :: t2 :: rest) s''.

(* A step that consumes nothing more: the state itself is the only one. *)
Local Ltac peak_nogo E :=
  split;
  [ intros [H1 _] s' R; inversion R as [|? ? ? s1' ? E' R'|? ? ? ? s1' ? E' R']; subst;
    [ exact H1
    | rewrite E in E'; discriminate
    | cbn [hd_error] in E, E'; rewrite E in E'; discriminate ]
  | intros H; split; [apply H; constructor|lia] ].

(** [peak] is the maximum over the reached states. *)
Lemma peak_spec_n : forall C k ts s B, length ts <= k ->
  (peak C s ts <= B <-> forall s', Reaches C s ts s' -> groups (s_frames s') <= B).
Proof.
  intros C k. induction k as [|k IH]; intros ts s B Hl.
  - destruct ts; [|simpl in Hl; lia]. cbn [peak]. split.
    + intros H s' R. inversion R; subst. exact H.
    + intros H. apply H. constructor.
  - destruct ts as [|t rest].
    + cbn [peak]. split.
      * intros H s' R. inversion R; subst. exact H.
      * intros H. apply H. constructor.
    + simpl in Hl. cbn [peak]. rewrite Nat.max_lub_iff.
      destruct (step C s t (hd_error rest)) as [s1|s1|o| |sc|sc] eqn:E.
      * rewrite (IH rest s1 B) by lia. split.
        -- intros [H1 H2] s' R. inversion R as [|? ? ? s1' ? E' R'|? ? t2 ? s1' ? E' R']; subst.
           ++ exact H1.
           ++ rewrite E in E'. injection E' as <-. apply H2. exact R'.
           ++ cbn [hd_error] in E, E'. rewrite E in E'. discriminate.
        -- intros H. split; [apply H; constructor|].
           intros s' R. apply H. eapply Reach_go1; eassumption.
      * destruct rest as [|t2 rest'].
        -- split.
           ++ intros [H1 _] s' R. inversion R as [|? ? ? s1' ? E' R'|]; subst; [exact H1|].
              cbn [hd_error] in E, E'. rewrite E in E'. discriminate.
           ++ intros H. split; [apply H; constructor|lia].
        -- simpl in Hl. rewrite (IH rest' s1 B) by lia. split.
           ++ intros [H1 H2] s' R.
              inversion R as [|? ? ? s1' ? E' R'|? ? ? ? s1' ? E' R']; subst.
              ** exact H1.
              ** rewrite E in E'. discriminate.
              ** cbn [hd_error] in E, E'. rewrite E in E'. injection E' as <-. apply H2. exact R'.
           ++ intros H. split; [apply H; constructor|].
              intros s' R. apply H. eapply Reach_go2; [exact E|exact R].
      * peak_nogo E.
      * peak_nogo E.
      * peak_nogo E.
      * peak_nogo E.
Qed.

Theorem peak_spec : forall C ts s B,
  peak C s ts <= B <-> forall s', Reaches C s ts s' -> groups (s_frames s') <= B.
Proof. intros C ts s B. apply (peak_spec_n C (length ts)). apply le_n. Qed.

(** Every control word has at most [max_name] letters. *)
Definition short_names (ts : list tok) : bool :=
  forallb (fun t => match t with TCs n => Nat.leb (length n) max_name | _ => true end) ts.

(** MAIN MEMORY (correction C-98).  pdfTeX's main memory holds what the
    format and the class leave at body start, the nodes the typeset material
    makes, and a COPY of every argument a command is running: an argument
    command nested inside another argument reads its argument out of the
    outer copy, so the copies grow with depth x tokens (the reviewer's
    document: 197 [\mbox] levels around 6,427 [\frame{}] overflow "[main
    memory size=5000000]" with 19,983 tokens and 200 groups).  The account:
    [mem C ts] = the sum of the tokens' costs ([c_cost]) plus, for every
    argument the stream reads, its command's [as_copy] per token inside it
    ([held]: for each token, the copy factors of the arguments open around
    it, the command name and the brace of an inner argument included).  It
    over-counts what is held at once (sibling arguments are not alive
    together) and charges every token its worst measured cost, never less.
    [opens] holds, for each open argument, the brace depth at which it was
    opened and its command's copy factor; a [}] back to that depth closes
    it. *)
Definition copy_of (C : contract) (n : name) : nat :=
  match c_arg C n with Some a => as_copy a | None => 0 end.

Fixpoint open_copies (opens : list (nat * nat)) : nat :=
  match opens with [] => 0 | (_, c) :: r => c + open_copies r end.

Fixpoint held_from (C : contract) (b : nat) (opens : list (nat * nat)) (ts : list tok) : nat :=
  match ts with
  | [] => 0
  | t :: r =>
      open_copies opens +
      match t with
      | TCs n =>
          if is_argcmd C n then
            match r with
            | TOpen :: r' => open_copies opens + held_from C (S b) ((b, copy_of C n) :: opens) r'
            | _ => held_from C b opens r
            end
          else held_from C b opens r
      | TOpen => held_from C (S b) opens r
      | TClose => held_from C (pred b) (filter (fun x => Nat.ltb (fst x) (pred b)) opens) r
      | _ => held_from C b opens r
      end
  end.

Definition held (C : contract) (ts : list tok) : nat := held_from C 0 [] ts.

Fixpoint node_cost (C : contract) (ts : list tok) : nat :=
  match ts with [] => 0 | t :: r => c_cost C t + node_cost C r end.

Definition mem (C : contract) (ts : list tok) : nat := node_cost C ts + held C ts.

(** DIMENSIONS (correction C-104).  [dim_run C s acc ts]: the run from [s]
    ([run]'s steps, up to where it stops: a stop halts pdfTeX, and the
    argument scanner that locates a deferred error typesets nothing), with
    [acc] the dimensions of the current segment so far (each token costs its
    [c_dim] in the mode it runs in: math iff the innermost frame is a
    formula, a math group or an argument run in math); a paragraph break
    read at the top level (no frame open: text, outside every group,
    formula and argument) ends the paragraph in TeX, and the next segment
    starts with that break's own cost (a paragraph's indent and fill).  The
    result is the largest segment. *)
Definition seg_start (s : state) (t : tok) : bool :=
  match t, s_frames s with
  | TPar _, [] => true
  | _, _ => false
  end.

(* The larger of two, by [Nat.leb] (extracted to OCaml's comparison):
   [Nat.max] is extracted as a recursion on its arguments (unary), which at
   a dimension account's values (thousands) makes the run quadratic. *)
Definition maxl (a b : nat) : nat := if Nat.leb a b then b else a.

Fixpoint dim_run (C : contract) (s : state) (acc : nat) (ts : list tok) : nat :=
  match ts with
  | [] => acc
  | t :: rest =>
      let m := in_math (s_frames s) in
      let a := if seg_start s t then c_dim C m t else acc + c_dim C m t in
      maxl a
        (match step C s t (hd_error rest) with
         | Go1 s' => dim_run C s' a rest
         | Go2 s' =>
             match rest with
             | [] => a
             | t2 :: rest' => dim_run C s' (a + c_dim C m t2) rest'
             end
         | _ => a
         end)
  end.

Definition dim (C : contract) (ts : list tok) : nat :=
  dim_run C init (c_dim C false (TPar false)) ts.

Definition bounded (C : contract) (ts : list tok) : bool :=
  Nat.leb (length ts) max_tokens && short_names ts && Nat.leb (peak C init ts) max_groups
  && Nat.leb (mem C ts) max_mem && Nat.leb (dim C ts) max_dim.

Definition in_strict_doc (C : contract) (d : doc) : Prop :=
  in_strict_toks C (flatten_doc d) /\ bounded C (flatten_doc d) = true.

Definition in_strict_b (C : contract) (d : doc) : bool :=
  forallb (tok_ok C) (flatten_doc d) && scripts_ok (flatten_doc d)
  && wfa C 0 (flatten_doc d) && bounded C (flatten_doc d).

Lemma in_strict_b_spec : forall C d, in_strict_b C d = true <-> in_strict_doc C d.
Proof.
  intros C d. unfold in_strict_b, in_strict_doc, in_strict_toks.
  rewrite !andb_true_iff, forallb_forall, Forall_forall. tauto.
Qed.

Theorem in_strict_dec : forall C d, {in_strict_doc C d} + {~ in_strict_doc C d}.
Proof.
  intros C d. destruct (in_strict_b C d) eqn:E.
  - left. apply in_strict_b_spec. exact E.
  - right. intro H. apply in_strict_b_spec in H. rewrite H in E. discriminate.
Qed.

(** A document of the tier: its run never holds more than [max_groups]
    groups, in any state it reaches. *)
Corollary strict_groups_bounded : forall C d s,
  in_strict_doc C d -> Reaches C init (flatten_doc d) s -> groups (s_frames s) <= max_groups.
Proof.
  intros C d s [_ Hb] R. unfold bounded in Hb. rewrite !andb_true_iff in Hb.
  destruct Hb as [[[_ Hp] _] _]. apply Nat.leb_le in Hp.
  exact (proj1 (peak_spec C _ init max_groups) Hp s R).
Qed.

(** C-98: a document of the tier stays within the main-memory account.
    DEFINITIONAL: the membership includes the bound.  That the account bounds
    pdfTeX's main memory is part of the attested premise [Faithful]
    (Bridge.v), not of this statement. *)
Corollary strict_mem_bounded : forall C d,
  in_strict_doc C d -> mem C (flatten_doc d) <= max_mem.
Proof.
  intros C d [_ Hb]. unfold bounded in Hb. rewrite !andb_true_iff in Hb.
  destruct Hb as [[_ Hh] _]. apply Nat.leb_le in Hh. exact Hh.
Qed.

(** C-104: every segment of a document of the tier stays within the
    dimension account.  DEFINITIONAL, like [strict_mem_bounded]: that the
    account bounds pdfTeX's dimensions is part of [Faithful]. *)
Corollary strict_dim_bounded : forall C d,
  in_strict_doc C d -> dim C (flatten_doc d) <= max_dim.
Proof.
  intros C d [_ Hb]. unfold bounded in Hb. rewrite !andb_true_iff in Hb.
  destruct Hb as [_ Hd]. apply Nat.leb_le in Hd. exact Hd.
Qed.

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

(** ** The scanner: [scan_run] is [Scans], both ways *)

Lemma scan_run_sound : forall ts sc p o, scan_run sc p ts = Some o -> Scans sc p ts o.
Proof.
  induction ts as [|t rest IH]; intros [r k sh ou] p o H; [discriminate|].
  destruct t; cbn [scan_run sc_r sc_k sc_sh sc_ou] in H;
    try (apply SC_skip; [exact I|apply IH; exact H]).
  - (* TPar *)
    destruct ou.
    + injection H as <-. apply SC_par_outer.
    + destruct (Nat.eqb sh 0) eqn:E.
      * apply Nat.eqb_eq in E. subst sh. apply SC_par_long. apply IH. exact H.
      * apply Nat.eqb_neq in E. apply SC_par_short; [exact E|]. apply IH. exact H.
  - (* TOpen *) apply SC_open. apply IH. exact H.
  - (* TClose *)
    destruct k as [|[|k]]; [discriminate| |].
    + injection H as <-. apply SC_close_last.
    + apply SC_close. apply IH. exact H.
  - (* TEnd *) discriminate.
Qed.

Lemma scan_run_complete : forall sc p ts o, Scans sc p ts o -> scan_run sc p ts = Some o.
Proof.
  intros sc p ts o H. induction H; cbn [scan_run sc_r sc_k sc_sh sc_ou].
  - reflexivity.
  - exact IHScans.
  - exact IHScans.
  - reflexivity.
  - apply Nat.eqb_neq in H. rewrite H. exact IHScans.
  - exact IHScans.
  - destruct t; simpl in H; try contradiction; exact IHScans.
Qed.

(** Proved on [Scans] itself, like [runs_deterministic]. *)
Theorem scans_deterministic : forall sc p ts o1 o2,
  Scans sc p ts o1 -> Scans sc p ts o2 -> o1 = o2.
Proof.
  intros sc p ts o1 o2 H1. revert o2.
  induction H1; intros o2 H2; inversion H2; subst; simpl in *;
    first [ reflexivity | contradiction | congruence | (apply IHScans; assumption) ].
Qed.

Definition halt_out (fs : list frame) (p : nat) (r : reason) (l : nat) (ts : list tok)
  : option outcome :=
  if in_arg fs then scan_run (start_scan fs r) p ts else Some (Fatal r l).

Lemma halt_out_sound : forall fs p r l ts o, halt_out fs p r l ts = Some o -> Stops fs p r l ts o.
Proof.
  intros fs p r l ts o H. unfold halt_out in H. destruct (in_arg fs) eqn:A.
  - apply Stop_defer; [exact A|]. apply scan_run_sound. exact H.
  - injection H as <-. apply Stop_now. exact A.
Qed.

Lemma halt_out_complete : forall fs p r l ts o, Stops fs p r l ts o -> halt_out fs p r l ts = Some o.
Proof.
  intros fs p r l ts o H. unfold halt_out. destruct H as [fs p r l ts A|fs p r l ts o A S].
  - rewrite A. reflexivity.
  - rewrite A. apply scan_run_complete. exact S.
Qed.

Theorem stops_deterministic : forall fs p r l ts o1 o2,
  Stops fs p r l ts o1 -> Stops fs p r l ts o2 -> o1 = o2.
Proof.
  intros fs p r l ts o1 o2 H1 H2.
  destruct H1 as [fs p r l ts A|fs p r l ts o A S];
    inversion H2 as [fs' p' r' l' ts' A'|fs' p' r' l' ts' o' A' S']; subst; try congruence.
  eapply scans_deterministic; eassumption.
Qed.

Lemma run_step : forall C s t rest,
  run C s (t :: rest) =
  match step C s t (hd_error rest) with
  | Go1 s' => run C s' rest
  | Go2 s' => match rest with [] => None | _ :: rest' => run C s' rest' end
  | Stop o => Some o
  | Stuck => None
  | Defer sc => scan_run sc (s_pos s) (t :: rest)
  | Defer2 sc =>
      match rest with [] => None | _ :: rest' => scan_run sc (S (S (s_pos s))) rest' end
  end.
Proof. reflexivity. Qed.

Lemma run_halt : forall C s t rest fs r l,
  step C s t (hd_error rest) = halt fs r l ->
  run C s (t :: rest) = halt_out fs (s_pos s) r l (t :: rest).
Proof.
  intros C s t rest fs r l H. rewrite run_step, H. unfold halt, halt_out.
  destruct (in_arg fs); reflexivity.
Qed.

(** ** Soundness: what [run] answers, [Runs] derives *)

(* Solve a goal [Runs ... (t :: rest) o] whose step is a [halt]. *)
Local Ltac by_halt Hrun :=
  first
    [ rewrite (run_halt _ _ _ _ _ _ _ eq_refl) in Hrun; apply halt_out_sound in Hrun
    | idtac ].

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
      destruct s as [fs so p].
      destruct t.
      * (* TChar *)
        rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
        destruct (in_math fs) eqn:Hm.
        -- apply R_char_math; [exact Hm|]. apply IH; assumption.
        -- apply R_char_text; [exact Hm|]. apply IH; assumption.
      * (* TSpace *)
        rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
        apply R_space. apply IH; assumption.
      * (* TPar *)
        destruct (Nat.eqb (short_depth fs) 0) eqn:Hsd.
        -- apply Nat.eqb_eq in Hsd.
           destruct (in_math fs) eqn:Hm.
           ++ apply R_par_math; [exact Hm|exact Hsd|].
              rewrite (run_halt C (mkState fs so p) _ _ fs E6 p) in Hrun
                by (cbn [step s_frames s_out s_pos]; rewrite Hsd, Hm; reflexivity).
              apply halt_out_sound. exact Hrun.
           ++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
              rewrite Hsd, Hm in Hrun. cbn in Hrun.
              apply R_par_text; [exact Hm|exact Hsd|]. apply IH; assumption.
        -- apply Nat.eqb_neq in Hsd. apply R_par_short; [exact Hsd|].
           rewrite (run_halt C (mkState fs so p) _ _ fs E6 p) in Hrun
             by (cbn [step s_frames s_out s_pos]; apply Nat.eqb_neq in Hsd; rewrite Hsd; reflexivity).
           apply halt_out_sound. exact Hrun.
      * (* TOpen *)
        rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
        destruct (in_math fs) eqn:Hm.
        -- apply R_open_math; [exact Hm|]. apply IH; assumption.
        -- apply R_open_text; [exact Hm|]. apply IH; assumption.
      * (* TClose *)
        destruct fs as [|f fs'].
        -- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
           injection Hrun as <-. apply R_close_top.
        -- destruct f as [|d sp sb|g sp sb|l pl ga sp sb].
           ++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
              apply R_close_simple. apply IH; assumption.
           ++ apply R_close_shift.
              rewrite (run_halt C _ _ _ (FShift d sp sb :: fs') E5 p) in Hrun by reflexivity.
              apply halt_out_sound. exact Hrun.
           ++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
              apply R_close_group. apply IH; assumption.
           ++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
              apply R_close_arg. apply IH; assumption.
      * (* TDollar *)
        destruct fs as [|f fs'] eqn:Efs.
        -- (* top: text, unrestricted *)
           rewrite run_step in Hrun. cbn [step s_frames s_out s_pos mgroup_head restricted] in Hrun.
           destruct rest as [|t2 rest2].
           ++ apply R_dollar_inline_open; [reflexivity|reflexivity|exact I|].
              apply IH; [simpl; lia|exact Hrun].
           ++ destruct t2; cbn [hd_error] in Hrun;
              try (apply R_dollar_inline_open; [reflexivity|reflexivity|exact I|apply IH; assumption]).
              apply R_dollar_display_open; [reflexivity|reflexivity|].
              apply IH; [simpl in Hl1; lia|exact Hrun].
        -- destruct f as [|d sp sb|g sp sb|l pl ga sp sb].
           ++ (* FSimple: text *)
              destruct (restricted (FSimple :: fs')) eqn:Hr.
              ** rewrite run_step in Hrun. cbn [step s_frames s_out s_pos mgroup_head] in Hrun.
                 rewrite Hr in Hrun.
                 apply R_dollar_restricted_open; [reflexivity|exact Hr|]. apply IH; assumption.
              ** rewrite run_step in Hrun. cbn [step s_frames s_out s_pos mgroup_head] in Hrun.
                 rewrite Hr in Hrun.
                 destruct rest as [|t2 rest2].
                 --- apply R_dollar_inline_open; [reflexivity|exact Hr|exact I|].
                     apply IH; [simpl; lia|exact Hrun].
                 --- destruct t2; cbn [hd_error] in Hrun;
                     try (apply R_dollar_inline_open; [reflexivity|exact Hr|exact I|apply IH; assumption]).
                     apply R_dollar_display_open; [reflexivity|exact Hr|].
                     apply IH; [simpl in Hl1; lia|exact Hrun].
           ++ destruct d.
              ** (* display *)
                 destruct rest as [|t2 rest2].
                 --- apply R_dollar_display_eof.
                     rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E5 p) in Hrun by reflexivity.
                     apply halt_out_sound. exact Hrun.
                 --- destruct t2 eqn:Et2.
                     all: try (apply R_dollar_display_bad; [exact I|];
                               rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E5 p) in Hrun by reflexivity;
                               apply halt_out_sound; exact Hrun).
                     +++ (* $$ *)
                         rewrite run_step in Hrun. cbn [step s_frames s_out s_pos hd_error] in Hrun.
                         apply R_dollar_display_close. apply IH; [simpl in Hl1; lia|exact Hrun].
                     +++ (* control word *)
                         destruct (c_defined C n) eqn:Hd.
                         *** destruct (is_some (c_sig C n) || is_some (c_arg C n)) eqn:Hs.
                             ---- apply R_dollar_display_bad.
                                  { simpl. split; [exact Hd|].
                                    apply orb_true_iff in Hs as [Hs|Hs];
                                      [left|right]; destruct (c_sig C n), (c_arg C n);
                                      simpl in Hs; try discriminate; discriminate. }
                                  rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E5 p) in Hrun
                                    by (cbn [step s_frames s_out s_pos hd_error]; rewrite Hd, Hs; reflexivity).
                                  apply halt_out_sound. exact Hrun.
                             ---- rewrite run_step in Hrun.
                                  cbn [step s_frames s_out s_pos hd_error] in Hrun.
                                  rewrite Hd, Hs in Hrun. discriminate.
                         *** apply R_dollar_display_undef; [exact Hd|].
                             rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E1 (S p)) in Hrun
                               by (cbn [step s_frames s_out s_pos hd_error]; rewrite Hd; reflexivity).
                             apply halt_out_sound. exact Hrun.
              ** (* inline *)
                 rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
                 apply R_dollar_inline_close. apply IH; assumption.
           ++ (* math brace group *)
              apply R_dollar_group; [reflexivity|].
              rewrite (run_halt C _ _ _ (FMGroup g sp sb :: fs') E5 p) in Hrun by reflexivity.
              apply halt_out_sound. exact Hrun.
           ++ destruct pl as [b|].
              ** (* text argument *)
                 destruct b.
                 --- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos mgroup_head restricted] in Hrun.
                     apply R_dollar_restricted_open; [reflexivity|reflexivity|]. apply IH; assumption.
                 --- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos mgroup_head restricted] in Hrun.
                     destruct rest as [|t2 rest2].
                     +++ apply R_dollar_inline_open; [reflexivity|reflexivity|exact I|].
                         apply IH; [simpl; lia|exact Hrun].
                     +++ destruct t2; cbn [hd_error] in Hrun;
                         try (apply R_dollar_inline_open; [reflexivity|reflexivity|exact I|apply IH; assumption]).
                         apply R_dollar_display_open; [reflexivity|reflexivity|].
                         apply IH; [simpl in Hl1; lia|exact Hrun].
              ** (* math argument *)
                 apply R_dollar_group; [reflexivity|].
                 rewrite (run_halt C _ _ _ (FArg l PMath ga sp sb :: fs') E5 p) in Hrun by reflexivity.
                 apply halt_out_sound. exact Hrun.
      * (* TMOpenInline *)
        destruct (in_math fs) eqn:Hm.
        -- apply R_mopen_inline_bad; [exact Hm|].
           rewrite (run_halt C _ _ _ fs E5 p) in Hrun
             by (cbn [step s_frames s_out s_pos]; rewrite Hm; reflexivity).
           apply halt_out_sound. exact Hrun.
        -- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun. rewrite Hm in Hrun.
           apply R_mopen_inline; [exact Hm|]. apply IH; assumption.
      * (* TMCloseInline *)
        destruct fs as [|[|[] sp sb|g sp sb|l pl ga sp sb] fs'];
          try (apply R_mclose_inline_bad; [exact I|];
               rewrite (run_halt C _ _ _ _ E5 p) in Hrun by reflexivity;
               apply halt_out_sound; exact Hrun).
        rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
        apply R_mclose_inline. apply IH; assumption.
      * (* TMOpenDisplay *)
        destruct (in_math fs) eqn:Hm.
        -- apply R_mopen_display_bad; [exact Hm|].
           rewrite (run_halt C _ _ _ fs E5 p) in Hrun
             by (cbn [step s_frames s_out s_pos]; rewrite Hm; reflexivity).
           apply halt_out_sound. exact Hrun.
        -- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun. rewrite Hm in Hrun.
           destruct (restricted fs) eqn:Hr.
           ++ apply R_mopen_display_restricted; [exact Hm|exact Hr|]. apply IH; assumption.
           ++ apply R_mopen_display; [exact Hm|exact Hr|]. apply IH; assumption.
      * (* TMCloseDisplay *)
        destruct fs as [|[|[] sp sb|g sp sb|l pl ga sp sb] fs'];
          try (apply R_mclose_display_bad; [exact I|];
               rewrite (run_halt C _ _ _ _ E5 p) in Hrun by reflexivity;
               apply halt_out_sound; exact Hrun).
        rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
        apply R_mclose_display. apply IH; assumption.
      * (* TScript *)
        destruct (in_math fs) eqn:Hm.
        -- destruct (tail_has up fs) eqn:Ht.
           ++ apply R_script_double; [exact Hm|exact Ht|].
              rewrite (run_halt C _ _ _ fs E4 p) in Hrun
                by (cbn [step s_frames s_out s_pos]; rewrite Hm, Ht; reflexivity).
              apply halt_out_sound. exact Hrun.
           ++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
              rewrite Hm, Ht in Hrun. cbn [negb] in Hrun.
              destruct rest as [|t2 rest2]; [discriminate|].
              cbn [hd_error] in Hrun. destruct t2; try discriminate.
              ** apply R_script_char; [exact Hm|exact Ht|].
                 apply IH; [simpl in Hl1; lia|exact Hrun].
              ** apply R_script_group; [exact Hm|exact Ht|].
                 apply IH; [simpl in Hl1; lia|exact Hrun].
        -- apply R_script_text; [exact Hm|].
           rewrite (run_halt C _ _ _ fs E3 p) in Hrun
             by (cbn [step s_frames s_out s_pos]; rewrite Hm; reflexivity).
           apply halt_out_sound. exact Hrun.
      * (* TCs *)
        destruct (c_defined C n) eqn:Hd.
        -- destruct (c_sig C n) as [sg|] eqn:Hs.
           ++ destruct (in_math fs) eqn:Hm.
              ** destruct (sig_math sg) eqn:Hsm.
                 --- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                     rewrite Hd, Hs, Hm, Hsm in Hrun. cbn [negb] in Hrun.
                     eapply R_cs_math_noad; try eassumption. apply IH; assumption.
                 --- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                     rewrite Hd, Hs, Hm, Hsm in Hrun. cbn [negb] in Hrun.
                     eapply R_cs_math_noop; try eassumption. apply IH; assumption.
                 --- eapply R_cs_math_fatal; try eassumption.
                     rewrite (run_halt C _ _ _ fs r p) in Hrun
                       by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Hm, Hsm; reflexivity).
                     apply halt_out_sound. exact Hrun.
              ** destruct (sig_text sg) eqn:Hst.
                 --- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                     rewrite Hd, Hs, Hm, Hst in Hrun. cbn [negb] in Hrun.
                     eapply R_cs_text_material; try eassumption. apply IH; assumption.
                 --- rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                     rewrite Hd, Hs, Hm, Hst in Hrun. cbn [negb] in Hrun.
                     eapply R_cs_text_noop; try eassumption. apply IH; assumption.
                 --- eapply R_cs_text_fatal; try eassumption.
                     rewrite (run_halt C _ _ _ fs r p) in Hrun
                       by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Hm, Hst; reflexivity).
                     apply halt_out_sound. exact Hrun.
           ++ destruct (c_arg C n) as [a|] eqn:Ha.
              ** destruct (in_math fs) eqn:Hm.
                 --- destruct (as_math a) as [r|r|pl ga] eqn:Ham.
                     +++ eapply R_arg_math_now; try eassumption.
                         rewrite (run_halt C _ _ _ fs r p) in Hrun
                           by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Ha, Hm, Ham; reflexivity).
                         apply halt_out_sound. exact Hrun.
                     +++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                         rewrite Hd, Hs, Ha, Hm, Ham in Hrun. cbn [negb] in Hrun.
                         destruct rest as [|t2 rest2]; [discriminate|].
                         cbn [hd_error] in Hrun. destruct t2; try discriminate.
                         eapply R_arg_math_after; try eassumption.
                         apply scan_run_sound. exact Hrun.
                     +++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                         rewrite Hd, Hs, Ha, Hm, Ham in Hrun. cbn [negb] in Hrun.
                         destruct rest as [|t2 rest2]; [discriminate|].
                         cbn [hd_error] in Hrun. destruct t2; try discriminate.
                         eapply R_arg_math_run; try eassumption.
                         apply IH; [simpl in Hl1; lia|exact Hrun].
                 --- destruct (as_text a) as [r|r|m pl ga] eqn:Hat.
                     +++ eapply R_arg_text_now; try eassumption.
                         rewrite (run_halt C _ _ _ fs r p) in Hrun
                           by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Ha, Hm, Hat; reflexivity).
                         apply halt_out_sound. exact Hrun.
                     +++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                         rewrite Hd, Hs, Ha, Hm, Hat in Hrun. cbn [negb] in Hrun.
                         destruct rest as [|t2 rest2]; [discriminate|].
                         cbn [hd_error] in Hrun. destruct t2; try discriminate.
                         eapply R_arg_text_after; try eassumption.
                         apply scan_run_sound. exact Hrun.
                     +++ rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                         rewrite Hd, Hs, Ha, Hm, Hat in Hrun. cbn [negb] in Hrun.
                         destruct rest as [|t2 rest2]; [discriminate|].
                         cbn [hd_error] in Hrun. destruct t2; try discriminate.
                         eapply R_arg_text_run; try eassumption.
                         apply IH; [simpl in Hl1; lia|exact Hrun].
              ** rewrite run_step in Hrun. cbn [step s_frames s_out s_pos negb] in Hrun.
                 rewrite Hd, Hs, Ha in Hrun. discriminate.
        -- apply R_cs_undefined; [exact Hd|].
           rewrite (run_halt C _ _ _ fs E1 p) in Hrun
             by (cbn [step s_frames s_out s_pos]; rewrite Hd; reflexivity).
           apply halt_out_sound. exact Hrun.
      * (* TEnd *)
        rewrite run_step in Hrun. cbn [step s_frames s_out s_pos] in Hrun.
        destruct (in_arg fs) eqn:Ha; [discriminate|].
        destruct (in_math fs) eqn:Hm.
        -- injection Hrun as <-. apply R_end_math; assumption.
        -- destruct so; injection Hrun as <-.
           ++ apply R_end_ok; assumption.
           ++ apply R_end_empty; assumption.
Qed.

Lemma run_sound : forall C ts s o, run C s ts = Some o -> Runs C s ts o.
Proof. intros C ts s o H. eapply run_sound_n; [apply le_n|exact H]. Qed.

(** ** Completeness: what [Runs] derives, [run] answers *)

(* A rule whose conclusion goes through [Stops]: the step is a [halt]. *)
Local Ltac by_stops H :=
  erewrite run_halt; [apply halt_out_complete; exact H|].

Lemma run_complete : forall C s ts o, Runs C s ts o -> run C s ts = Some o.
Proof.
  intros C s ts o H. induction H.
  - (* R_eof *) reflexivity.
  - (* R_end_ok *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0. reflexivity.
  - (* R_end_empty *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0. reflexivity.
  - (* R_end_math *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0. reflexivity.
  - (* R_char_text *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H. exact IHRuns.
  - (* R_char_math *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H. exact IHRuns.
  - (* R_space *) exact IHRuns.
  - (* R_par_text *)
    rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H0, H. exact IHRuns.
  - (* R_par_math *)
    by_stops H1. cbn [step s_frames s_out s_pos]. rewrite H0, H. reflexivity.
  - (* R_par_short *)
    by_stops H0. cbn [step s_frames s_out s_pos].
    apply Nat.eqb_neq in H. rewrite H. reflexivity.
  - (* R_open_text *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H. exact IHRuns.
  - (* R_open_math *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H. exact IHRuns.
  - (* R_close_simple *) exact IHRuns.
  - (* R_close_group *) exact IHRuns.
  - (* R_close_arg *) exact IHRuns.
  - (* R_close_shift *) by_stops H. reflexivity.
  - (* R_close_top *) reflexivity.
  - (* R_dollar_display_open *)
    rewrite run_step.
    destruct fs as [|[|d sp sb|g sp sb|l [b|] ga sp sb] fs']; simpl in H, H0; try discriminate; try subst b;
      cbn [step s_frames s_out s_pos mgroup_head restricted hd_error]; try rewrite H0; exact IHRuns.
  - (* R_dollar_inline_open *)
    rewrite run_step.
    destruct fs as [|[|d sp sb|g sp sb|l [b|] ga sp sb] fs']; simpl in H, H0; try discriminate; try subst b;
      cbn [step s_frames s_out s_pos mgroup_head restricted]; try rewrite H0;
      (destruct rest as [|[] rest']; simpl in H1; try contradiction; exact IHRuns).
  - (* R_dollar_restricted_open *)
    rewrite run_step.
    destruct fs as [|[|d sp sb|g sp sb|l [b|] ga sp sb] fs']; simpl in H, H0; try discriminate; try subst b;
      cbn [step s_frames s_out s_pos mgroup_head restricted]; try rewrite H0; exact IHRuns.
  - (* R_dollar_inline_close *) exact IHRuns.
  - (* R_dollar_display_close *) exact IHRuns.
  - (* R_dollar_display_undef *)
    by_stops H0. cbn [step s_frames s_out s_pos hd_error]. rewrite H. reflexivity.
  - (* R_dollar_display_bad *)
    by_stops H0. cbn [step s_frames s_out s_pos hd_error].
    destruct t; simpl in H; try contradiction; try reflexivity.
    destruct H as [Hd Hs]. rewrite Hd.
    destruct (c_sig C n), (c_arg C n); try reflexivity.
    exfalso. destruct Hs as [Hs|Hs]; apply Hs; reflexivity.
  - (* R_dollar_display_eof *) by_stops H. reflexivity.
  - (* R_dollar_group *)
    by_stops H0.
    destruct fs as [|[|d sp sb|g sp sb|l [b|] ga sp sb] fs']; simpl in H; try discriminate; reflexivity.
  - (* R_mopen_inline *) rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H. exact IHRuns.
  - (* R_mopen_inline_bad *) by_stops H0. cbn [step s_frames s_out s_pos]. rewrite H. reflexivity.
  - (* R_mclose_inline *) exact IHRuns.
  - (* R_mclose_inline_bad *)
    by_stops H0.
    destruct fs as [|[|[] sp sb|g sp sb|l pl ga sp sb] fs']; simpl in H; try contradiction; reflexivity.
  - (* R_mopen_display *)
    rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0. exact IHRuns.
  - (* R_mopen_display_restricted *)
    rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0. exact IHRuns.
  - (* R_mopen_display_bad *) by_stops H0. cbn [step s_frames s_out s_pos]. rewrite H. reflexivity.
  - (* R_mclose_display *) exact IHRuns.
  - (* R_mclose_display_bad *)
    by_stops H0.
    destruct fs as [|[|[] sp sb|g sp sb|l pl ga sp sb] fs']; simpl in H; try contradiction; reflexivity.
  - (* R_script_text *) by_stops H0. cbn [step s_frames s_out s_pos]. rewrite H. reflexivity.
  - (* R_script_double *)
    by_stops H1. cbn [step s_frames s_out s_pos]. rewrite H, H0. reflexivity.
  - (* R_script_char *)
    rewrite run_step. cbn [step s_frames s_out s_pos hd_error]. rewrite H, H0. exact IHRuns.
  - (* R_script_group *)
    rewrite run_step. cbn [step s_frames s_out s_pos hd_error]. rewrite H, H0. exact IHRuns.
  - (* R_cs_undefined *) by_stops H0. cbn [step s_frames s_out s_pos]. rewrite H. reflexivity.
  - (* R_cs_text_material *)
    rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_text_noop *)
    rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_text_fatal *)
    by_stops H3. cbn [step s_frames s_out s_pos]. rewrite H, H0, H2, H1. reflexivity.
  - (* R_cs_math_noad *)
    rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_math_noop *)
    rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite H, H0, H2, H1. exact IHRuns.
  - (* R_cs_math_fatal *)
    by_stops H3. cbn [step s_frames s_out s_pos]. rewrite H, H0, H2, H1. reflexivity.
  - (* R_arg_text_now *)
    by_stops H4. cbn [step s_frames s_out s_pos]. rewrite H, H0, H1, H3, H2. reflexivity.
  - (* R_arg_text_after *)
    rewrite run_step. cbn [step s_frames s_out s_pos hd_error]. rewrite H, H0, H1, H3, H2.
    apply scan_run_complete. exact H4.
  - (* R_arg_text_run *)
    rewrite run_step. cbn [step s_frames s_out s_pos hd_error]. rewrite H, H0, H1, H3, H2.
    exact IHRuns.
  - (* R_arg_math_now *)
    by_stops H4. cbn [step s_frames s_out s_pos]. rewrite H, H0, H1, H3, H2. reflexivity.
  - (* R_arg_math_after *)
    rewrite run_step. cbn [step s_frames s_out s_pos hd_error]. rewrite H, H0, H1, H3, H2.
    apply scan_run_complete. exact H4.
  - (* R_arg_math_run *)
    rewrite run_step. cbn [step s_frames s_out s_pos hd_error]. rewrite H, H0, H1, H3, H2.
    exact IHRuns.
Qed.

(** ** Determinism of the semantics, proved on [Runs] itself *)

Lemma mgroup_in_math : forall fs, mgroup_head fs = true -> in_math fs = true.
Proof. intros [|[|d sp sb|g sp sb|l [b|] ga sp sb] r] H; simpl in H; try discriminate; reflexivity. Qed.

(* Two premises reading the same contract entry name the same entry. *)
Local Ltac unify_entries :=
  repeat match goal with
  | [ H1 : ?x = Some ?a, H2 : ?x = Some ?b |- _ ] =>
      rewrite H1 in H2; injection H2 as <-
  | [ H1 : as_text ?a = TRun ?m ?p ?g, H2 : as_text ?a = TRun ?m' ?p' ?g' |- _ ] =>
      rewrite H1 in H2; injection H2 as <- <- <-
  | [ H1 : as_text ?a = TFatalAfter ?r, H2 : as_text ?a = TFatalAfter ?r' |- _ ] =>
      rewrite H1 in H2; injection H2 as <-
  | [ H1 : as_math ?a = MRun ?p ?g, H2 : as_math ?a = MRun ?p' ?g' |- _ ] =>
      rewrite H1 in H2; injection H2 as <- <-
  | [ H1 : as_math ?a = MFatalAfter ?r, H2 : as_math ?a = MFatalAfter ?r' |- _ ] =>
      rewrite H1 in H2; injection H2 as <-
  | [ H1 : as_text ?a = TFatalNow ?r, H2 : as_text ?a = TFatalNow ?r' |- _ ] =>
      rewrite H1 in H2; injection H2 as <-
  | [ H1 : as_math ?a = MFatalNow ?r, H2 : as_math ?a = MFatalNow ?r' |- _ ] =>
      rewrite H1 in H2; injection H2 as <-
  | [ H1 : sig_text ?a = TxFatal ?r, H2 : sig_text ?a = TxFatal ?r' |- _ ] =>
      rewrite H1 in H2; injection H2 as <-
  | [ H1 : sig_math ?a = MxFatal ?r, H2 : sig_math ?a = MxFatal ?r' |- _ ] =>
      rewrite H1 in H2; injection H2 as <-
  end.

Theorem runs_deterministic : forall C s ts o1 o2,
  Runs C s ts o1 -> Runs C s ts o2 -> o1 = o2.
Proof.
  intros C s ts o1 o2 Ha. revert o2.
  induction Ha; intros o2 Hb; inversion Hb; subst; simpl in *; unify_entries;
    first
      [ reflexivity
      | apply IHHa; assumption
      | contradiction
      | congruence
      | eapply stops_deterministic; eassumption
      | eapply scans_deterministic; eassumption
      | match goal with
        | [ Hc : _ /\ _ |- _ ] => destruct Hc; congruence
        end
      | match goal with
        | [ Hm : mgroup_head ?fs = true, Hi : in_math ?fs = false |- _ ] =>
            rewrite (mgroup_in_math _ Hm) in Hi; discriminate
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

(** The braces [wfa] counts are the brace frames [arg_depth] counts. *)
Lemma arg_depth_out : forall fs, in_arg fs = false -> arg_depth fs = 0.
Proof.
  induction fs as [|f r IH]; intros H; [reflexivity|].
  unfold in_arg in H. cbn [existsb] in H. apply orb_false_iff in H as [H1 H2].
  cbn [arg_depth]. unfold in_arg. rewrite H2, H1. reflexivity.
Qed.

Lemma arg_depth_in : forall fs, in_arg fs = true -> 1 <= arg_depth fs.
Proof.
  induction fs as [|f r IH]; intros H; [discriminate|].
  cbn [arg_depth]. unfold in_arg in *. cbn [existsb] in H.
  destruct (existsb is_arg_frame r) eqn:E.
  - destruct (is_brace f); [lia|]. apply IH. reflexivity.
  - rewrite orb_false_r in H. rewrite H. lia.
Qed.

Lemma arg_depth_zero : forall fs, Nat.eqb (arg_depth fs) 0 = negb (in_arg fs).
Proof.
  intros fs. destruct (in_arg fs) eqn:E.
  - apply Nat.eqb_neq. pose proof (arg_depth_in fs E). lia.
  - rewrite (arg_depth_out fs E). reflexivity.
Qed.

Lemma in_arg_fresh : forall fs, in_arg (fresh_tail fs) = in_arg fs.
Proof. intros [|[] r]; reflexivity. Qed.

Lemma arg_depth_fresh : forall fs, arg_depth (fresh_tail fs) = arg_depth fs.
Proof. intros [|[] r]; reflexivity. Qed.

Lemma in_arg_mark : forall up fs, in_arg (mark_script up fs) = in_arg fs.
Proof. intros up [|[] r]; reflexivity. Qed.

Lemma arg_depth_mark : forall up fs, arg_depth (mark_script up fs) = arg_depth fs.
Proof. intros up [|[] r]; reflexivity. Qed.

(** Pushing a brace frame that is not an argument. *)
Lemma arg_depth_push : forall f fs,
  is_brace f = true -> is_arg_frame f = false ->
  arg_depth (f :: fs) = if Nat.eqb (arg_depth fs) 0 then 0 else S (arg_depth fs).
Proof.
  intros f fs Hb Ha. cbn [arg_depth]. rewrite Hb, Ha, arg_depth_zero.
  destruct (in_arg fs); reflexivity.
Qed.

Lemma arg_depth_push_arg : forall l pl g sp sb fs,
  arg_depth (FArg l pl g sp sb :: fs) = S (arg_depth fs).
Proof.
  intros. cbn [arg_depth is_brace is_arg_frame].
  destruct (in_arg fs) eqn:E; [reflexivity|]. rewrite (arg_depth_out fs E). reflexivity.
Qed.

Lemma arg_depth_shift : forall d sp sb fs, arg_depth (FShift d sp sb :: fs) = arg_depth fs.
Proof.
  intros. cbn [arg_depth is_brace is_arg_frame].
  destruct (in_arg fs) eqn:E; [reflexivity|]. rewrite (arg_depth_out fs E). reflexivity.
Qed.

Lemma arg_depth_pop : forall f fs,
  is_brace f = true -> arg_depth fs = pred (arg_depth (f :: fs)).
Proof.
  intros f fs Hb. cbn [arg_depth]. rewrite Hb.
  destruct (in_arg fs) eqn:E; [reflexivity|].
  rewrite (arg_depth_out fs E). destruct (is_arg_frame f); reflexivity.
Qed.

Lemma scan_total_n : forall C k ts sc p,
  length ts <= k -> 1 <= sc_k sc -> wfa C (sc_k sc) ts = true -> scan_run sc p ts <> None.
Proof.
  intros C k. induction k as [|k IH]; intros ts [r kk sh ou] p Hlen Hk Hw;
    cbn [sc_k] in Hk, Hw.
  - destruct ts; [|simpl in Hlen; lia].
    cbn [wfa] in Hw. apply Nat.eqb_eq in Hw. lia.
  - destruct ts as [|t rest].
    + cbn [wfa] in Hw. apply Nat.eqb_eq in Hw. lia.
    + simpl in Hlen. assert (Hl : length rest <= k) by lia.
      destruct t; cbn [scan_run sc_r sc_k sc_sh sc_ou]; cbn [wfa] in Hw;
        try (apply IH; [exact Hl|exact Hk|exact Hw]).
      * (* TPar *)
        destruct ou; [discriminate|].
        destruct (Nat.eqb sh 0); apply IH; cbn [sc_k]; assumption.
      * (* TOpen *)
        apply IH; cbn [sc_k]; [exact Hl|lia|].
        replace (Nat.eqb kk 0) with false in Hw by (symmetry; apply Nat.eqb_neq; lia).
        exact Hw.
      * (* TClose *)
        destruct kk as [|[|kk]]; [lia|discriminate|].
        apply IH; cbn [sc_k]; [exact Hl|lia|exact Hw].
      * (* TCs *)
        destruct (is_argcmd C n) eqn:Ha.
        -- destruct rest as [|[] r']; try discriminate.
           apply IH; cbn [sc_k]; [exact Hl|exact Hk|].
           cbn [wfa]. replace (Nat.eqb kk 0) with false by (symmetry; apply Nat.eqb_neq; lia).
           exact Hw.
        -- apply IH; cbn [sc_k]; assumption.
      * (* TEnd *) apply Nat.eqb_eq in Hw. lia.
Qed.

Lemma halt_total : forall C fs p r l ts,
  wfa C (arg_depth fs) ts = true -> halt_out fs p r l ts <> None.
Proof.
  intros C fs p r l ts Hw. unfold halt_out. destruct (in_arg fs) eqn:E; [|discriminate].
  apply (scan_total_n C (length ts)); [apply le_n|cbn [start_scan sc_k]; apply arg_depth_in; exact E|].
  exact Hw.
Qed.

Local Ltac halt_tot C Hw :=
  rewrite (run_halt C _ _ _ _ _ _ eq_refl); apply (halt_total C); exact Hw.

Lemma run_total_n : forall C k ts s,
  length ts <= k -> Forall (fun t => tok_ok C t = true) ts -> scripts_ok ts = true ->
  wfa C (arg_depth (s_frames s)) ts = true -> run C s ts <> None.
Proof.
  intros C k. induction k as [|k IH]; intros ts s Hlen Hok Hsc Hw.
  - destruct ts; [|simpl in Hlen; lia]. destruct s; simpl; discriminate.
  - destruct ts as [|t rest]; [destruct s; simpl; discriminate|].
    simpl in Hlen. inversion Hok as [|t' rest' Ht Hrest]; subst.
    assert (Hl1 : length rest <= k) by lia.
    assert (Hsc1 : scripts_ok rest = true).
    { destruct t; simpl in Hsc; try exact Hsc.
      destruct rest as [|[] r]; try discriminate; exact Hsc. }
    destruct s as [fs so p]. cbn [s_frames] in Hw.
    set (d := arg_depth fs) in *.
    (* one token consumed, frames [fs'] with [arg_depth fs' = d'] *)
    assert (G1 : forall fs' so' p', arg_depth fs' = arg_depth fs ->
               wfa C (arg_depth fs) rest = true ->
               run C (mkState fs' so' p') rest <> None).
    { intros fs' so' p' E W. apply IH; try assumption; cbn [s_frames]; rewrite E. exact W. }
    destruct t.
    + (* TChar *)
      rewrite run_step. cbn [step s_frames s_out s_pos].
      cbn [wfa] in Hw.
      destruct (in_math fs); apply G1; try rewrite arg_depth_fresh; auto.
    + (* TSpace *)
      rewrite run_step. cbn [step s_frames s_out s_pos]. cbn [wfa] in Hw. apply G1; auto.
    + (* TPar *)
      destruct (negb (Nat.eqb (short_depth fs) 0)) eqn:Hs.
      * rewrite (run_halt C _ _ _ fs E6 p) by (cbn [step s_frames s_out s_pos]; rewrite Hs; reflexivity).
        apply (halt_total C). exact Hw.
      * destruct (in_math fs) eqn:Hm.
        -- rewrite (run_halt C _ _ _ fs E6 p)
             by (cbn [step s_frames s_out s_pos]; rewrite Hs, Hm; reflexivity).
           apply (halt_total C). exact Hw.
        -- rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite Hs, Hm.
           cbn [wfa] in Hw. apply G1; auto.
    + (* TOpen *)
      rewrite run_step. cbn [step s_frames s_out s_pos]. cbn [wfa] in Hw.
      destruct (in_math fs).
      * apply IH; try assumption. cbn [s_frames].
        rewrite arg_depth_push by reflexivity. rewrite arg_depth_fresh. exact Hw.
      * apply IH; try assumption. cbn [s_frames].
        rewrite arg_depth_push by reflexivity. exact Hw.
    + (* TClose *)
      cbn [wfa] in Hw.
      destruct fs as [|f fs'].
      * rewrite run_step. cbn [step s_frames s_out s_pos]. discriminate.
      * destruct f as [|dd sp sb|g sp sb|l pl ga sp sb].
        -- rewrite run_step. cbn [step s_frames s_out s_pos].
           apply IH; try assumption. cbn [s_frames].
           rewrite (arg_depth_pop FSimple fs' eq_refl). exact Hw.
        -- rewrite (run_halt C _ _ _ (FShift dd sp sb :: fs') E5 p) by reflexivity.
           apply (halt_total C). cbn [wfa]. exact Hw.
        -- rewrite run_step. cbn [step s_frames s_out s_pos].
           apply IH; try assumption. cbn [s_frames].
           rewrite (arg_depth_pop (FMGroup g sp sb) fs' eq_refl). exact Hw.
        -- rewrite run_step. cbn [step s_frames s_out s_pos].
           apply IH; try assumption. cbn [s_frames].
           rewrite (arg_depth_pop (FArg l pl ga sp sb) fs' eq_refl). exact Hw.
    + (* TDollar *)
      assert (Hw' : wfa C d rest = true) by (cbn [wfa] in Hw; exact Hw).
      destruct fs as [|f fs'] eqn:Efs.
      * rewrite run_step. cbn [step s_frames s_out s_pos mgroup_head restricted].
        destruct rest as [|t2 rest2]; [simpl; discriminate|].
        destruct t2; cbn [hd_error];
          try (apply IH; try assumption; cbn [s_frames]; rewrite arg_depth_shift; exact Hw').
        apply IH; [simpl in Hl1; lia|inversion Hrest; assumption| |].
        { simpl in Hsc1. exact Hsc1. }
        cbn [s_frames]. rewrite arg_depth_shift. cbn [wfa] in Hw'. exact Hw'.
      * subst d.
        destruct f as [|dd sp sb|g sp sb|l pl ga sp sb].
        -- (* FSimple *)
           rewrite run_step. cbn [step s_frames s_out s_pos mgroup_head].
           destruct (restricted (FSimple :: fs')).
           ++ apply IH; try assumption; cbn [s_frames]; rewrite arg_depth_shift; exact Hw'.
           ++ destruct rest as [|t2 rest2]; [simpl; discriminate|].
              destruct t2; cbn [hd_error];
                try (apply IH; try assumption; cbn [s_frames]; rewrite arg_depth_shift; exact Hw').
              apply IH; [simpl in Hl1; lia|inversion Hrest; assumption| |].
              { simpl in Hsc1. exact Hsc1. }
              cbn [s_frames]. rewrite arg_depth_shift. cbn [wfa] in Hw'. exact Hw'.
        -- destruct dd.
           ++ (* display *)
              destruct rest as [|t2 rest2].
              ** rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E5 p) by reflexivity.
                 apply (halt_total C). exact Hw.
              ** destruct t2 eqn:Et2.
                 all: try (rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E5 p) by reflexivity;
                           apply (halt_total C); exact Hw).
                 --- (* $$ *)
                     rewrite run_step. cbn [step s_frames s_out s_pos hd_error].
                     apply IH; [simpl in Hl1; lia|inversion Hrest; assumption|simpl in Hsc1; exact Hsc1|].
                     cbn [s_frames]. rewrite <- (arg_depth_shift true sp sb fs').
                     cbn [wfa] in Hw'. exact Hw'.
                 --- (* control word *)
                     inversion Hrest as [|? ? Ht2 _]; subst. simpl in Ht2.
                     apply andb_true_iff in Ht2 as [_ Ht2].
                     destruct (c_defined C n) eqn:Hd.
                     +++ destruct (is_some (c_sig C n) || is_some (c_arg C n)) eqn:Hs.
                         *** rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E5 p)
                               by (cbn [step s_frames s_out s_pos hd_error]; rewrite Hd, Hs; reflexivity).
                             apply (halt_total C). exact Hw.
                         *** simpl in Ht2. rewrite Hs in Ht2. discriminate.
                     +++ rewrite (run_halt C _ _ _ (FShift true sp sb :: fs') E1 (S p))
                           by (cbn [step s_frames s_out s_pos hd_error]; rewrite Hd; reflexivity).
                         apply (halt_total C). exact Hw.
           ++ (* inline *)
              rewrite run_step. cbn [step s_frames s_out s_pos].
              apply IH; try assumption. cbn [s_frames].
              rewrite <- (arg_depth_shift false sp sb fs'). exact Hw'.
        -- rewrite (run_halt C _ _ _ (FMGroup g sp sb :: fs') E5 p) by reflexivity.
           apply (halt_total C). exact Hw.
        -- destruct pl as [b|].
           ++ rewrite run_step. cbn [step s_frames s_out s_pos mgroup_head restricted].
              destruct b.
              ** apply IH; try assumption; cbn [s_frames]; rewrite arg_depth_shift; exact Hw'.
              ** destruct rest as [|t2 rest2]; [simpl; discriminate|].
                 destruct t2; cbn [hd_error];
                   try (apply IH; try assumption; cbn [s_frames]; rewrite arg_depth_shift; exact Hw').
                 apply IH; [simpl in Hl1; lia|inversion Hrest; assumption| |].
                 { simpl in Hsc1. exact Hsc1. }
                 cbn [s_frames]. rewrite arg_depth_shift. cbn [wfa] in Hw'. exact Hw'.
           ++ rewrite (run_halt C _ _ _ (FArg l PMath ga sp sb :: fs') E5 p) by reflexivity.
              apply (halt_total C). exact Hw.
    + (* TMOpenInline *)
      destruct (in_math fs) eqn:Hm.
      * rewrite (run_halt C _ _ _ fs E5 p) by (cbn [step s_frames s_out s_pos]; rewrite Hm; reflexivity).
        apply (halt_total C). exact Hw.
      * rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite Hm.
        apply IH; try assumption; cbn [s_frames]; rewrite arg_depth_shift; cbn [wfa] in Hw. exact Hw.
    + (* TMCloseInline *)
      destruct fs as [|[|[] sp sb|g sp sb|l pl ga sp sb] fs'];
        try (rewrite (run_halt C _ _ _ _ E5 p) by reflexivity; apply (halt_total C); exact Hw).
      rewrite run_step. cbn [step s_frames s_out s_pos].
      apply IH; try assumption. cbn [s_frames].
      rewrite <- (arg_depth_shift false sp sb fs'). cbn [wfa] in Hw. exact Hw.
    + (* TMOpenDisplay *)
      destruct (in_math fs) eqn:Hm.
      * rewrite (run_halt C _ _ _ fs E5 p) by (cbn [step s_frames s_out s_pos]; rewrite Hm; reflexivity).
        apply (halt_total C). exact Hw.
      * rewrite run_step. cbn [step s_frames s_out s_pos]. rewrite Hm. cbn [wfa] in Hw.
        destruct (restricted fs).
        -- apply IH; try assumption.
        -- apply IH; try assumption; cbn [s_frames]; rewrite arg_depth_shift; exact Hw.
    + (* TMCloseDisplay *)
      destruct fs as [|[|[] sp sb|g sp sb|l pl ga sp sb] fs'];
        try (rewrite (run_halt C _ _ _ _ E5 p) by reflexivity; apply (halt_total C); exact Hw).
      rewrite run_step. cbn [step s_frames s_out s_pos].
      apply IH; try assumption. cbn [s_frames].
      rewrite <- (arg_depth_shift true sp sb fs'). cbn [wfa] in Hw. exact Hw.
    + (* TScript *)
      destruct (in_math fs) eqn:Hm.
      * destruct (tail_has up fs) eqn:Htl.
        -- rewrite (run_halt C _ _ _ fs E4 p)
             by (cbn [step s_frames s_out s_pos]; rewrite Hm, Htl; reflexivity).
           apply (halt_total C). exact Hw.
        -- rewrite run_step. cbn [step s_frames s_out s_pos negb]. rewrite Hm, Htl. cbn [negb].
           destruct rest as [|t2 rest2]; [simpl in Hsc; discriminate|].
           simpl in Hsc. inversion Hrest; subst.
           cbn [wfa] in Hw.
           destruct t2; try discriminate; cbn [hd_error].
           ++ apply IH; [simpl in Hl1; lia|assumption|exact Hsc|].
              cbn [s_frames]. rewrite arg_depth_mark. cbn [wfa] in Hw. exact Hw.
           ++ apply IH; [simpl in Hl1; lia|assumption|exact Hsc|].
              cbn [s_frames]. rewrite arg_depth_push by reflexivity. rewrite arg_depth_mark.
              cbn [wfa] in Hw. exact Hw.
      * rewrite (run_halt C _ _ _ fs E3 p) by (cbn [step s_frames s_out s_pos]; rewrite Hm; reflexivity).
        apply (halt_total C). exact Hw.
    + (* TCs *)
      simpl in Ht. apply andb_true_iff in Ht as [_ Ht].
      destruct (c_defined C n) eqn:Hd.
      * destruct (c_sig C n) as [sg|] eqn:Hs.
        -- assert (Hw' : wfa C d rest = true).
           { cbn [wfa] in Hw. unfold is_argcmd in Hw. rewrite Hd, Hs in Hw. exact Hw. }
           destruct (in_math fs) eqn:Hm.
           ++ destruct (sig_math sg) as [| |r] eqn:Hsm.
              ** rewrite run_step. cbn [step s_frames s_out s_pos negb]. rewrite Hd, Hs, Hm, Hsm.
                 cbn [negb]. apply G1; [apply arg_depth_fresh|exact Hw'].
              ** rewrite run_step. cbn [step s_frames s_out s_pos negb]. rewrite Hd, Hs, Hm, Hsm.
                 cbn [negb]. apply G1; auto.
              ** rewrite (run_halt C _ _ _ fs r p)
                   by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Hm, Hsm; reflexivity).
                 apply (halt_total C). exact Hw.
           ++ destruct (sig_text sg) as [| |r] eqn:Hst.
              ** rewrite run_step. cbn [step s_frames s_out s_pos negb]. rewrite Hd, Hs, Hm, Hst.
                 cbn [negb]. apply G1; auto.
              ** rewrite run_step. cbn [step s_frames s_out s_pos negb]. rewrite Hd, Hs, Hm, Hst.
                 cbn [negb]. apply G1; auto.
              ** rewrite (run_halt C _ _ _ fs r p)
                   by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Hm, Hst; reflexivity).
                 apply (halt_total C). exact Hw.
        -- destruct (c_arg C n) as [a|] eqn:Ha.
           ++ assert (Harg : is_argcmd C n = true) by (unfold is_argcmd; rewrite Hd, Hs, Ha; reflexivity).
              assert (Hw2 := Hw). cbn [wfa] in Hw2. rewrite Harg in Hw2.
              destruct (in_math fs) eqn:Hm.
              ** destruct (as_math a) as [r|r|pl ga] eqn:Ham.
                 --- rewrite (run_halt C _ _ _ fs r p)
                       by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Ha, Hm, Ham; reflexivity).
                     apply (halt_total C). exact Hw.
                 --- rewrite run_step. cbn [step s_frames s_out s_pos negb].
                     rewrite Hd, Hs, Ha, Hm, Ham. cbn [negb].
                     destruct rest as [|[] r']; try discriminate. cbn [hd_error].
                     apply (scan_total_n C (length r')); [apply le_n| |].
                     { cbn [start_scan sc_k]. rewrite arg_depth_push_arg. lia. }
                     cbn [start_scan sc_k]. rewrite arg_depth_push_arg. exact Hw2.
                 --- rewrite run_step. cbn [step s_frames s_out s_pos negb].
                     rewrite Hd, Hs, Ha, Hm, Ham. cbn [negb].
                     destruct rest as [|[] r']; try discriminate. cbn [hd_error].
                     inversion Hrest as [|? ? _ Hr']; subst.
                     apply IH; [simpl in Hl1; lia|exact Hr'|simpl in Hsc1; exact Hsc1|].
                     cbn [s_frames]. rewrite arg_depth_push_arg, arg_depth_fresh. exact Hw2.
              ** destruct (as_text a) as [r|r|m pl ga] eqn:Hat.
                 --- rewrite (run_halt C _ _ _ fs r p)
                       by (cbn [step s_frames s_out s_pos]; rewrite Hd, Hs, Ha, Hm, Hat; reflexivity).
                     apply (halt_total C). exact Hw.
                 --- rewrite run_step. cbn [step s_frames s_out s_pos negb].
                     rewrite Hd, Hs, Ha, Hm, Hat. cbn [negb].
                     destruct rest as [|[] r']; try discriminate. cbn [hd_error].
                     apply (scan_total_n C (length r')); [apply le_n| |].
                     { cbn [start_scan sc_k]. rewrite arg_depth_push_arg. lia. }
                     cbn [start_scan sc_k]. rewrite arg_depth_push_arg. exact Hw2.
                 --- rewrite run_step. cbn [step s_frames s_out s_pos negb].
                     rewrite Hd, Hs, Ha, Hm, Hat. cbn [negb].
                     destruct rest as [|[] r']; try discriminate. cbn [hd_error].
                     inversion Hrest as [|? ? _ Hr']; subst.
                     apply IH; [simpl in Hl1; lia|exact Hr'|simpl in Hsc1; exact Hsc1|].
                     cbn [s_frames]. rewrite arg_depth_push_arg. exact Hw2.
           ++ simpl in Ht; try rewrite Hs in Ht; try rewrite Ha in Ht; simpl in Ht; discriminate.
      * rewrite (run_halt C _ _ _ fs E1 p) by (cbn [step s_frames s_out s_pos]; rewrite Hd; reflexivity).
        apply (halt_total C). exact Hw.
    + (* TEnd *)
      rewrite run_step. cbn [step s_frames s_out s_pos].
      cbn [wfa] in Hw. unfold d in Hw. rewrite arg_depth_zero in Hw.
      destruct (in_arg fs); [discriminate|].
      destruct (in_math fs); [discriminate|]. destruct so; discriminate.
Qed.

Theorem runs_total : forall C d,
  in_strict_doc C d -> exists o, Runs C init (flatten_doc d) o.
Proof.
  intros C d [[Hok [Hsc Hw]] _].
  destruct (run C init (flatten_doc d)) as [o|] eqn:E.
  - exists o. apply run_sound. exact E.
  - exfalso. eapply (run_total_n C _ _ init); [apply le_n|exact Hok|exact Hsc|exact Hw|exact E].
Qed.

Theorem decide_total : forall C d, in_strict_doc C d -> decide C d <> NotStrict.
Proof.
  intros C d Hs. pose proof Hs as Hs'. apply in_strict_b_spec in Hs'.
  destruct Hs as [[Hok [Hsc Hw]] _].
  unfold decide. rewrite Hs'.
  destruct (run C init (flatten_doc d)) as [[|r l]|] eqn:E; simpl; try discriminate.
  intros _. eapply (run_total_n C _ _ init); [apply le_n|exact Hok|exact Hsc|exact Hw|exact E].
Qed.
