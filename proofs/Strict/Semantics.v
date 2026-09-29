(** * Strict.Semantics — the declarative semantics [Runs] of L_S0.

    ADR-012 / STRICT_TIER_DESIGN.md §C, trust layer (1): a human-reviewed
    inductive relation, ONE CONSTRUCTOR PER CONSTRUCT x FAILURE MODE.  It is a
    model of what pdfTeX does with the token stream of a rendered document
    (Syntax.v).  That it IS pdfTeX's behaviour is the named premise
    [Faithful] (Bridge.v), never an axiom; it is attested by the probes named
    in each constructor's comment and by the generated differential.

    Probe families.  Each constructor cites the family [S0/<constructor>] of
    corpora/strict_s0/rule_probes.json, which scripts/tools/strict_differential.py
    ([--rules]) regenerates: directed documents for that constructor, each
    graded by the pinned oracle (scripts/tools/_oracle.py) and compared with
    the model's verdict, reason and line.  The pdfTeX messages quoted below
    are the ones those probes record.

    The state.  [s_frames] is the TeX group stack of the body, innermost
    first (the [document] environment's own group is below it and never
    popped by the body):
    - [FSimple]: a brace group opened in text;
    - [FShift display sp sb]: a math formula ([$], [\(], [$$], [\[]); in TeX
      the math-shift group;
    - [FMGroup script sp sb]: a brace group opened in math (TeX's
      [math_group]): after [^]/[_] ([script = true]) or as a sub-formula;
    - [FArg l p g sp sb] (step 2, slice A): the argument of a one-argument
      command (Contract.v [asig]) while it runs, in a group of mode [p]; [l]
      is the command's [longness], [g] the number of TeX groups the command
      holds open meanwhile (Contract.v [TRun]/[MRun], C-94).
    Each frame is one or more TeX groups; their total is the fragment's
    capacity measure (Decide.v [groups], [bounded]).
    Every math frame carries the scripts of its list's TAIL noad
    ([sp]: has a superscript, [sb]: has a subscript); [false, false] also
    stands for "no noad yet", where TeX inserts an empty noad for [^]/[_]
    (tex.web §1176) — the double-script rule only ever asks whether the
    tail already has the script.  The mode is math iff the innermost frame
    is a math frame; inside a math brace group TeX is in non-display math
    ([-mmode]) even within a display, which is why [FMGroup] needs no
    display flag.  [s_out] records whether anything has been typeset (E0),
    [s_pos] is the index of the next token (the location of a fatal).

    Arguments (slice A).  pdfTeX reads the whole argument of a command
    before it runs any of it.  So an error raised by a token of an argument
    is not reported where that token is, but where the file reader stands:
    on the closing brace of the OUTERMOST argument being run (the argument
    that was read from the file).  The semantics says this with two small
    relations used by every rule that stops pdfTeX:
    - [Stops fs p r l ts out]: outside every argument, the run stops with
      [Fatal r l]; inside one, the error is DEFERRED and the tokens are
      [Scans]ned from the offending one on;
    - [Scans sc p ts out]: TeX's argument scanner, which only counts braces
      until the outermost argument closes ([Fatal r] there), except that a
      paragraph break inside an argument that is not long stops earlier
      (Contract.v [longness]; [sc_sh], [sc_ou] below).
    A token stream in which an argument does not close before
    [\end{document}] or the end of the file is outside the fragment
    (Decide.v [wfa]: pdfTeX would read on past what the fragment models). *)

From Coq Require Import List Bool Arith.
Import ListNotations.
From LaTeXPerfectionist.Strict Require Import Syntax Contract.

Inductive frame :=
| FSimple
| FShift (display : bool) (sp sb : bool)
| FMGroup (script : bool) (sp sb : bool)
| FArg (l : longness) (p : pay) (g : nat) (sp sb : bool).

Record state := mkState { s_frames : list frame; s_out : bool; s_pos : nat }.

Definition init : state := mkState [] false 0.

Inductive outcome :=
| Compiles
| Fatal (r : reason) (l : nat).  (* [l]: index of the token in the stream *)

Definition in_math (fs : list frame) : bool :=
  match fs with
  | FShift _ _ _ :: _ | FMGroup _ _ _ :: _ | FArg _ PMath _ _ _ :: _ => true
  | _ => false
  end.

(** Does the tail noad of the innermost math list already have the script? *)
Definition tail_has (up : bool) (fs : list frame) : bool :=
  match fs with
  | FShift _ sp sb :: _ | FMGroup _ sp sb :: _ | FArg _ PMath _ sp sb :: _ =>
      if up then sp else sb
  | _ => false
  end.

(** A new noad becomes the tail: no scripts yet. *)
Definition fresh_tail (fs : list frame) : list frame :=
  match fs with
  | FShift d _ _ :: r => FShift d false false :: r
  | FMGroup g _ _ :: r => FMGroup g false false :: r
  | FArg l p g _ _ :: r => FArg l p g false false :: r
  | r => r
  end.

(** The tail noad receives a superscript ([up]) or a subscript. *)
Definition mark_script (up : bool) (fs : list frame) : list frame :=
  match fs with
  | FShift d sp sb :: r =>
      FShift d (if up then true else sp) (if up then sb else true) :: r
  | FMGroup g sp sb :: r =>
      FMGroup g (if up then true else sp) (if up then sb else true) :: r
  | FArg l p g sp sb :: r =>
      FArg l p g (if up then true else sp) (if up then sb else true) :: r
  | r => r
  end.

(** The innermost math list is a math GROUP (a brace group in math, or a
    math argument), where a [$] meets the group: "Missing } inserted". *)
Definition mgroup_head (fs : list frame) : bool :=
  match fs with
  | FMGroup _ _ _ :: _ | FArg _ PMath _ _ _ :: _ => true
  | _ => false
  end.

(** Text in restricted horizontal mode: the innermost frame that is not a
    text brace group is a text argument run in an hbox ([PText true]). *)
Fixpoint restricted (fs : list frame) : bool :=
  match fs with
  | FSimple :: r => restricted r
  | FArg _ (PText b) _ _ _ :: _ => b
  | _ => false
  end.

(** ** Arguments: where an error inside one is reported *)

Definition is_arg_frame (f : frame) : bool :=
  match f with FArg _ _ _ _ _ => true | _ => false end.

(** A frame TeX opened with a brace (every frame but a formula). *)
Definition is_brace (f : frame) : bool :=
  match f with FShift _ _ _ => false | _ => true end.

Definition short_frame (f : frame) : bool :=
  match f with FArg LLong _ _ _ _ => false | FArg _ _ _ _ _ => true | _ => false end.

Definition in_arg (fs : list frame) : bool := existsb is_arg_frame fs.

(** The number of braces still to close before the OUTERMOST argument
    closes: the brace frames from the innermost down to the outermost
    argument frame, both included (0 outside every argument). *)
Fixpoint arg_depth (fs : list frame) : nat :=
  match fs with
  | [] => 0
  | f :: r =>
      if in_arg r then (if is_brace f then S (arg_depth r) else arg_depth r)
      else (if is_arg_frame f then 1 else 0)
  end.

(** The depth, counted as [arg_depth] counts, of the OUTERMOST argument frame
    whose argument is not long (0: none). *)
Fixpoint short_depth (fs : list frame) : nat :=
  match fs with
  | [] => 0
  | f :: r =>
      match short_depth r with
      | O => if short_frame f then arg_depth (f :: r) else O
      | d => d
      end
  end.

(** The outermost argument frame is [LShortOuter]: its argument was read from
    the file by a macro that is not long. *)
Fixpoint outer_short (fs : list frame) : bool :=
  match fs with
  | [] => false
  | f :: r =>
      if in_arg r then outer_short r
      else match f with FArg LShortOuter _ _ _ _ => true | _ => false end
  end.

(** The argument scanner's state: the reason of the deferred error, the
    braces still to close ([sc_k], at least 1), the depth of the outermost
    argument that is not long and was open when the error was deferred
    ([sc_sh], 0 once it has closed or when there is none), and whether the
    outermost argument is [LShortOuter] ([sc_ou]). *)
Record scan := mkScan { sc_r : reason; sc_k : nat; sc_sh : nat; sc_ou : bool }.

Definition start_scan (fs : list frame) (r : reason) : scan :=
  mkScan r (arg_depth fs) (short_depth fs) (outer_short fs).

(** After a closing brace the depth is [k]; an argument at depth [sh] deeper
    than that has closed. *)
Definition close_sh (k sh : nat) : nat := if Nat.ltb k sh then 0 else sh.

(** Tokens the scanner passes over. *)
Definition scan_skips (t : tok) : Prop :=
  match t with TOpen | TClose | TPar _ | TEnd => False | _ => True end.

Inductive Scans : scan -> nat -> list tok -> outcome -> Prop :=
(* probe S0/SC_close_last: the closing brace of the outermost argument: the
   deferred error is reported here (the file reader stands on this brace). *)
| SC_close_last : forall r sh ou p rest,
    Scans (mkScan r 1 sh ou) p (TClose :: rest) (Fatal r p)
(* probe S0/SC_close: an inner closing brace. *)
| SC_close : forall r k sh ou p rest out,
    Scans (mkScan r (S k) (close_sh (S k) sh) ou) (S p) rest out ->
    Scans (mkScan r (S (S k)) sh ou) p (TClose :: rest) out
(* probe S0/SC_open *)
| SC_open : forall r k sh ou p rest out,
    Scans (mkScan r (S k) sh ou) (S p) rest out ->
    Scans (mkScan r k sh ou) p (TOpen :: rest) out
(* probe S0/SC_par_outer: a paragraph break in an outermost argument read by
   a macro that is not long: "Paragraph ended before ... was complete" at
   the break (the file reader stands on it), before anything of the argument
   has run. *)
| SC_par_outer : forall r k sh p e rest,
    Scans (mkScan r k sh true) p (TPar e :: rest) (Fatal E6 p)
(* probe S0/SC_par_short: a paragraph break inside an argument that is not
   long and was open when the error was deferred: that argument's command
   reads it before running it, so its "Paragraph ended" comes first. *)
| SC_par_short : forall r k sh p e rest out,
    sh <> 0 ->
    Scans (mkScan E6 k sh false) (S p) rest out ->
    Scans (mkScan r k sh false) p (TPar e :: rest) out
(* probe S0/SC_par_long: any other paragraph break is only scanned. *)
| SC_par_long : forall r k p e rest out,
    Scans (mkScan r k 0 false) (S p) rest out ->
    Scans (mkScan r k 0 false) p (TPar e :: rest) out
(* probe S0/SC_skip: any other token is only scanned. *)
| SC_skip : forall sc p t rest out,
    scan_skips t ->
    Scans sc (S p) rest out ->
    Scans sc p (t :: rest) out.

(** A token raises the error [r] at location [l]: outside every argument
    the run stops there; inside one the error is deferred and the argument
    scanned from that token on. *)
Inductive Stops : list frame -> nat -> reason -> nat -> list tok -> outcome -> Prop :=
(* probe S0/Stop_now: every fatal probe outside an argument. *)
| Stop_now : forall fs p r l ts,
    in_arg fs = false ->
    Stops fs p r l ts (Fatal r l)
(* probe S0/Stop_defer: every fatal event inside an argument. *)
| Stop_defer : forall fs p r l ts out,
    in_arg fs = true ->
    Scans (start_scan fs r) p ts out ->
    Stops fs p r l ts out.

(** The first token of a stream is not [$]. *)
Definition not_dollar_head (ts : list tok) : Prop :=
  match ts with TDollar :: _ => False | _ => True end.

(** After a [$] in display math, TeX EXPANDS the next token looking for the
    second [$] (tex.web §1197, [get_x_token]).  A space, a character, a
    brace, a paragraph break or [\end] is not one; an undefined control word
    raises its own error first ([R_dollar_display_undef]).

    A defined control word is a bad follower here ONLY because the contract
    admits no name that expansion can see through.  Being attested is not
    enough (correction C-85): a macro that expands to nothing ([\empty],
    [\iftrue], [\theenumiii]) is transparent to [get_x_token], so TeX reads
    the token AFTER it, and [$$z $\empty $$] closes the display.  The
    semantics has no rule for a transparent name; instead the signature
    generator probes every candidate in this position (families D-FOLLOW-*
    of gen_strict_signatures.py) and rejects the ones that are not bad
    followers, and check_strict_kernel.py fails on an admitted name without
    that evidence.  The premise below is therefore a claim about the
    contract's names, attested per name, not about every defined name. *)
Definition display_bad_follower (C : contract) (t : tok) : Prop :=
  match t with
  | TDollar => False
  | TCs n => c_defined C n = true /\ (c_sig C n <> None \/ c_arg C n <> None)
  | _ => True
  end.

Definition not_inline_shift (fs : list frame) : Prop :=
  match fs with FShift false _ _ :: _ => False | _ => True end.

Definition not_display_shift (fs : list frame) : Prop :=
  match fs with FShift true _ _ :: _ => False | _ => True end.

Inductive Runs (C : contract) : state -> list tok -> outcome -> Prop :=

(* ---- end of the stream ------------------------------------------------ *)

(* probe S0/R_eof: no \end{document}; TeX reads past the end of the file:
   "*** (job aborted, no legal \end found)", "! Emergency stop.", rc 1. *)
| R_eof : forall fs o p,
    Runs C (mkState fs o p) [] (Fatal E5 p)

(* probe S0/R_end_ok: \end{document} outside math after typeset material:
   rc 0 and a PDF.  Open brace groups are only a warning (design §C.2: a
   surplus { at EOF is NOT fatal).  Never inside an argument (Decide.v
   [wfa]: pdfTeX would read it as part of the argument). *)
| R_end_ok : forall fs p rest,
    in_arg fs = false ->
    in_math fs = false ->
    Runs C (mkState fs true p) (TEnd :: rest) Compiles

(* probe S0/R_end_empty: nothing typeset: rc 0, "No pages of output.",
   no PDF (design §B.4 E0). *)
| R_end_empty : forall fs p rest,
    in_arg fs = false ->
    in_math fs = false ->
    Runs C (mkState fs false p) (TEnd :: rest) (Fatal E0 p)

(* probe S0/R_end_math: \end{document} inside math: its paragraph end meets
   math mode: "! Missing $ inserted." on the \end{document} line. *)
| R_end_math : forall fs o p rest,
    in_arg fs = false ->
    in_math fs = true ->
    Runs C (mkState fs o p) (TEnd :: rest) (Fatal E5 p)

(* ---- characters and spaces --------------------------------------------- *)

(* probe S0/R_char_text: a character in text starts or continues a
   paragraph: typeset material. *)
| R_char_text : forall fs o p c rest out,
    in_math fs = false ->
    Runs C (mkState fs true (S p)) rest out ->
    Runs C (mkState fs o p) (TChar c :: rest) out

(* probe S0/R_char_math: a character in math is a new noad (tex.web §1151). *)
| R_char_math : forall fs o p c rest out,
    in_math fs = true ->
    Runs C (mkState (fresh_tail fs) o (S p)) rest out ->
    Runs C (mkState fs o p) (TChar c :: rest) out

(* probe S0/R_space: a space is ignored in vertical mode and in math, and is
   glue in horizontal mode, which already has material: never fatal, never
   the first material, never a noad. *)
| R_space : forall fs o p rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState fs o p) (TSpace :: rest) out

(* ---- paragraph breaks -------------------------------------------------- *)

(* probe S0/R_par_text: \par (or a blank line) outside math ends the
   paragraph, if any; not fatal, inside a brace group too, and inside the
   argument of a command whose argument is long (in restricted horizontal
   mode it does nothing). *)
| R_par_text : forall fs o p e rest out,
    in_math fs = false ->
    short_depth fs = 0 ->
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState fs o p) (TPar e :: rest) out

(* probe S0/R_par_math: \par in math, including a blank line in display math
   and inside a math brace group: "! Missing $ inserted." (design E6). *)
| R_par_math : forall fs o p e rest out,
    in_math fs = true ->
    short_depth fs = 0 ->
    Stops fs p E6 p (TPar e :: rest) out ->
    Runs C (mkState fs o p) (TPar e :: rest) out

(* probe S0/R_par_short: \par (or a blank line) inside the argument of a
   command whose argument is not long: "Paragraph ended before ... was
   complete" (design E6), where [Scans] says. *)
| R_par_short : forall fs o p e rest out,
    short_depth fs <> 0 ->
    Stops fs p E6 p (TPar e :: rest) out ->
    Runs C (mkState fs o p) (TPar e :: rest) out

(* ---- brace groups ------------------------------------------------------ *)

(* probe S0/R_open_text: { in text opens a simple group. *)
| R_open_text : forall fs o p rest out,
    in_math fs = false ->
    Runs C (mkState (FSimple :: fs) o (S p)) rest out ->
    Runs C (mkState fs o p) (TOpen :: rest) out

(* probe S0/R_open_math: { in math appends a new noad whose nucleus is the
   sub-formula (tex.web §1154): when it closes, the tail is that noad, with
   no scripts. *)
| R_open_math : forall fs o p rest out,
    in_math fs = true ->
    Runs C (mkState (FMGroup false false false :: fresh_tail fs) o (S p)) rest out ->
    Runs C (mkState fs o p) (TOpen :: rest) out

(* probe S0/R_close_simple *)
| R_close_simple : forall fs o p rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FSimple :: fs) o p) (TClose :: rest) out

(* probe S0/R_close_group: closing a math brace group; the enclosing list's
   tail is as the group's opening left it. *)
| R_close_group : forall fs o p g sp sb rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FMGroup g sp sb :: fs) o p) (TClose :: rest) out

(* probe S0/R_close_arg: the closing brace of an argument that ran without
   an error: the command is done (in math the enclosing list's tail is as
   the command's opening left it: fresh). *)
| R_close_arg : forall fs o p l pl g sp sb rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FArg l pl g sp sb :: fs) o p) (TClose :: rest) out

(* probe S0/R_close_shift: } whose innermost group is the formula itself:
   "! Extra }, or forgotten $." *)
| R_close_shift : forall fs o p d sp sb rest out,
    Stops (FShift d sp sb :: fs) p E5 p (TClose :: rest) out ->
    Runs C (mkState (FShift d sp sb :: fs) o p) (TClose :: rest) out

(* probe S0/R_close_top: } with no open group in the body:
   "! Too many }'s." *)
| R_close_top : forall o p rest,
    Runs C (mkState [] o p) (TClose :: rest) (Fatal E5 p)

(* ---- $ ----------------------------------------------------------------- *)

(* probe S0/R_dollar_display_open: $ outside math immediately followed by $
   opens DISPLAY math (tex.web §1138: [init_math] reads the next token
   without expansion).  This is where an empty inline formula written [$$]
   is display math.  Typeset material (a paragraph is started).  Not in
   restricted horizontal mode ([R_dollar_restricted_open]). *)
| R_dollar_display_open : forall fs o p rest out,
    in_math fs = false ->
    restricted fs = false ->
    Runs C (mkState (FShift true false false :: fs) true (S (S p))) rest out ->
    Runs C (mkState fs o p) (TDollar :: TDollar :: rest) out

(* probe S0/R_dollar_inline_open: $ outside math followed by anything else
   (a space included) opens inline math. *)
| R_dollar_inline_open : forall fs o p rest out,
    in_math fs = false ->
    restricted fs = false ->
    not_dollar_head rest ->
    Runs C (mkState (FShift false false false :: fs) true (S p)) rest out ->
    Runs C (mkState fs o p) (TDollar :: rest) out

(* probe S0/R_dollar_restricted_open: $ in restricted horizontal mode (a text
   argument run in an hbox) always opens INLINE math, a following $
   included (tex.web §1138: display math only when [mode > 0]): [$$] there
   is an empty formula. *)
| R_dollar_restricted_open : forall fs o p rest out,
    in_math fs = false ->
    restricted fs = true ->
    Runs C (mkState (FShift false false false :: fs) true (S p)) rest out ->
    Runs C (mkState fs o p) (TDollar :: rest) out

(* probe S0/R_dollar_inline_close: $ in inline math closes it, whatever
   follows (no look-ahead: [$x$$y$] is two inline formulas), and whichever
   of $ or \( opened it. *)
| R_dollar_inline_close : forall fs o p sp sb rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FShift false sp sb :: fs) o p) (TDollar :: rest) out

(* probe S0/R_dollar_display_close: $$ in display math closes it, whichever
   of $$ or \[ opened it. *)
| R_dollar_display_close : forall fs o p sp sb rest out,
    Runs C (mkState fs o (S (S p))) rest out ->
    Runs C (mkState (FShift true sp sb :: fs) o p) (TDollar :: TDollar :: rest) out

(* probe S0/R_dollar_display_undef: $ in display math followed by an
   undefined control word: TeX expands the follower and reports
   "! Undefined control sequence." at the follower. *)
| R_dollar_display_undef : forall fs o p sp sb n rest out,
    c_defined C n = false ->
    Stops (FShift true sp sb :: fs) p E1 (S p) (TDollar :: TCs n :: rest) out ->
    Runs C (mkState (FShift true sp sb :: fs) o p) (TDollar :: TCs n :: rest) out

(* probe S0/R_dollar_display_bad: $ in display math followed by anything
   but $ (an admitted control word included, see [display_bad_follower]):
   "! Display math should end with $$." at the $.  The follower is on the
   $'s line ([render] puts no line feed after [TDollar]), which is why the
   line of the $ is the line pdfTeX reports. *)
| R_dollar_display_bad : forall fs o p sp sb t rest out,
    display_bad_follower C t ->
    Stops (FShift true sp sb :: fs) p E5 p (TDollar :: t :: rest) out ->
    Runs C (mkState (FShift true sp sb :: fs) o p) (TDollar :: t :: rest) out

(* probe S0/R_dollar_display_eof: $ in display math as the last byte of a
   file without \end{document}.  pdfTeX appends an end-of-line to the last
   line of a file too, so the look-ahead meets a SPACE, not the end of the
   file: "! Display math should end with $$." at the $ (correction C-83: the
   first version said "Emergency stop" at the end of the file; the
   token-level rule probe measured otherwise on its first run). *)
| R_dollar_display_eof : forall fs o p sp sb out,
    Stops (FShift true sp sb :: fs) p E5 p [TDollar] out ->
    Runs C (mkState (FShift true sp sb :: fs) o p) [TDollar] out

(* probe S0/R_dollar_group: $ inside a math brace group, or in a math
   argument (tex.web §1193, [off_save]): "! Missing } inserted." *)
| R_dollar_group : forall fs o p rest out,
    mgroup_head fs = true ->
    Stops fs p E5 p (TDollar :: rest) out ->
    Runs C (mkState fs o p) (TDollar :: rest) out

(* ---- \( \) \[ \] (LaTeX kernel macros around $ and $$) ------------------ *)

(* probe S0/R_mopen_inline: \( outside math: inline math (the $ in its
   expansion is followed by \fi, never by a second $). *)
| R_mopen_inline : forall fs o p rest out,
    in_math fs = false ->
    Runs C (mkState (FShift false false false :: fs) true (S p)) rest out ->
    Runs C (mkState fs o p) (TMOpenInline :: rest) out

(* probe S0/R_mopen_inline_bad: \( in math:
   "! LaTeX Error: Bad math environment delimiter." *)
| R_mopen_inline_bad : forall fs o p rest out,
    in_math fs = true ->
    Stops fs p E5 p (TMOpenInline :: rest) out ->
    Runs C (mkState fs o p) (TMOpenInline :: rest) out

(* probe S0/R_mclose_inline: \) in inline math closes it. *)
| R_mclose_inline : forall fs o p sp sb rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FShift false sp sb :: fs) o p) (TMCloseInline :: rest) out

(* probe S0/R_mclose_inline_bad: \) anywhere else: outside math and in
   display math "! LaTeX Error: Bad math environment delimiter.", inside a
   math brace group (where \ifinner holds and its $ meets the brace group)
   "! Missing } inserted.". *)
| R_mclose_inline_bad : forall fs o p rest out,
    not_inline_shift fs ->
    Stops fs p E5 p (TMCloseInline :: rest) out ->
    Runs C (mkState fs o p) (TMCloseInline :: rest) out

(* probe S0/R_mopen_display: \[ outside math: display math; in vertical mode
   it first typesets an empty box, so it is material either way.  Not in
   restricted horizontal mode ([R_mopen_display_restricted]). *)
| R_mopen_display : forall fs o p rest out,
    in_math fs = false ->
    restricted fs = false ->
    Runs C (mkState (FShift true false false :: fs) true (S p)) rest out ->
    Runs C (mkState fs o p) (TMOpenDisplay :: rest) out

(* probe S0/R_mopen_display_restricted: \[ in restricted horizontal mode:
   its $$ is an empty inline formula there, so it opens nothing (and a
   later \] meets text: [R_mclose_display_bad]). *)
| R_mopen_display_restricted : forall fs o p rest out,
    in_math fs = false ->
    restricted fs = true ->
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState fs o p) (TMOpenDisplay :: rest) out

(* probe S0/R_mopen_display_bad: \[ in math: "Bad math environment
   delimiter". *)
| R_mopen_display_bad : forall fs o p rest out,
    in_math fs = true ->
    Stops fs p E5 p (TMOpenDisplay :: rest) out ->
    Runs C (mkState fs o p) (TMOpenDisplay :: rest) out

(* probe S0/R_mclose_display: \] in display math closes it. *)
| R_mclose_display : forall fs o p sp sb rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FShift true sp sb :: fs) o p) (TMCloseDisplay :: rest) out

(* probe S0/R_mclose_display_bad: \] anywhere else, a math brace group
   inside a display included: "Bad math environment delimiter". *)
| R_mclose_display_bad : forall fs o p rest out,
    not_display_shift fs ->
    Stops fs p E5 p (TMCloseDisplay :: rest) out ->
    Runs C (mkState fs o p) (TMCloseDisplay :: rest) out

(* ---- ^ and _ ----------------------------------------------------------- *)

(* probe S0/R_script_text: ^ or _ outside math: "! Missing $ inserted." *)
| R_script_text : forall fs o p up rest out,
    in_math fs = false ->
    Stops fs p E3 p (TScript up :: rest) out ->
    Runs C (mkState fs o p) (TScript up :: rest) out

(* probe S0/R_script_double: the tail noad already has that script:
   "! Double superscript." / "! Double subscript." (tex.web §1177). *)
| R_script_double : forall fs o p up rest out,
    in_math fs = true ->
    tail_has up fs = true ->
    Stops fs p E4 p (TScript up :: rest) out ->
    Runs C (mkState fs o p) (TScript up :: rest) out

(* probe S0/R_script_char: ^c / _c: the character is the script; the tail
   noad keeps it (a following ^ of the same kind is a double script). *)
| R_script_char : forall fs o p up c rest out,
    in_math fs = true ->
    tail_has up fs = false ->
    Runs C (mkState (mark_script up fs) o (S (S p))) rest out ->
    Runs C (mkState fs o p) (TScript up :: TChar c :: rest) out

(* probe S0/R_script_group: ^{...} / _{...}: the script is a sub-formula in
   a math brace group with its own, empty, list. *)
| R_script_group : forall fs o p up rest out,
    in_math fs = true ->
    tail_has up fs = false ->
    Runs C (mkState (FMGroup true false false :: mark_script up fs) o (S (S p))) rest out ->
    Runs C (mkState fs o p) (TScript up :: TOpen :: rest) out

(* ---- control words (behaviour read from the contract) ------------------ *)

(* probe S0/R_cs_undefined, and every committed contract's closed world:
   "! Undefined control sequence.", in any mode. *)
| R_cs_undefined : forall fs o p n rest out,
    c_defined C n = false ->
    Stops fs p E1 p (TCs n :: rest) out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* The six constructors below read the signature attested for the name by
   the solo probes of gen_strict_signatures.py (families T-ALONE, T-MID,
   T-GROUP, T-PAR, T-DOLLAR for text; M-ALONE, M-MID, M-GROUP, M-RESET,
   M-DISPLAY for math; the per-name evidence is in the signature file). *)

(* probe S0/R_cs_text_material + signature families T-* *)
| R_cs_text_material : forall fs o p n sg rest out,
    c_defined C n = true -> c_sig C n = Some sg -> sig_text sg = TxMaterial ->
    in_math fs = false ->
    Runs C (mkState fs true (S p)) rest out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* probe S0/R_cs_text_noop + signature families T-* *)
| R_cs_text_noop : forall fs o p n sg rest out,
    c_defined C n = true -> c_sig C n = Some sg -> sig_text sg = TxNoop ->
    in_math fs = false ->
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* probe S0/R_cs_text_fatal + signature families T-* *)
| R_cs_text_fatal : forall fs o p n sg r rest out,
    c_defined C n = true -> c_sig C n = Some sg -> sig_text sg = TxFatal r ->
    in_math fs = false ->
    Stops fs p r p (TCs n :: rest) out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* probe S0/R_cs_math_noad + signature families M-* *)
| R_cs_math_noad : forall fs o p n sg rest out,
    c_defined C n = true -> c_sig C n = Some sg -> sig_math sg = MxNoad ->
    in_math fs = true ->
    Runs C (mkState (fresh_tail fs) o (S p)) rest out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* probe S0/R_cs_math_noop + signature families M-* *)
| R_cs_math_noop : forall fs o p n sg rest out,
    c_defined C n = true -> c_sig C n = Some sg -> sig_math sg = MxNoop ->
    in_math fs = true ->
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* probe S0/R_cs_math_fatal + signature families M-* *)
| R_cs_math_fatal : forall fs o p n sg r rest out,
    c_defined C n = true -> c_sig C n = Some sg -> sig_math sg = MxFatal r ->
    in_math fs = true ->
    Stops fs p r p (TCs n :: rest) out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* ---- one-argument commands (step 2, slice A; Contract.v [asig]) -------- *)

(* The six constructors below read the argument signature attested for the
   name by the solo probes of gen_strict_signatures.py stage A (families
   A-*; the per-name evidence is in the signature file).  The argument is
   the brace group right after the name (Decide.v [wfa]). *)

(* probe S0/R_arg_text_now + signature families A-*: stops before reading
   the argument ("allowed only in math mode", "Missing $ inserted" on the
   line of the name). *)
| R_arg_text_now : forall fs o p n a r rest out,
    c_defined C n = true -> c_sig C n = None -> c_arg C n = Some a ->
    as_text a = TFatalNow r ->
    in_math fs = false ->
    Stops fs p r p (TCs n :: rest) out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* probe S0/R_arg_text_after + signature families A-*: reads the argument,
   then stops (on the line of its closing brace, or earlier by [Scans]).  The
   argument is only scanned, never run: its frame holds no TeX group (the
   [0]; [start_scan] reads only the braces, C-94). *)
| R_arg_text_after : forall fs o p n a r rest out,
    c_defined C n = true -> c_sig C n = None -> c_arg C n = Some a ->
    as_text a = TFatalAfter r ->
    in_math fs = false ->
    Scans (start_scan (FArg (as_long a) (PText false) 0 false false :: fs) r) (S (S p)) rest out ->
    Runs C (mkState fs o p) (TCs n :: TOpen :: rest) out

(* probe S0/R_arg_text_run + signature families A-*: reads the argument and
   runs it in a group of mode [pl]. *)
| R_arg_text_run : forall fs o p n a m pl g rest out,
    c_defined C n = true -> c_sig C n = None -> c_arg C n = Some a ->
    as_text a = TRun m pl g ->
    in_math fs = false ->
    Runs C (mkState (FArg (as_long a) pl g false false :: fs) (o || m) (S (S p))) rest out ->
    Runs C (mkState fs o p) (TCs n :: TOpen :: rest) out

(* probe S0/R_arg_math_now + signature families A-* *)
| R_arg_math_now : forall fs o p n a r rest out,
    c_defined C n = true -> c_sig C n = None -> c_arg C n = Some a ->
    as_math a = MFatalNow r ->
    in_math fs = true ->
    Stops fs p r p (TCs n :: rest) out ->
    Runs C (mkState fs o p) (TCs n :: rest) out

(* probe S0/R_arg_math_after + signature families A-* *)
| R_arg_math_after : forall fs o p n a r rest out,
    c_defined C n = true -> c_sig C n = None -> c_arg C n = Some a ->
    as_math a = MFatalAfter r ->
    in_math fs = true ->
    Scans (start_scan (FArg (as_long a) (PText false) 0 false false :: fs) r) (S (S p)) rest out ->
    Runs C (mkState fs o p) (TCs n :: TOpen :: rest) out

(* probe S0/R_arg_math_run + signature families A-*: the result is a fresh
   tail of the enclosing list. *)
| R_arg_math_run : forall fs o p n a pl g rest out,
    c_defined C n = true -> c_sig C n = None -> c_arg C n = Some a ->
    as_math a = MRun pl g ->
    in_math fs = true ->
    Runs C (mkState (FArg (as_long a) pl g false false :: fresh_tail fs) o (S (S p))) rest out ->
    Runs C (mkState fs o p) (TCs n :: TOpen :: rest) out.
