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
      [math_group]): after [^]/[_] ([script = true]) or as a sub-formula.
    Every math frame carries the scripts of its list's TAIL noad
    ([sp]: has a superscript, [sb]: has a subscript); [false, false] also
    stands for "no noad yet", where TeX inserts an empty noad for [^]/[_]
    (tex.web §1176) — the double-script rule only ever asks whether the
    tail already has the script.  The mode is math iff the innermost frame
    is a math frame; inside a math brace group TeX is in non-display math
    ([-mmode]) even within a display, which is why [FMGroup] needs no
    display flag.  [s_out] records whether anything has been typeset (E0),
    [s_pos] is the index of the next token (the location of a fatal). *)

From Coq Require Import List Bool.
Import ListNotations.
From LaTeXPerfectionist.Strict Require Import Syntax Contract.

Inductive frame :=
| FSimple
| FShift (display : bool) (sp sb : bool)
| FMGroup (script : bool) (sp sb : bool).

Record state := mkState { s_frames : list frame; s_out : bool; s_pos : nat }.

Definition init : state := mkState [] false 0.

Inductive outcome :=
| Compiles
| Fatal (r : reason) (l : nat).  (* [l]: index of the token in the stream *)

Definition in_math (fs : list frame) : bool :=
  match fs with
  | FShift _ _ _ :: _ | FMGroup _ _ _ :: _ => true
  | _ => false
  end.

(** Does the tail noad of the innermost math list already have the script? *)
Definition tail_has (up : bool) (fs : list frame) : bool :=
  match fs with
  | FShift _ sp sb :: _ | FMGroup _ sp sb :: _ => if up then sp else sb
  | _ => false
  end.

(** A new noad becomes the tail: no scripts yet. *)
Definition fresh_tail (fs : list frame) : list frame :=
  match fs with
  | FShift d _ _ :: r => FShift d false false :: r
  | FMGroup g _ _ :: r => FMGroup g false false :: r
  | r => r
  end.

(** The tail noad receives a superscript ([up]) or a subscript. *)
Definition mark_script (up : bool) (fs : list frame) : list frame :=
  match fs with
  | FShift d sp sb :: r =>
      FShift d (if up then true else sp) (if up then sb else true) :: r
  | FMGroup g sp sb :: r =>
      FMGroup g (if up then true else sp) (if up then sb else true) :: r
  | r => r
  end.

(** The first token of a stream is not [$]. *)
Definition not_dollar_head (ts : list tok) : Prop :=
  match ts with TDollar :: _ => False | _ => True end.

(** After a [$] in display math, TeX expands the next token looking for the
    second [$] (tex.web §1197, [get_x_token]).  A space, a character, a
    brace, a paragraph break, [\end] or an attested control word is not
    one; an undefined control word raises its own error first
    ([R_dollar_display_undef]). *)
Definition display_bad_follower (C : contract) (t : tok) : Prop :=
  match t with
  | TDollar => False
  | TCs n => c_defined C n = true /\ c_sig C n <> None
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
   surplus { at EOF is NOT fatal). *)
| R_end_ok : forall fs p rest,
    in_math fs = false ->
    Runs C (mkState fs true p) (TEnd :: rest) Compiles

(* probe S0/R_end_empty: nothing typeset: rc 0, "No pages of output.",
   no PDF (design §B.4 E0). *)
| R_end_empty : forall fs p rest,
    in_math fs = false ->
    Runs C (mkState fs false p) (TEnd :: rest) (Fatal E0 p)

(* probe S0/R_end_math: \end{document} inside math: its paragraph end meets
   math mode: "! Missing $ inserted." on the \end{document} line. *)
| R_end_math : forall fs o p rest,
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
   paragraph, if any; not fatal, inside a brace group too. *)
| R_par_text : forall fs o p e rest out,
    in_math fs = false ->
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState fs o p) (TPar e :: rest) out

(* probe S0/R_par_math: \par in math, including a blank line in display math
   and inside a math brace group: "! Missing $ inserted." (design E6). *)
| R_par_math : forall fs o p e rest,
    in_math fs = true ->
    Runs C (mkState fs o p) (TPar e :: rest) (Fatal E6 p)

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

(* probe S0/R_close_shift: } whose innermost group is the formula itself:
   "! Extra }, or forgotten $." *)
| R_close_shift : forall fs o p d sp sb rest,
    Runs C (mkState (FShift d sp sb :: fs) o p) (TClose :: rest) (Fatal E5 p)

(* probe S0/R_close_top: } with no open group in the body:
   "! Too many }'s." *)
| R_close_top : forall o p rest,
    Runs C (mkState [] o p) (TClose :: rest) (Fatal E5 p)

(* ---- $ ----------------------------------------------------------------- *)

(* probe S0/R_dollar_display_open: $ outside math immediately followed by $
   opens DISPLAY math (tex.web §1138: [init_math] reads the next token
   without expansion).  This is where an empty inline formula written [$$]
   is display math.  Typeset material (a paragraph is started). *)
| R_dollar_display_open : forall fs o p rest out,
    in_math fs = false ->
    Runs C (mkState (FShift true false false :: fs) true (S (S p))) rest out ->
    Runs C (mkState fs o p) (TDollar :: TDollar :: rest) out

(* probe S0/R_dollar_inline_open: $ outside math followed by anything else
   (a space included) opens inline math. *)
| R_dollar_inline_open : forall fs o p rest out,
    in_math fs = false ->
    not_dollar_head rest ->
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
| R_dollar_display_undef : forall fs o p sp sb n rest,
    c_defined C n = false ->
    Runs C (mkState (FShift true sp sb :: fs) o p) (TDollar :: TCs n :: rest)
      (Fatal E1 (S p))

(* probe S0/R_dollar_display_bad: $ in display math followed by anything
   but $: "! Display math should end with $$." at the $. *)
| R_dollar_display_bad : forall fs o p sp sb t rest,
    display_bad_follower C t ->
    Runs C (mkState (FShift true sp sb :: fs) o p) (TDollar :: t :: rest) (Fatal E5 p)

(* probe S0/R_dollar_display_eof: $ in display math as the last byte of a
   file without \end{document}.  pdfTeX appends an end-of-line to the last
   line of a file too, so the look-ahead meets a SPACE, not the end of the
   file: "! Display math should end with $$." at the $ (correction C-83: the
   first version said "Emergency stop" at the end of the file; the
   token-level rule probe measured otherwise on its first run). *)
| R_dollar_display_eof : forall fs o p sp sb,
    Runs C (mkState (FShift true sp sb :: fs) o p) [TDollar] (Fatal E5 p)

(* probe S0/R_dollar_group: $ inside a math brace group (tex.web §1193,
   [off_save]): "! Missing } inserted." *)
| R_dollar_group : forall fs o p g sp sb rest,
    Runs C (mkState (FMGroup g sp sb :: fs) o p) (TDollar :: rest) (Fatal E5 p)

(* ---- \( \) \[ \] (LaTeX kernel macros around $ and $$) ------------------ *)

(* probe S0/R_mopen_inline: \( outside math: inline math (the $ in its
   expansion is followed by \fi, never by a second $). *)
| R_mopen_inline : forall fs o p rest out,
    in_math fs = false ->
    Runs C (mkState (FShift false false false :: fs) true (S p)) rest out ->
    Runs C (mkState fs o p) (TMOpenInline :: rest) out

(* probe S0/R_mopen_inline_bad: \( in math:
   "! LaTeX Error: Bad math environment delimiter." *)
| R_mopen_inline_bad : forall fs o p rest,
    in_math fs = true ->
    Runs C (mkState fs o p) (TMOpenInline :: rest) (Fatal E5 p)

(* probe S0/R_mclose_inline: \) in inline math closes it. *)
| R_mclose_inline : forall fs o p sp sb rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FShift false sp sb :: fs) o p) (TMCloseInline :: rest) out

(* probe S0/R_mclose_inline_bad: \) anywhere else: outside math and in
   display math "! LaTeX Error: Bad math environment delimiter.", inside a
   math brace group (where \ifinner holds and its $ meets the brace group)
   "! Missing } inserted.". *)
| R_mclose_inline_bad : forall fs o p rest,
    not_inline_shift fs ->
    Runs C (mkState fs o p) (TMCloseInline :: rest) (Fatal E5 p)

(* probe S0/R_mopen_display: \[ outside math: display math; in vertical mode
   it first typesets an empty box, so it is material either way. *)
| R_mopen_display : forall fs o p rest out,
    in_math fs = false ->
    Runs C (mkState (FShift true false false :: fs) true (S p)) rest out ->
    Runs C (mkState fs o p) (TMOpenDisplay :: rest) out

(* probe S0/R_mopen_display_bad: \[ in math: "Bad math environment
   delimiter". *)
| R_mopen_display_bad : forall fs o p rest,
    in_math fs = true ->
    Runs C (mkState fs o p) (TMOpenDisplay :: rest) (Fatal E5 p)

(* probe S0/R_mclose_display: \] in display math closes it. *)
| R_mclose_display : forall fs o p sp sb rest out,
    Runs C (mkState fs o (S p)) rest out ->
    Runs C (mkState (FShift true sp sb :: fs) o p) (TMCloseDisplay :: rest) out

(* probe S0/R_mclose_display_bad: \] anywhere else, a math brace group
   inside a display included: "Bad math environment delimiter". *)
| R_mclose_display_bad : forall fs o p rest,
    not_display_shift fs ->
    Runs C (mkState fs o p) (TMCloseDisplay :: rest) (Fatal E5 p)

(* ---- ^ and _ ----------------------------------------------------------- *)

(* probe S0/R_script_text: ^ or _ outside math: "! Missing $ inserted." *)
| R_script_text : forall fs o p up rest,
    in_math fs = false ->
    Runs C (mkState fs o p) (TScript up :: rest) (Fatal E3 p)

(* probe S0/R_script_double: the tail noad already has that script:
   "! Double superscript." / "! Double subscript." (tex.web §1177). *)
| R_script_double : forall fs o p up rest,
    in_math fs = true ->
    tail_has up fs = true ->
    Runs C (mkState fs o p) (TScript up :: rest) (Fatal E4 p)

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
| R_cs_undefined : forall fs o p n rest,
    c_defined C n = false ->
    Runs C (mkState fs o p) (TCs n :: rest) (Fatal E1 p)

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
| R_cs_text_fatal : forall fs o p n sg r rest,
    c_defined C n = true -> c_sig C n = Some sg -> sig_text sg = TxFatal r ->
    in_math fs = false ->
    Runs C (mkState fs o p) (TCs n :: rest) (Fatal r p)

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
| R_cs_math_fatal : forall fs o p n sg r rest,
    c_defined C n = true -> c_sig C n = Some sg -> sig_math sg = MxFatal r ->
    in_math fs = true ->
    Runs C (mkState fs o p) (TCs n :: rest) (Fatal r p).
