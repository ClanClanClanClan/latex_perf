(** * Strict.Syntax — the node grammar of the strict fragment L_S0.

    ADR-012, milestone M2 phase 1 (docs/v27/STRICT_TIER_DESIGN.md §A.2, §F).
    The fragment is the one the design names for M2 on configuration [article]
    with no packages: text, spaces, paragraph breaks, brace groups (and a stray
    close brace), the four math delimiters ([$], [$$], [\(]..[\)], [\[]..[\]]),
    super- and subscripts, and control words whose status (undefined, or a
    probe-attested signature) is read from a CONTRACT (Contract.v).  No control
    word name is written in this file or in any file of the kernel: every name
    reaches the kernel through the contract, which is generated data.

    Three layers, as in the design:
    - [node] / [doc]: the grammar a document is parsed into.  Phase 1 has no
      parser from bytes; documents are built as trees (by the generated
      differential, scripts/tools/strict_differential.py) and printed to bytes
      by [render] below.  A parser [parse C bytes] and [parse_exact] are
      phase 2.
    - [tok]: what pdfTeX's reader turns the bytes into.  [flatten_doc] maps a
      tree to its token stream.  The semantics (Semantics.v) and the decider
      (Decide.v) both work on the token stream, because that is what TeX
      executes: the tree nesting is NOT the TeX nesting.  Two examples the
      semantics must (and does) get right:
        - [NMath MkDollar []] prints as [$$]; TeX reads that as the OPENING of
          display math, not as an empty formula (the byte-level lesson of the
          semantics-first spike, design §A.2).  At the token level this is
          [TDollar; TDollar], and the semantics looks ahead exactly as TeX's
          [init_math] does.
        - [NGroup [NStrayClose]] prints as [{}}]: the first [}] closes the
          group and the second is the stray one.
    - [render]: the exact bytes given to pdflatex.  The bridge theorem
      (Bridge.v) is stated about [render d], so the differential grades
      exactly these bytes; they are produced by the EXTRACTED function.

    Rendering rule (why each byte is there).  Every token except [TSpace] and
    [TDollar] is followed by a line feed.  This puts nearly every token on its
    own line, so the line number pdfTeX reports ([l.N]) locates the token that
    raised an error; the differential checks it.  The line feed is harmless
    for the fragment's semantics:
    - after a control word the reader is in state S and a line end produces no
      token; elsewhere it produces one space token, and a space token is a
      no-op in every mode of this fragment (Semantics.v: [R_space]), and is
      skipped by the math scanner after [^]/[_];
    - it is never emitted after [TDollar] (a line end between two [$] would
      turn display math into two inline formulas) and never after [TSpace] (a
      line holding only spaces is a blank line, i.e. a paragraph break).
    A paragraph break [TPar false] prints as two line feeds, which always
    yields at least one blank line (two, after a token that ended its line:
    two [\par] tokens, and a second [\par] outside math is a no-op too). *)

From Coq Require Import List Ascii String Bool.
Import ListNotations.

(** Control-word names, as byte strings.  Phase 1 admits control WORDS only
    (ASCII letters; [in_strict_doc] checks it), whose reading does not depend
    on anything the fragment can change (no catcode changes exist in L_S0). *)
Definition name := list ascii.

Inductive math_kind :=
| MkDollar          (* $ ... $   *)
| MkDisplayDollar   (* $$ ... $$ *)
| MkParen           (* \( ... \) *)
| MkBracket.        (* \[ ... \] *)

Inductive node :=
| NText (w : list ascii)          (* characters of [safe_char] (Decide.v) *)
| NSpace
| NPar (explicit : bool)          (* [false]: a blank line; [true]: [\par] *)
| NGroup (b : list node)          (* { b } *)
| NStrayClose                     (* }     *)
| NMath (k : math_kind) (b : list node)
| NScript (up : bool) (arg : node)  (* ^arg ([up]) or _arg *)
| NCmd (cs : name).               (* \cs — phase 1: no arguments *)

(** A document of configuration [article]:
    [\documentclass{article}] [\begin{document}] body, then
    [\end{document}] iff [d_has_end].  Anything after [\end{document}] is
    never read by TeX, so the fragment has no trailing material. *)
Record doc := mkDoc { d_body : list node; d_has_end : bool }.

(** The tokens pdfTeX's reader produces from the rendered bytes. *)
Inductive tok :=
| TChar (c : ascii)
| TSpace
| TPar (explicit : bool)
| TOpen
| TClose
| TDollar
| TMOpenInline      (* \( *)
| TMCloseInline     (* \) *)
| TMOpenDisplay     (* \[ *)
| TMCloseDisplay    (* \] *)
| TScript (up : bool)
| TCs (n : name)
| TEnd.             (* \end{document} *)

Fixpoint flatten_node (n : node) : list tok :=
  match n with
  | NText w => map TChar w
  | NSpace => [TSpace]
  | NPar e => [TPar e]
  | NGroup b => TOpen :: flat_map flatten_node b ++ [TClose]
  | NStrayClose => [TClose]
  | NMath MkDollar b => TDollar :: flat_map flatten_node b ++ [TDollar]
  | NMath MkDisplayDollar b =>
      TDollar :: TDollar :: flat_map flatten_node b ++ [TDollar; TDollar]
  | NMath MkParen b => TMOpenInline :: flat_map flatten_node b ++ [TMCloseInline]
  | NMath MkBracket b => TMOpenDisplay :: flat_map flatten_node b ++ [TMCloseDisplay]
  | NScript up a => TScript up :: flatten_node a
  | NCmd n => [TCs n]
  end.

Definition flatten_nodes (l : list node) : list tok := flat_map flatten_node l.

Definition flatten_doc (d : doc) : list tok :=
  flatten_nodes (d_body d) ++ (if d_has_end d then [TEnd] else []).

(** ** Rendering to bytes *)

Local Open Scope char_scope.

Definition nl : ascii := "010".
Definition bs : ascii := "\".

Definition render_tok (t : tok) : list ascii :=
  match t with
  | TChar c => [c; nl]
  | TSpace => [" "]
  | TPar false => [nl; nl]
  | TPar true => [bs; "p"; "a"; "r"; nl]
  | TOpen => ["{"; nl]
  | TClose => ["}"; nl]
  | TDollar => ["$"]
  | TMOpenInline => [bs; "("; nl]
  | TMCloseInline => [bs; ")"; nl]
  | TMOpenDisplay => [bs; "["; nl]
  | TMCloseDisplay => [bs; "]"; nl]
  | TScript true => ["^"; nl]
  | TScript false => ["_"; nl]
  | TCs n => bs :: n ++ [nl]
  | TEnd => list_ascii_of_string "\end{document}" ++ [nl]
  end.

Local Close Scope char_scope.

Definition header : list ascii :=
  list_ascii_of_string "\documentclass{article}" ++ [nl]
  ++ list_ascii_of_string "\begin{document}" ++ [nl].

Definition render_toks (ts : list tok) : list ascii := flat_map render_tok ts.

(** The bytes pdflatex is run on.  They depend on the document only through
    its token stream, which is what makes the bridge statement (Bridge.v)
    about [render d] a statement about the stream [Runs] reads. *)
Definition render (d : doc) : list ascii := header ++ render_toks (flatten_doc d).

Lemma render_is_of_tokens : forall d1 d2,
  flatten_doc d1 = flatten_doc d2 -> render d1 = render d2.
Proof. intros d1 d2 H. unfold render. rewrite H. reflexivity. Qed.
