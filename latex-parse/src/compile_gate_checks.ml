(** Precise structural-fatal compile-gate detectors. See
    [compile_gate_checks.mli].

    Every detector here fires IFF pdflatex genuinely FAILS with no output PDF on
    the targeted deterministic-structural condition. Each boundary below was
    pinned empirically against pdflatex (compiling-vs-failing counter-examples
    are enumerated in [test_compile_gate.ml]). Detectors are pure functions of
    the source bytes, comment/verbatim/context-aware via the [Validators_common]
    range helpers, so they are cheap and identical on the fast and full
    readiness branches. A detected fatal is the DANGEROUS direction to miss
    (false-READY), so each detector is conservative: it fires only when the
    fatal boundary is unambiguous, never on a compiling form. *)

(* A byte offset is "skipped" (comment / verbatim / \verb / url) — no detector
   reads structural meaning out of those bytes. *)
let in_ranges (ranges : (int * int) list) (off : int) : bool =
  List.exists (fun (a, b) -> a <= off && off < b) ranges

(* Commands whose brace argument is a MOVING / NAME argument that pdflatex does
   NOT re-typeset in the current mode: the argument bytes are stored/used as a
   key, not executed, so a `_`/`^`/`&`/`'` inside them is an ordinary character,
   NOT a script/alignment operator. Empirically confirmed:
   `$...\label{a_b_c}...$` and `\Cref{a&b}` both COMPILE. We must exclude these
   argument ranges from the structural detectors or they over-reject on real
   papers (labels like `eq:BSDE_P_W` are ubiquitous inside align/equation
   environments, which [find_math_ranges] otherwise flags as math). *)
let moving_arg_commands =
  [
    "label";
    "ref";
    "eqref";
    "cref";
    "Cref";
    "crefrange";
    "Crefrange";
    "pageref";
    "autoref";
    "nameref";
    "vref";
    "vpageref";
    "hyperref";
    "hypertarget";
    "hyperlink";
    "href";
    "url";
    "nolinkurl";
    "path";
    "cite";
    "citep";
    "citet";
    "citeauthor";
    "citeyear";
    "citealp";
    "citealt";
    "textcite";
    "parencite";
    "autocite";
    "footcite";
    "cites";
    "index";
    "input";
    "include";
    "includeonly";
    "bibliography";
    "InputIfFileExists";
    "includegraphics";
    "graphicspath";
    "verbatiminput";
    "lstinputlisting";
  ]

(* [find_moving_arg_ranges s] — half-open byte ranges of the FIRST brace group
   argument of each occurrence of a [moving_arg_commands] control sequence.
   Matched-brace, escape-aware, and [find_verbatim_comment_url_ranges]-aware so
   we do not treat a `\label` written inside a comment/verbatim as real. Only
   the immediately-following brace group (after optional `[...]` opts and
   whitespace) is captured — enough to cover the label/ref/cite/url key. *)
(* [find_ref_alias_macros s] — names of user-defined macros that are REFERENCE
   ALIASES: a `\newcommand{\Foo}[k]{…}` or `\def\Foo…{…}` whose body invokes a
   reference/label/cite command (`\ref`, `\eqref`, `\pageref`, `\cref`, `\Cref`,
   `\autoref`, `\hyperref`, `\nameref`, `\vref`, `\cite…`, `\label`). Such a
   macro's brace argument is a LABEL KEY, never re-typeset as math — so a
   `_`/`^` inside `\Foo{eq:a_b}` (even inside `$…$`, e.g. `\Eqn{ssnl_v_update}`
   inside a `cases` environment) is an ordinary character, not a script
   operator. We must fold these names into the moving-arg skip or the
   double-script detector over-rejects real compiling papers that use custom
   `\ref` wrappers (very common: `\reff`, `\Eqn`, `\eqreff`, `\myref`…).
   Detection is CONSERVATIVE for soundness: we only add a name whose definition
   body provably contains a reference command, so a genuine math-typesetting
   macro (`\mathrm`, `\text`) is never skipped and true `x^a^b` fatals inside
   those are still caught. *)
let ref_body_commands =
  [
    "\\ref";
    "\\eqref";
    "\\pageref";
    "\\cref";
    "\\Cref";
    "\\autoref";
    "\\nameref";
    "\\vref";
    "\\vpageref";
    "\\hyperref";
    "\\cite";
    "\\citep";
    "\\citet";
    "\\label";
    "\\crefrange";
    "\\Crefrange";
    "\\ref*";
  ]

let find_ref_alias_macros (s : string) : string list =
  let n = String.length s in
  let skip = Validators_common.find_verbatim_comment_url_ranges s in
  let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  let is_escaped idx =
    let rec count b acc =
      if b < 0 then acc
      else if String.unsafe_get s b = '\\' then count (b - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let starts pfx j =
    let pl = String.length pfx in
    j + pl <= n && String.sub s j pl = pfx
  in
  (* read a matched brace group starting at the '{' at [k]; returns
     (inner_start, inner_stop, past_close) or None. *)
  let read_group k =
    if k >= n || String.unsafe_get s k <> '{' then None
    else
      let d = ref 1 and m = ref (k + 1) in
      let start = k + 1 in
      while !m < n && !d > 0 do
        let c = String.unsafe_get s !m in
        if c = '{' && not (is_escaped !m) then incr d
        else if c = '}' && not (is_escaped !m) then decr d;
        incr m
      done;
      if !d = 0 then Some (start, !m - 1, !m) else None
  in
  let body_is_ref body =
    List.exists
      (fun cmd ->
        (* substring search for cmd in body *)
        let cl = String.length cmd and bl = String.length body in
        let rec go i =
          if i + cl > bl then false
          else if String.sub body i cl = cmd then true
          else go (i + 1)
        in
        go 0)
      ref_body_commands
  in
  let names = ref [] in
  let i = ref 0 in
  while !i < n do
    let pos = !i in
    if in_ranges skip pos then incr i
    else if
      (not (is_escaped pos))
      && (starts "\\newcommand" pos
         || starts "\\renewcommand" pos
         || starts "\\providecommand" pos)
    then (
      (* \newcommand{\Foo}[..]{body} or \newcommand\Foo[..]{body} *)
      let j = ref (pos + 1) in
      while !j < n && is_letter (String.unsafe_get s !j) do
        incr j
      done;
      (* skip optional '*' *)
      if !j < n && String.unsafe_get s !j = '*' then incr j;
      (* skip whitespace *)
      while
        !j < n
        &&
        let c = String.unsafe_get s !j in
        c = ' ' || c = '\t' || c = '\n' || c = '\r'
      do
        incr j
      done;
      let name = ref "" in
      if !j < n && String.unsafe_get s !j = '{' then
        (* {\Foo} *)
        match read_group !j with
        | Some (a, b, past) ->
            let inner = String.sub s a (b - a) in
            if String.length inner >= 2 && inner.[0] = '\\' then
              name := String.sub inner 1 (String.length inner - 1);
            j := past
        | None -> ()
      else if !j < n && String.unsafe_get s !j = '\\' then (
        (* \Foo *)
        let k = ref (!j + 1) in
        while !k < n && is_letter (String.unsafe_get s !k) do
          incr k
        done;
        name := String.sub s (!j + 1) (!k - !j - 1);
        j := !k);
      (* skip [..] optional-arg specs and whitespace to reach the body {..} *)
      let cont = ref true in
      while !cont && !j < n do
        let c = String.unsafe_get s !j in
        if c = ' ' || c = '\t' || c = '\n' || c = '\r' then incr j
        else if c = '[' then (
          let d = ref 1 in
          incr j;
          while !j < n && !d > 0 do
            (match String.unsafe_get s !j with
            | '[' -> incr d
            | ']' -> decr d
            | _ -> ());
            incr j
          done)
        else cont := false
      done;
      match read_group !j with
      | Some (a, b, past) ->
          let body = String.sub s a (b - a) in
          if !name <> "" && body_is_ref body then names := !name :: !names;
          i := past
      | None -> i := !j)
    else if (not (is_escaped pos)) && starts "\\def" pos then (
      (* \def\Foo<params>{body} — capture name then find first balanced {..} *)
      let j = ref (pos + String.length "\\def") in
      while
        !j < n
        &&
        let c = String.unsafe_get s !j in
        c = ' ' || c = '\t' || c = '\n' || c = '\r'
      do
        incr j
      done;
      if !j < n && String.unsafe_get s !j = '\\' then (
        let k = ref (!j + 1) in
        while !k < n && is_letter (String.unsafe_get s !k) do
          incr k
        done;
        let nm = String.sub s (!j + 1) (!k - !j - 1) in
        (* scan forward to the first unescaped '{' at brace depth 0 (skipping
           the param text like #1#2) then read the body group *)
        let m = ref !k in
        while
          !m < n && not (String.unsafe_get s !m = '{' && not (is_escaped !m))
        do
          incr m
        done;
        match read_group !m with
        | Some (a, b, past) ->
            let body = String.sub s a (b - a) in
            if nm <> "" && body_is_ref body then names := nm :: names.contents;
            i := past
        | None -> i := !m)
      else incr i)
    else incr i
  done;
  !names

let find_moving_arg_ranges ?(extra = []) (s : string) : (int * int) list =
  let n = String.length s in
  let skip = Validators_common.find_verbatim_comment_url_ranges s in
  let cmd_tbl = Hashtbl.create 64 in
  List.iter (fun c -> Hashtbl.replace cmd_tbl c ()) moving_arg_commands;
  List.iter (fun c -> Hashtbl.replace cmd_tbl c ()) extra;
  let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
  let is_escaped idx =
    let rec count b acc =
      if b < 0 then acc
      else if String.unsafe_get s b = '\\' then count (b - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let ranges = ref [] in
  let i = ref 0 in
  while !i < n do
    let pos = !i in
    if in_ranges skip pos then incr i
    else if String.unsafe_get s pos = '\\' && not (is_escaped pos) then (
      (* read control word *)
      let j = ref (pos + 1) in
      while !j < n && is_letter (String.unsafe_get s !j) do
        incr j
      done;
      let name = String.sub s (pos + 1) (!j - pos - 1) in
      if Hashtbl.mem cmd_tbl name then (
        (* skip optional [..] groups and whitespace, then capture one {..} *)
        let k = ref !j in
        let continue = ref true in
        while !continue && !k < n do
          let c = String.unsafe_get s !k in
          if c = ' ' || c = '\t' || c = '\n' || c = '\r' then incr k
          else if c = '[' then (
            (* skip to matching ] (no nesting expected in opts) *)
            let d = ref 1 in
            incr k;
            while !k < n && !d > 0 do
              (match String.unsafe_get s !k with
              | '[' -> incr d
              | ']' -> decr d
              | _ -> ());
              incr k
            done)
          else continue := false
        done;
        if !k < n && String.unsafe_get s !k = '{' then (
          let d = ref 1 and m = ref (!k + 1) in
          let start = !k + 1 in
          while !m < n && !d > 0 do
            let cm = String.unsafe_get s !m in
            if cm = '{' && not (is_escaped !m) then incr d
            else if cm = '}' && not (is_escaped !m) then decr d;
            incr m
          done;
          (* range excludes the closing brace *)
          let stop = if !d = 0 then !m - 1 else !m in
          ranges := (start, stop) :: !ranges;
          i := !m)
        else i := !k)
      else i := !j)
    else incr i
  done;
  List.rev !ranges

(* ── Detector (1): double super/subscript in math ─────────────────────────
   `x^a^b` / `x_a_b` → "! Double superscript/subscript", FATAL (no PDF).

   Model (pinned against pdflatex, see test cases): within one math atom (base),
   TeX tracks a superscript slot and a subscript slot at the current brace
   depth. - `^` fills the superscript slot; a 2nd `^` on the same base → fatal.
   - `_` fills the subscript slot; a 2nd `_` on the same base → fatal. - `'`
   (prime) IS a superscript. A prime BEFORE any `^` merges with the
   following/other primes (x''^b compiles). A prime AFTER `^` already filled the
   superscript slot → Double superscript, fatal (x^b' fails). - super and sub
   share the SAME base: `x^a_b^c` fails (two supers on x); `x^a_b` compiles (one
   of each). - The base RESETS when a new ordinary atom starts (another char,
   group, or command that is not itself a script operator): `x^a y^b`,
   `x^a{}^b`, `x^a b^c` all compile. - A group `{...}` is its OWN scope: scripts
   inside it are tracked at the deeper depth and do not leak out; entering `{`
   pushes a fresh frame.

   We only scan bytes inside math ranges, skipping comment/verbatim. *)

let double_script_fatal (s : string) : string option =
  let n = String.length s in
  (* Skip comment/verbatim/url AND moving-argument ranges (label/ref/cite keys),
     where a `_`/`^`/`'` is an ordinary character, not a script operator.
     Without the latter, labels like `eq:BSDE_P_W` inside align/equation
     environments — which [find_math_ranges] marks as math — would produce a
     FALSE `x_a_b` double-subscript and over-reject real compiling papers. *)
  let vcu = Validators_common.find_verbatim_comment_url_ranges s in
  (* Include user-defined \ref-alias macros (\reff, \Eqn, …) so their label-key
     arguments are skipped exactly like the built-in \ref/\label. *)
  let ref_aliases = find_ref_alias_macros s in
  let skip = vcu @ find_moving_arg_ranges ~extra:ref_aliases s in
  (* Math ranges MUST be computed on a comment/verbatim/url-BLANKED copy of the
     source. [find_math_ranges] is context-blind about comments, so a `$` or
     `$$` written inside a commented-out line (ubiquitous in real papers — a
     stray or unbalanced `$$` in a `%…` block) desynchronises ALL downstream
     math pairing and spills a huge FAKE math range over the following prose.
     That prose often contains a custom `\ref`-alias (`\reff{def_S_tilde}`,
     `\Eqn{ssnl_v_update}`) whose label-key underscores would then read as a
     `x_a_b` double subscript — a false-NOT-READY on a paper pdflatex compiles
     cleanly. Blanking the vcu ranges to spaces (offset-preserving; a space is
     never a math toggle) neutralises those commented dollars so the math
     pairing is accurate. This is the same defence
     [Validators_common.compute_exempt_ranges] applies. *)
  let blanked = Bytes.of_string s in
  List.iter
    (fun (a, b) ->
      for k = a to b - 1 do
        if k >= 0 && k < n then Bytes.set blanked k ' '
      done)
    vcu;
  let math =
    Validators_common.find_math_ranges (Bytes.unsafe_to_string blanked)
  in
  let in_math off = Validators_common.is_in_math_range math off in
  (* Per brace-frame state: has the current base seen a super / a sub, and has a
     `^` (caret, not just primes) locked the superscript slot. [prime_only] lets
     consecutive primes-before-caret coexist (x''^b) while a prime after a caret
     (x^b') is fatal. *)
  let result = ref None in
  (* stack of mutable frames: (sup_seen, sub_seen, caret_super) *)
  let sup = Array.make 4096 false in
  let sub = Array.make 4096 false in
  let caret = Array.make 4096 false in
  let depth = ref 0 in
  let reset_base d =
    sup.(d) <- false;
    sub.(d) <- false;
    caret.(d) <- false
  in
  reset_base 0;
  let is_escaped idx =
    (* count preceding backslashes; odd ⇒ escaped *)
    let rec count b acc =
      if b < 0 then acc
      else if String.unsafe_get s b = '\\' then count (b - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  (* [skip_cs pos] returns the index just past a control sequence whose
     backslash is at [pos] (control word = run of letters, else single-char
     control symbol). *)
  let skip_cs pos =
    let j = ref (pos + 1) in
    (if !j < n then
       let cc = String.unsafe_get s !j in
       if (cc >= 'a' && cc <= 'z') || (cc >= 'A' && cc <= 'Z') then
         while
           !j < n
           &&
           let d = String.unsafe_get s !j in
           (d >= 'a' && d <= 'z') || (d >= 'A' && d <= 'Z')
         do
           incr j
         done
       else incr j);
    !j
  in
  (* [consume_arg pos] skips ONE script argument starting at [pos]: whitespace,
     then either a brace group (matched, respecting nesting), a control
     sequence, or a single character. Returns the index just past it. This is
     the superscript/subscript operand and does NOT start a fresh base. *)
  let rec consume_arg pos =
    if pos >= n then pos
    else
      let c = String.unsafe_get s pos in
      if c = ' ' || c = '\t' || c = '\n' || c = '\r' then consume_arg (pos + 1)
      else if c = '{' && not (is_escaped pos) then (
        (* skip to matching close brace *)
        let d = ref 1 and j = ref (pos + 1) in
        while !j < n && !d > 0 do
          let cj = String.unsafe_get s !j in
          if cj = '{' && not (is_escaped !j) then incr d
          else if cj = '}' && not (is_escaped !j) then decr d;
          incr j
        done;
        !j)
      else if c = '\\' then skip_cs pos
      else pos + 1
  in
  let i = ref 0 in
  while !i < n && !result = None do
    let pos = !i in
    if in_ranges skip pos || not (in_math pos) then (
      (* Leaving math or skipped bytes: nothing to track; a non-math boundary is
         also a base reset for whatever follows. *)
      reset_base !depth;
      incr i)
    else
      let c = String.unsafe_get s pos in
      if c = '{' && not (is_escaped pos) then (
        (* enter a new scope: the group is a fresh base at deeper depth *)
        if !depth + 1 >= Array.length sup then
          (* depth guard: extreme nesting — bail out of tracking safely by not
             descending; treat the brace as an ordinary base reset. *)
          reset_base !depth
        else (
          incr depth;
          reset_base !depth);
        incr i)
      else if c = '}' && not (is_escaped pos) then (
        if !depth > 0 then decr depth;
        (* The completed group is a FRESH base atom in the enclosing scope
           (operand groups of a preceding script are consumed by [consume_arg]
           and never reach here). A script may follow it and attaches to this
           new base ({x^a}^b, x^a{}^b both compile), so reset the enclosing
           frame's slots. *)
        reset_base !depth;
        incr i)
      else if c = '^' && not (is_escaped pos) then (
        (* A caret is fatal iff a PRIOR caret already locked the super slot.
           Primes-before-caret merge into this caret (x''^b compiles), so we
           gate on [caret], not [sup]. *)
        if caret.(!depth) then
          result :=
            Some "double superscript in math (x^a^b): ! Double superscript"
        else (
          sup.(!depth) <- true;
          caret.(!depth) <- true;
          (* consume the superscript's operand so it is not seen as a base *)
          i := consume_arg (pos + 1) - 1);
        incr i)
      else if c = '\'' && not (is_escaped pos) then (
        (* prime = superscript. Fatal only if a caret already locked the super
           slot; primes-before-caret merge and are fine. A prime has no operand
           (it is self-contained). *)
        if caret.(!depth) then
          result :=
            Some
              "double superscript in math (prime after ^): ! Double superscript"
        else sup.(!depth) <- true;
        incr i)
      else if c = '_' && not (is_escaped pos) then (
        if sub.(!depth) then
          result := Some "double subscript in math (x_a_b): ! Double subscript"
        else (
          sub.(!depth) <- true;
          i := consume_arg (pos + 1) - 1);
        incr i)
      else if c = ' ' || c = '\t' || c = '\n' || c = '\r' then
        (* whitespace does NOT reset the base for script purposes: `x^a ^b`
           still fails as a double superscript. Skip without resetting. *)
        incr i
      else if c = '\\' then (
        (* A command token begins a fresh base atom (e.g. \alpha). *)
        reset_base !depth;
        i := skip_cs pos)
      else (
        (* an ordinary character token: this begins a fresh base atom. *)
        reset_base !depth;
        incr i)
  done;
  !result

(* ── Detector (2), DROPPED: misplaced alignment tab `&` ─────────────────── An
   unescaped `&` outside every alignment context IS fatal in pdflatex ("!
   Misplaced alignment tab character &."), but a SOUND detector for it cannot be
   made free of over-rejection on real compiling papers without full macro
   expansion: - Real papers define custom alignment-environment shortcut macros
   (\def\bea{\begin{eqnarray}}, \bal, \be, …); a `&` inside `\bea … \eea` is
   legal but has no `\begin{...}` for an environment-stack to see. - A `&`
   inside a moving/name argument (\label{a&b}, \href{…&…}, \Cref{…}) COMPILES
   (the argument is not re-typeset). A cross-check over the real published-paper
   corpus fired on 107 root documents that pdflatex compiles cleanly — a gross
   over-rejection. Per the STEP's rule ("if it can't be made precise, drop it
   and say so"), the `&` detector is NOT part of the gate. Detectors (1), (3),
   (4) remain, and each was corpus-validated to zero over-rejection. A
   [misplaced_amp_fatal] stub is deliberately not exported; the gate is the
   three precise detectors below. *)

(* ── Detector (3): no \documentclass (nor \documentstyle) ───────────────── A
   document with no \documentclass / \documentstyle anywhere outside
   comment/verbatim cannot set up the format → fatal (no PDF). *)

let no_documentclass_fatal (s : string) : string option =
  let n = String.length s in
  let skip = Validators_common.find_verbatim_comment_url_ranges s in
  let is_escaped idx =
    let rec count b acc =
      if b < 0 then acc
      else if String.unsafe_get s b = '\\' then count (b - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let starts pfx j =
    let pl = String.length pfx in
    j + pl <= n && String.sub s j pl = pfx
  in
  let found = ref false in
  let i = ref 0 in
  while !i < n && not !found do
    let pos = !i in
    if in_ranges skip pos then incr i
    else if
      (not (is_escaped pos))
      && (starts "\\documentclass" pos || starts "\\documentstyle" pos)
    then found := true
    else incr i
  done;
  if !found then None
  else
    Some
      "no \\documentclass (nor \\documentstyle) in document: ! LaTeX Error: \
       missing \\documentclass"

(* ── Detector (4): \usepackage after \begin{document} ─────────────────────
   \usepackage is a preamble-only command; any occurrence after the first
   \begin{document} → "! LaTeX Error: Can be used only in preamble." FATAL.
   Comment/verbatim-aware for both the \begin{document} anchor and the offending
   \usepackage. *)

let usepackage_after_begin_fatal (s : string) : string option =
  let n = String.length s in
  let skip = Validators_common.find_verbatim_comment_url_ranges s in
  let is_escaped idx =
    let rec count b acc =
      if b < 0 then acc
      else if String.unsafe_get s b = '\\' then count (b - 1) (acc + 1)
      else acc
    in
    count (idx - 1) 0 land 1 = 1
  in
  let starts pfx j =
    let pl = String.length pfx in
    j + pl <= n && String.sub s j pl = pfx
  in
  (* locate first real \begin{document} *)
  let begin_doc = ref (-1) in
  let i = ref 0 in
  while !i < n && !begin_doc < 0 do
    let pos = !i in
    if in_ranges skip pos then incr i
    else if (not (is_escaped pos)) && starts "\\begin{document}" pos then
      begin_doc := pos
    else incr i
  done;
  if !begin_doc < 0 then None
    (* no document body; detector (3)/parse covers it *)
  else
    let result = ref None in
    let j = ref (!begin_doc + String.length "\\begin{document}") in
    while !j < n && !result = None do
      let pos = !j in
      if in_ranges skip pos then incr j
      else if (not (is_escaped pos)) && starts "\\usepackage" pos then
        result :=
          Some
            "\\usepackage after \\begin{document}: ! LaTeX Error: Can be used \
             only in preamble"
      else incr j
    done;
    !result

(* ── Public entry ─────────────────────────────────────────────────────── *)
let structural_fatal_reasons (source : string) : string list =
  List.filter_map
    (fun f -> f source)
    [
      double_script_fatal;
      (* Detector (2), the misplaced-`&` detector, is DROPPED — see its section
         above: it cannot be made over-rejection-free without macro
         expansion. *)
      no_documentclass_fatal;
      usepackage_after_begin_fatal;
    ]
