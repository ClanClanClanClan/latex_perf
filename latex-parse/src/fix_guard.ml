(* Fix guard (R7-3). See fix_guard.mli for the contract and the error-polarity
   note (this is a SUBTRACTIVE filter: over-wide is safe, narrow/misplaced is
   not).

   Regions implemented, all purely lexical: 1. control symbol arguments, 2.
   TikZ/PGF picture bodies, 3a. filename arguments, 3b. package-spec arguments.

   Regions NOT yet covered, in measured-damage order, and — this part matters —
   with UNEQUAL evidence behind them: 4. key arguments (\label \ref \cite ...,
   also the SCRIPT-001->007 cascade). NO fixture exists for this class anywhere
   in the corpora, so the round-trip gate is SILENT on it. Its absence from the
   gate's baseline is not evidence that it is harmless; it is evidence that
   nobody has measured it. A key-argument corruption would ship with every gate
   green. 5. tabular/array preamble. This one IS measured: good_longtable_free
   under the pilot profile occupies two rows of
   corpora/apply_fixes/manifest.json and is, after region 3, the ONLY remaining
   manufactured false-READY. An earlier version of this comment claimed both
   classes were fixture-tracked. Only region 5 is. *)

let is_letter c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

(* ── Region 1: control-symbol arguments ──────────────────────────────────── A
   backslash followed by a NON-letter is a control SYMBOL: the byte after the
   backslash is the command, not text. The accent commands (grave, acute,
   circumflex, diaeresis, tilde, macron, dot, bar, slash, cedilla-comma) all
   have this shape, and rewriting that byte destroys the command.

   NB: this comment deliberately spells the accents out in words. An OCaml
   comment still lexes string literals, so writing the escape sequences
   literally here opens an unterminated string and fails the build.

   Both bytes are protected. Protecting only the symbol would let an edit that
   starts on the backslash and ends after it slip through. *)
let control_symbol_ranges (src : string) : (int * int) list =
  let n = String.length src in
  let acc = ref [] in
  let i = ref 0 in
  while !i < n do
    if String.unsafe_get src !i = '\\' && !i + 1 < n then
      let c = String.unsafe_get src (!i + 1) in
      if is_letter c then (
        (* control WORD: \foo — the name is letters, ordinary prose may follow.
           Skip it so its trailing letters are not rescanned as a new escape. *)
        let j = ref (!i + 1) in
        while !j < n && is_letter (String.unsafe_get src !j) do
          incr j
        done;
        i := !j)
      else (
        (* control SYMBOL: protect the backslash and the symbol byte, then step
           past both — otherwise `\\` would have its second backslash re-read as
           the start of a fresh escape. *)
        acc := (!i, !i + 2) :: !acc;
        i := !i + 2)
    else incr i
  done;
  List.rev !acc

(* ── Region 2: TikZ / PGF picture bodies ───────────────────────────────────
   Inside a picture, `--` is pgf's line-to PATH OPERATOR, `-|` and `|-` are the
   orthogonal variants, and `..` introduces a curve. None of it is punctuation.

   The whole environment body is protected, begin and end markers included. That
   is deliberately over-wide: typographic fixes inside a picture have no value
   and real risk. Note tikzpicture is NOT in Validators_common's verbatim env
   list, so nothing else was covering this. *)
let picture_envs = [ "tikzpicture"; "pgfpicture" ]

let find_all (hay : string) (needle : string) : int list =
  let nh = String.length hay and nn = String.length needle in
  if nn = 0 || nn > nh then []
  else
    let acc = ref [] in
    for i = nh - nn downto 0 do
      if String.sub hay i nn = needle then acc := i :: !acc
    done;
    !acc

let picture_ranges (src : string) : (int * int) list =
  List.concat_map
    (fun env ->
      let b = "\\begin{" ^ env ^ "}" and e = "\\end{" ^ env ^ "}" in
      let ends = find_all src e in
      List.filter_map
        (fun bs ->
          (* First \end{env} at or after this \begin{env}. Picture environments
             do not nest in practice; if one ever did, taking the first close is
             the over-wide-safe direction only for the inner pair, so an
             unmatched \begin protects to end-of-file rather than protecting
             nothing. *)
          match List.find_opt (fun es -> es >= bs) ends with
          | Some es -> Some (bs, es + String.length e)
          | None -> Some (bs, String.length src))
        (find_all src b))
    picture_envs

(* ── Region 3: filename and package-spec arguments ─────────────────────────
   The braced argument of an include-family command is a FILESYSTEM IDENTIFIER,
   not prose. Measured on adv_input_filename.tex in all four fixer modes:
   TYPO-002 rewrites the double hyphen of \input{adv--child} to an en dash, and
   the pilot profile additionally inserts a thin-space command INTO the name, so
   the emitted document asks TeX for a file that does not exist.

   Two command sets, because they need different exemptions.

   3a FILENAME arguments — names the author chose, which really do contain the
   characters typography rules target (fig--v2, data-2020). No producer has any
   business rewriting one, so this region has no exemption list.

   3b PACKAGE-SPEC arguments — \usepackage and friends. The argument is still a
   filename (a .sty or .cls, which for a local package the author also named)
   and the same rewrite corrupts it; but four shipped producers reorder whole
   \usepackage lines as their CONTRACT, so this region carries the
   package_spec_aware exemption below. Splitting 3a from 3b keeps that exemption
   narrow: PKG-002 is exempt from package specs only, and is still blocked from
   filenames.

   FAILURE DIRECTION (the argument this module requires of every region). A
   range always STARTS at the command backslash and runs contiguously forward,
   so it may be over-wide; the danger is the opposite — a SHORT range that ends
   before the argument and leaves load-bearing bytes exposed.

   An earlier draft of this scanner claimed it could be over-wide but never
   short. That was FALSE. An audit produced three shapes that broke it, all of
   them shapes region 3 exists for. Each is now handled explicitly and pinned by
   a test: (1) a right bracket inside a braced option VALUE, as in
   backslash-usepackage[Ligatures={x]y}]{name} — the option group now closes
   only at an UNESCAPED bracket at brace DEPTH 0, mirroring the verified
   drop_after_rbracket in proofs/BodyTokenFrontEnd.v, which was written for
   exactly this shape; (2) a TeX comment between the command and its argument —
   now skipped to end of line, because TeX swallows it before reading the
   argument; (3) any other byte this scanner does not model, in practice a
   control sequence — the range now extends to end of line instead of stopping
   at the command name.

   The remaining deliberate choices all err over-wide, which only withholds a
   fix: * a mention inside a comment or a verbatim block is protected too. Those
   bytes are never typeset, and declining to model them avoids inheriting the
   comment-blindness bug class that has bitten every scanner reused in this
   codebase. * an unclosed brace or option group protects to end of file — what
   TeX itself does with the unclosed group, and the same choice region 2 makes
   for an unmatched \begin.

   Accepted UNDER-reach, recorded rather than left silent: an argument sitting
   on a LATER line than its command, reached past a token this scanner does not
   model, is not covered; and the plain-TeX bare form is honoured for \input
   only, up to the next whitespace. *)
let filename_arg_cmds =
  [
    "input";
    "include";
    "includeonly";
    "includegraphics";
    "lstinputlisting";
    "verbatiminput";
    "InputIfFileExists";
    "subfile";
    "subfileinclude";
    "bibliography";
    "addbibresource";
    "bibliographystyle";
    "graphicspath";
  ]

let package_arg_cmds =
  [
    "usepackage";
    "RequirePackage";
    "RequirePackageWithOptions";
    "documentclass";
    "LoadClass";
    "LoadClassWithOptions";
  ]

let is_blank c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

(* Advance past whitespace and TeX comments. A comment runs from an unescaped
   percent to end of line and TeX swallows it before reading the argument, so
   stepping over one EXTENDS the search rather than truncating it. Not doing so
   ended the range at the command name for [\includegraphics%c] followed by the
   braced filename on the next line, leaving the filename exposed. *)
let rec skip_blanks_and_comments (src : string) (n : int) (p : int) : int =
  if p >= n then p
  else if is_blank (String.unsafe_get src p) then
    skip_blanks_and_comments src n (p + 1)
  else if String.unsafe_get src p = '%' then (
    let e = ref p in
    while !e < n && String.unsafe_get src !e <> '\n' do
      incr e
    done;
    skip_blanks_and_comments src n !e)
  else p

(* From [k], one past the command name, consume an optional star, any number of
   bracketed option groups, and the first braced group; return one past the last
   byte consumed. [bare] additionally accepts the plain-TeX form (a filename
   terminated by whitespace) when no brace follows. Never returns less than
   [k]. *)
let scan_command_argument (src : string) (k : int) ~(bare : bool) : int =
  let n = String.length src in
  let stop = ref k in
  let i = ref k in
  let found_group = ref false in
  if !i < n && String.unsafe_get src !i = '*' then (
    incr i;
    stop := !i);
  let scanning = ref true in
  while !scanning do
    let j = ref (skip_blanks_and_comments src n !i) in
    if !j >= n then scanning := false
    else
      match String.unsafe_get src !j with
      | '[' ->
          (* Option group. This mirrors the semantics of the VERIFIED
             [drop_after_rbracket] (proofs/BodyTokenFrontEnd.v:388, shipped in
             #508 for exactly this shape): the group closes at an UNESCAPED
             right bracket at brace DEPTH 0. Closing at the first raw bracket
             instead ended the range before the filename in
             [\usepackage[Ligatures={x]y}]{fontspec-local}] — a SHORT range,
             which is the one failure this module must not produce. An unclosed
             group runs to end of file, which is over-wide and therefore
             safe. *)
          let e = ref (!j + 1) and depth = ref 0 and fin = ref (-1) in
          while !fin < 0 && !e < n do
            (match String.unsafe_get src !e with
            | '\\' -> incr e
            | '{' -> incr depth
            | '}' -> if !depth > 0 then decr depth
            | ']' -> if !depth = 0 then fin := !e + 1
            | _ -> ());
            incr e
          done;
          let e = if !fin >= 0 then !fin else n in
          stop := e;
          i := e
      | '{' ->
          let depth = ref 0 and e = ref !j and fin = ref (-1) in
          while !fin < 0 && !e < n do
            (match String.unsafe_get src !e with
            | '\\' -> incr e (* an escaped brace is a character, not a group *)
            | '{' -> incr depth
            | '}' ->
                decr depth;
                if !depth = 0 then fin := !e + 1
            | _ -> ());
            incr e
          done;
          stop := if !fin >= 0 then !fin else n;
          found_group := true;
          scanning := false
      | c ->
          (* Bare plain-TeX form. Refuse the openers that cannot start a
             filename, so a command with no argument at all does not swallow the
             next control sequence or a comment. *)
          if bare && not (c = '\\' || c = '%' || c = '}' || c = '$' || c = '&')
          then (
            let e = ref !j in
            while !e < n && not (is_blank (String.unsafe_get src !e)) do
              incr e
            done;
            if !e > !j then (
              stop := !e;
              found_group := true))
          else if not !found_group then (
            (* We bailed on a byte belonging to no argument shape this scanner
               understands — in practice a control sequence, as in
               [\includegraphics\relax{fig-1}]. Ending here would leave a
               filename later on the SAME LINE exposed, so extend to end of
               line: over-wide only withholds a fix, short exposes load-bearing
               bytes. Bounded at the newline so it cannot swallow the
               document. *)
            let e = ref !j in
            while !e < n && String.unsafe_get src !e <> '\n' do
              incr e
            done;
            stop := max !stop !e);
          scanning := false
  done;
  !stop

let argument_ranges (src : string) : (int * int) list * (int * int) list =
  let n = String.length src in
  let fns = ref [] and pkgs = ref [] in
  let i = ref 0 in
  while !i < n do
    if String.unsafe_get src !i = '\\' && !i + 1 < n then
      if is_letter (String.unsafe_get src (!i + 1)) then (
        let start = !i in
        let j = ref (!i + 1) in
        while !j < n && is_letter (String.unsafe_get src !j) do
          incr j
        done;
        (* Whole-name comparison, so \include does not match inside
           \includegraphics. *)
        let name = String.sub src (start + 1) (!j - start - 1) in
        let fn = List.mem name filename_arg_cmds in
        let pk = (not fn) && List.mem name package_arg_cmds in
        if fn || pk then (
          let stop =
            scan_command_argument src !j ~bare:(String.equal name "input")
          in
          let r = (start, max stop !j) in
          if fn then fns := r :: !fns else pkgs := r :: !pkgs;
          i := max !j stop)
        else i := !j)
      else
        (* Control SYMBOL: step past both bytes, so the second backslash of a
           doubled escape is not re-read as the start of a fresh command. *)
        i := !i + 2
    else incr i
  done;
  (List.rev !fns, List.rev !pkgs)

type regions = {
  control_symbol : (int * int) list;
  picture : (int * int) list;
  filename : (int * int) list;
  package_spec : (int * int) list;
}

let compute_regions (src : string) : regions =
  let filename, package_spec = argument_ranges src in
  {
    control_symbol = control_symbol_ranges src;
    picture = picture_ranges src;
    filename;
    package_spec;
  }

(* One-entry memo keyed on the buffer's PHYSICAL identity.

   [filter] is called once per FIRING RULE per converge pass — up to 64 passes,
   with every rule in a pass seeing the same buffer — and the scanners are all
   linear in the buffer (region 2's substring search allocates once per byte per
   needle), so recomputing them per rule dominated the fixer's cost.

   OCaml strings are immutable, so [==] implies equal contents: a stale entry
   can only ever cause a MISS, never a wrong answer. The fix path is
   single-threaded; a concurrent caller would at worst lose the cache hit. *)
let memo : (string * regions) option ref = ref None

let regions_of (src : string) : regions =
  match !memo with
  | Some (s, r) when s == src -> r
  | _ ->
      let r = compute_regions src in
      memo := Some (src, r);
      r

let protected_ranges (src : string) : (int * int) list =
  let r = regions_of src in
  let rs = r.control_symbol @ r.picture @ r.filename @ r.package_spec in
  List.sort (fun (a, _) (b, _) -> compare a b) rs

(* Rules whose contract IS editing control symbols. Derived from the golden
   variants in check_producer_coverage.py: each of these was measured emitting a
   legitimate fix that region 1 withheld. That gate is the completeness check —
   a control-symbol-aware rule missing from this list loses its fix and the gate
   goes red, which is the safe direction (functionality lost, nothing
   corrupted).

   TYPO-013 is deliberately ABSENT: curling an ASCII backtick is exactly the
   prose-blind rewrite that destroyed the grave-accent command in
   good_accents_utf8. *)
let control_symbol_aware =
  [
    "CS-001" (* spurious thin space before a unit *);
    "MATH-082" (* doubled negative thin space *);
    "TYPO-015" (* doubled escaped percent *);
    "TYPO-017" (* accent brace form *);
    "TYPO-055" (* consecutive thin spaces *);
    "TYPO-056" (* legacy accent brace form *);
    "TYPO-062" (* literal backslash to \textbackslash *);
  ]

(* Rules whose contract IS rewriting a package specification: each reorders two
   whole \usepackage lines, so its edit necessarily spans one. Derived the same
   way as the list above — from the golden variants in
   check_producer_coverage.py, which is the completeness check.

   The package INSERTERS (CJK-004, CJK-006, PKG-011, PKG-012, REF-011,
   STRUCT-001) are deliberately absent: they emit a pure insertion at the offset
   just PAST the closing brace, and a point on a range's exclusive end is not
   inside it, so region 3b never withholds them. That is verified by the same
   gate, not assumed here. *)
let package_spec_aware =
  [
    "PKG-002" (* geometry before hyperref *);
    "PKG-007" (* hyperref load order *);
    "PKG-023" (* unicode-math before microtype *);
    "TIKZ-007" (* tikz before hyperref *);
  ]

(* Half-open intersection. A pure insertion (s = e) is a point, and a point on a
   protected range's exclusive end is NOT inside it. *)
let intersects (s, e) (a, b) = if s = e then a <= s && s < b else s < b && a < e

let filter ~(src : string) ~(rule_id : string) (edits : Cst_edit.t list) :
    Cst_edit.t list =
  match edits with
  | [] -> []
  | _ ->
      let r = regions_of src in
      (* Exemptions are PER REGION, never global. A control-symbol-aware rule
         still gets the picture, filename and package regions; a package-aware
         reorderer is still blocked from filenames and TikZ paths. Nothing is
         ever exempt from regions 2 and 3a. *)
      let active =
        (if List.mem rule_id control_symbol_aware then []
         else [ r.control_symbol ])
        @ [ r.picture; r.filename ]
        @ if List.mem rule_id package_spec_aware then [] else [ r.package_spec ]
      in
      let blocked span =
        List.exists
          (fun rs -> List.exists (fun rg -> intersects span rg) rs)
          active
      in
      List.filter
        (fun (ed : Cst_edit.t) ->
          not (blocked (ed.start_offset, ed.end_offset)))
        edits
