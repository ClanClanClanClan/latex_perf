(* Fix guard (R7-3). See fix_guard.mli for the contract and the error-polarity
   note (this is a SUBTRACTIVE filter: over-wide is safe, narrow/misplaced is
   not).

   v1 implements the two highest-damage regions, both purely lexical and both
   over-wide-safe. Regions deliberately NOT yet covered, in measured-damage
   order: 3. filename arguments (\input \include \includegraphics \bibliography
   ...) 4. key arguments (\label \ref \cite ... — also the SCRIPT-001->007
   cascade) 5. tabular/array preamble (the pilot-only good_longtable_free
   corruption) Their fixtures stay recorded as known breakages in
   corpora/apply_fixes/, so the round-trip gate proves exactly which classes are
   closed and which are not. *)

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

let protected_ranges (src : string) : (int * int) list =
  let rs = control_symbol_ranges src @ picture_ranges src in
  List.sort (fun (a, _) (b, _) -> compare a b) rs

(* Half-open intersection. A pure insertion (s = e) is a point, and a point on a
   protected range's exclusive end is NOT inside it. *)
(* Rules whose contract IS editing control symbols. Derived from the golden
   variants in check_producer_coverage.py: each of these was measured emitting a
   legitimate fix that region 1 withheld. That gate is the completeness check —
   a control-symbol-aware rule missing from this list loses its fix and the gate
   goes red, which is the safe direction (functionality lost, nothing corrupted).

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

let intersects (s, e) (a, b) = if s = e then a <= s && s < b else s < b && a < e

let filter ~(src : string) ~(rule_id : string) (edits : Cst_edit.t list) :
    Cst_edit.t list =
  match edits with
  | [] -> []
  | _ ->
      (* A control-symbol-aware rule still gets the picture region: no producer
         has any business rewriting inside a TikZ path. *)
      let ranges =
        if List.mem rule_id control_symbol_aware then picture_ranges src
        else protected_ranges src
      in
      if ranges = [] then edits
      else
        List.filter
          (fun (ed : Cst_edit.t) ->
            let span = (ed.start_offset, ed.end_offset) in
            not (List.exists (fun r -> intersects span r) ranges))
          edits
