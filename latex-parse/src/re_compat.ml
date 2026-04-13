(* ══════════════════════════════════════════════════════════════════════
   Re_compat — thread-safe Str-compatible regex operations

   Drop-in replacement for OCaml's Str module using the Re library. Translates
   Str's regex syntax to PCRE and returns match results as values instead of
   storing them in global mutable state.

   Str syntax differences handled by translate_str_to_pcre: \( → ( \) → ) \| → |
   \? → ? \+ → +
   ══════════════════════════════════════════════════════════════════════ *)

type regexp = Re.re
type match_result = Re.Group.t

(* ── Str-to-PCRE syntax translation ───────────────────────────────── *)

let translate_str_to_pcre (pat : string) : string =
  (* Str vs PCRE differences: - \( \) are group delimiters in Str → ( ) in PCRE
     - \| is alternation in Str → | in PCRE - Bare ( ) | are literal in Str → \(
     \) \| in PCRE - *, +, ? are quantifiers in BOTH (identical semantics) - \*,
     \+, \? are literal chars in BOTH (identical semantics) - Character classes
     [a-z], escapes \n \t \\ etc. are identical *)
  let len = String.length pat in
  let buf = Buffer.create (len + 16) in
  let i = ref 0 in
  while !i < len do
    let c = pat.[!i] in
    if c = '\\' && !i + 1 < len then (
      let next = pat.[!i + 1] in
      match next with
      (* Str group/alternation escapes → PCRE bare chars *)
      | '(' ->
          Buffer.add_char buf '(';
          i := !i + 2
      | ')' ->
          Buffer.add_char buf ')';
          i := !i + 2
      | '|' ->
          Buffer.add_char buf '|';
          i := !i + 2
      (* All other \X escapes pass through unchanged — this includes \*, \+, \?,
         \n, \t, \\, \[, \], \., \^, \$, \d, etc. These are identical between
         Str and PCRE. *)
      | _ ->
          Buffer.add_char buf '\\';
          Buffer.add_char buf next;
          i := !i + 2)
    else
      match c with
      (* Bare ( ) | { } are literal in Str but special in PCRE → escape them *)
      | '(' ->
          Buffer.add_string buf "\\(";
          i := !i + 1
      | ')' ->
          Buffer.add_string buf "\\)";
          i := !i + 1
      | '|' ->
          Buffer.add_string buf "\\|";
          i := !i + 1
      | '{' ->
          Buffer.add_string buf "\\{";
          i := !i + 1
      | '}' ->
          Buffer.add_string buf "\\}";
          i := !i + 1
      (* Everything else (including bare *, +, ?, ., ^, $, [, ]) is the same in
         both Str and PCRE *)
      | _ ->
          Buffer.add_char buf c;
          i := !i + 1
  done;
  Buffer.contents buf

(* ── Compilation ──────────────────────────────────────────────────── *)

let regexp (pat : string) : regexp =
  let pcre_pat = translate_str_to_pcre pat in
  try Re.compile (Re.Pcre.re pcre_pat)
  with exn ->
    Printf.eprintf
      "[Re_compat] PARSE ERROR on pattern:\n\
      \  Str: %S\n\
      \  PCRE: %S\n\
      \  Error: %s\n\
       %!"
      pat pcre_pat (Printexc.to_string exn);
    raise exn

let regexp_string (s : string) : regexp = Re.compile (Re.str s)
let quote (s : string) : string = Re.Pcre.quote s

(* ── Search ───────────────────────────────────────────────────────── *)

let search_forward (re : regexp) (s : string) (pos : int) : match_result * int =
  match Re.exec_opt ~pos re s with
  | Some group ->
      let start = Re.Group.start group 0 in
      (group, start)
  | None -> raise Not_found

(* ── Match access ─────────────────────────────────────────────────── *)

let matched_group (mr : match_result) (n : int) (_s : string) : string =
  try Re.Group.get mr n with Not_found | Invalid_argument _ -> raise Not_found

let matched_string (mr : match_result) (_s : string) : string =
  Re.Group.get mr 0

let match_end (mr : match_result) : int = Re.Group.stop mr 0
let match_beginning (mr : match_result) : int = Re.Group.start mr 0

(* ── Split ────────────────────────────────────────────────────────── *)

let split (re : regexp) (s : string) : string list = Re.split re s
