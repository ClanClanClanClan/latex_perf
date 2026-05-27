(** Direct unit tests for [is_ascii_context] and [is_extended_context] (defined
    in [validators_common.ml]).

    Background — v27.0.61 introduced [is_ascii_context] as the codebase's first
    positive-context filter helper, used by CJK-001 / CJK-002 to gate
    fullwidth-punctuation fixes by the surrounding byte-class majority. v27.0.62
    added its symmetric inverse [is_extended_context], used by CJK-010 to gate
    the opposite fix (ASCII → fullwidth in CJK-heavy runs). Both helpers are
    load-bearing for the CJK family; therefore they get direct unit tests
    mirroring the [test_math_ranges.ml] discipline. *)

open Printf
open Latex_parse_lib.Validators_common

(** Each case: (label, source, off, expected). [off] is the byte offset of the
    candidate's first byte; [candidate_bytes] defaults to 3 (UTF-8 3-byte
    sequence for U+FFxx fullwidth chars). [window] defaults to 32 bytes per
    side. *)
let default_cases : (string * string * int * bool) list =
  [
    (* Pure ASCII surroundings → true. *)
    ( "all-ASCII window (Latin)",
      "Hello world\xef\xbc\x8cthis is ASCII context",
      11,
      true );
    ( "all-ASCII window (mixed letters and digits)",
      "abc 123 def\xef\xbc\x8cghi 456 jkl",
      11,
      true );
    ( "all-ASCII window (ASCII punctuation)",
      "x, y; z!\xef\xbc\x8c(a) {b} [c]",
      8,
      true );
    (* Pure non-ASCII surroundings → false. *)
    ( "all-CJK window",
      "\xe4\xb8\xad\xe6\x96\x87\xef\xbc\x8c\xe4\xb8\xad\xe6\x96\x87",
      6,
      false );
    (* All ~6 bytes around the candidate are extended (CJK) — strict-majority
       extended → false. *)

    (* Mixed surroundings — ties resolve to false (strict majority required). *)
    ( "tie (equal ASCII / extended counts) → false",
      "abc\xef\xbc\x8c\xe4\xb8\xad\xe6\x96\x87",
      3,
      false );
    (* 3 ASCII bytes ("abc") + 6 extended bytes after candidate → false. *)

    (* Boundary clipping — candidate near start. *)
    ( "candidate at offset 0 (no left context)",
      "\xef\xbc\x8cabc def ghi jkl mno",
      0,
      true );
    (* All right-side bytes ASCII → true. *)

    (* Boundary clipping — candidate near EOF. *)
    ( "candidate near EOF (clipped right window)",
      "abcdefghijklmnopqr\xef\xbc\x8c",
      18,
      true );
    (* All left-side bytes ASCII, no right context → ASCII majority → true. *)

    (* Window size — small window, ASCII dominates. *)
    ("small window (window=4) ASCII dominates", "abcd\xef\xbc\x8cwxyz", 4, true);
    (* Window size — small window, extended dominates. *)
    ( "small window (window=4) extended dominates",
      "\xe4\xb8\xad\xe6\x96\x87\xef\xbc\x8c\xe4\xb8\xad\xe6\x96\x87",
      6,
      false );
    (* Standalone candidate with no context at all → false (0 == 0 tie →
       false). *)
    ("candidate alone, empty context → false", "\xef\xbc\x8c", 0, false);
    (* Long ASCII run on one side, short extended on the other → true. *)
    ( "long-ASCII left, no right",
      "the quick brown fox jumps over\xef\xbc\x8c",
      30,
      true );
    (* Exactly at threshold — 1 ASCII vs 0 extended → true (strict majority). *)
    ("one ASCII byte beats zero extended", "a\xef\xbc\x8c", 1, true);
    (* Exactly at threshold — 0 ASCII vs 1 extended → false. *)
    ("zero ASCII against one extended byte", "\xc2\xa0\xef\xbc\x8c", 2, false);
    (* The two-byte leading U+00A0 (C2 A0) — both bytes >= 0x80 → extended. *)

    (* Custom window — small window narrows decision. *)
    ("very small window=2 ASCII dominates", "ab\xef\xbc\x8ccd", 2, true);
  ]

(** Default-parameter tests (window=32, candidate_bytes=3). *)

(** Custom-window tests: pass an explicit [~window] to verify the parameter is
    honoured. *)
let custom_window_cases : (string * string * int * int * bool) list =
  [
    (* window=2 with 3 ASCII bytes on each side; only 2 bytes counted per side →
       4 ASCII vs 0 extended → true. *)
    ("explicit window=2, all-ASCII context", "xy\xef\xbc\x8cab", 2, 2, true);
    (* window=2 with 3 extended bytes on each side; only 2 bytes counted per
       side → 0 ASCII vs 4 extended → false. *)
    ( "explicit window=2, all-extended context",
      "\xe4\xb8\xad\xef\xbc\x8c\xe6\x96\x87",
      3,
      2,
      false );
    (* window=0 → no context counted → 0 == 0 tie → false. *)
    ("explicit window=0 → no context → false", "abc\xef\xbc\x8cxyz", 3, 0, false);
  ]

(** Custom candidate_bytes tests: verify multi-byte candidates of length other
    than 3 are handled. *)
let custom_candidate_cases : (string * string * int * int * bool) list =
  [
    (* candidate_bytes=2 for a 2-byte U+00xx sequence, all-ASCII surroundings →
       true. *)
    ("candidate_bytes=2, ASCII context", "abc\xc2\xa0xyz", 3, 2, true);
    (* candidate_bytes=1 for a single-byte candidate, all-ASCII → true. *)
    ("candidate_bytes=1, ASCII context", "abc\xffxyz", 3, 1, true);
    (* candidate_bytes=2, extended context → false. *)
    ( "candidate_bytes=2, extended context",
      "\xe4\xb8\xad\xc2\xa0\xe6\x96\x87",
      3,
      2,
      false );
  ]

let () =
  let fails = ref 0 in
  let total = ref 0 in
  (* Default-parameter tests. *)
  List.iter
    (fun (label, src, off, exp) ->
      incr total;
      let got = is_ascii_context src off in
      if got <> exp then (
        incr fails;
        eprintf
          "[ascii-context] FAIL %s\n  src: %S\n  off: %d  exp: %b  got: %b\n%!"
          label src off exp got))
    default_cases;
  (* Custom-window tests. *)
  List.iter
    (fun (label, src, off, window, exp) ->
      incr total;
      let got = is_ascii_context ~window src off in
      if got <> exp then (
        incr fails;
        eprintf
          "[ascii-context] FAIL %s\n\
          \  src: %S\n\
          \  off: %d  window: %d  exp: %b  got: %b\n\
           %!"
          label src off window exp got))
    custom_window_cases;
  (* Custom candidate_bytes tests. *)
  List.iter
    (fun (label, src, off, candidate_bytes, exp) ->
      incr total;
      let got = is_ascii_context ~candidate_bytes src off in
      if got <> exp then (
        incr fails;
        eprintf
          "[ascii-context] FAIL %s\n\
          \  src: %S\n\
          \  off: %d  candidate_bytes: %d  exp: %b  got: %b\n\
           %!"
          label src off candidate_bytes exp got))
    custom_candidate_cases;

  (* ── is_extended_context: symmetric inverse, true iff strict-majority
     extended (≥ 0x80). Same window/candidate-exclusion semantics. ──── *)
  let extended_default_cases : (string * string * int * bool) list =
    [
      (* Pure CJK → true. *)
      ( "all-CJK window → true",
        "\xe4\xb8\xad\xe6\x96\x87\xef\xbc\x8c\xe4\xb8\xad\xe6\x96\x87",
        6,
        true );
      (* Pure ASCII → false. *)
      ( "all-ASCII window → false",
        "Hello world\xef\xbc\x8cthis is ASCII context",
        11,
        false );
      (* Tie (3 ASCII bytes + 6 extended bytes counted; 6>3 → true). *)
      ( "3 ASCII vs 6 extended → true (extended strict majority)",
        "abc\xef\xbc\x8c\xe4\xb8\xad\xe6\x96\x87",
        3,
        true );
      (* Exact tie (3 ASCII bytes + 3 extended bytes) → false (mirror of the
         ascii-side tie test above). *)
      ( "tie (3 ASCII vs 3 extended) → false",
        "abc\xef\xbc\x8c\xe4\xb8\xad",
        3,
        false );
      (* Boundary: candidate at offset 0, all-extended right context → true. *)
      ( "candidate at offset 0, extended right → true",
        "\xef\xbc\x8c\xe4\xb8\xad\xe6\x96\x87\xe4\xb8\xad",
        0,
        true );
      (* No-context case (candidate alone) → false (0 == 0 tie). *)
      ("candidate alone, no context → false", "\xef\xbc\x8c", 0, false);
      (* Symmetric to is_ascii_context's "one ASCII vs zero" → here "one
         extended vs zero ASCII" → true. *)
      ("one extended byte beats zero ASCII", "\xc2\xa0\xef\xbc\x8c", 2, true);
      (* Mirror of ascii "long-ASCII left, no right" → "long-extended left, no
         right". *)
      ( "long-extended left, no right → true",
        "\xe4\xb8\xad\xe4\xb8\xad\xe4\xb8\xad\xe4\xb8\xad\xe4\xb8\xad\xe6\x96\x87\xef\xbc\x8c",
        18,
        true );
    ]
  in
  List.iter
    (fun (label, src, off, exp) ->
      incr total;
      let got = is_extended_context src off in
      if got <> exp then (
        incr fails;
        eprintf
          "[ascii-context] FAIL %s\n  src: %S\n  off: %d  exp: %b  got: %b\n%!"
          label src off exp got))
    extended_default_cases;

  (* Symmetry check: for every byte position [p] in [s] that is NOT inside the
     candidate's own bytes, [is_ascii_context] and [is_extended_context] must
     never both be true. (They can both be false in tie cases.) *)
  let symmetry_cases =
    [ "plain ASCII"; "all CJK"; "mixed"; "boundary"; "empty" ]
  in
  let symmetry_inputs =
    [
      "abcdef hello world";
      "\xe4\xb8\xad\xe6\x96\x87\xe6\x97\xa5\xe6\x9c\xac";
      "abc \xe4\xb8\xad xyz";
      "\xef\xbc\x8cend";
      "";
    ]
  in
  List.iter2
    (fun label src ->
      let n = String.length src in
      for off = 0 to n - 1 do
        let a = is_ascii_context ~candidate_bytes:1 src off in
        let e = is_extended_context ~candidate_bytes:1 src off in
        incr total;
        if a && e then (
          incr fails;
          eprintf
            "[ascii-context] FAIL symmetry %s at off=%d (both true)\n\
            \  src: %S\n\
             %!"
            label off src)
      done)
    symmetry_cases symmetry_inputs;

  if !fails = 0 then (
    printf "[ascii-context] PASS %d cases\n%!" !total;
    exit 0)
  else exit 1
