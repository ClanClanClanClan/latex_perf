(** Tier 2 Stage 2 migration tests: REF-008 / REF-010 now consume the
    comment/verbatim-aware [Ast_semantic_state] extractors, so a `\ref` /
    `\label` / `@entry` written inside a comment or verbatim block is no longer
    a semantic declaration and must NOT trigger these rules (the false-match
    correction the old regex extractors got wrong). Each case pairs a POSITIVE
    trigger (proves the rule still fires on real content) with a FALSE-MATCH
    case (proves the protected occurrence is now ignored). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let find_result id src =
  List.find_opt
    (fun (r : Validators.result) -> r.id = id)
    (Validators.run_all src)

let fires id src = find_result id src <> None

let expect tag cond =
  incr cases;
  if not cond then (
    incr fails;
    Printf.eprintf "[ref-ast-migration] FAIL: %s\n%!" tag)

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ── REF-010: figure referenced before first mention. ─────────────── *)
  (* Positive: a real \ref{fig:x} precedes the real \label{fig:x} → fires. *)
  expect "REF-010 fires on real ref-before-label"
    (fires "REF-010"
       "See \\ref{fig:x} above.\n\
        Later \\begin{figure}\\label{fig:x}\\end{figure}");

  (* False-match: the ONLY ref-before-label pairing is a \ref inside a %
     comment; the real \label comes after. The old regex extractor counted the
     commented ref (pos < label pos) and fired; the AST extractor drops it. *)
  expect "REF-010 does NOT fire when the earlier ref is in a comment"
    (not
       (fires "REF-010"
          "% early note: \\ref{fig:x}\n\
           Figure \\label{fig:x} defined, \\ref{fig:x}."));

  (* False-match (verbatim): earlier ref inside a verbatim block. *)
  expect "REF-010 does NOT fire when the earlier ref is in verbatim"
    (not
       (fires "REF-010"
          "\\begin{verbatim}\n\
           \\ref{fig:x}\n\
           \\end{verbatim}\n\
           \\label{fig:x} then \\ref{fig:x}."));

  (* ── REF-008: duplicate bib/cite key. ─────────────────────────────── *)
  (* Positive: two @entry blocks share key "dup" → fires. *)
  expect "REF-008 fires on genuinely duplicated bib key"
    (fires "REF-008" "@article{dup, title={A}}\n@book{dup, title={B}}\n");

  (* False-match: one real @entry{dup} and a second @entry{dup} shown inside a
     verbatim listing. Old regex saw 2 → duplicate → fired; AST drops the
     verbatim one → only 1 real key → no duplicate. *)
  expect "REF-008 does NOT fire when the duplicate is in verbatim"
    (not
       (fires "REF-008"
          "@article{dup, title={A}}\n\
           \\begin{verbatim}\n\
           @book{dup, title={B}}\n\
           \\end{verbatim}\n"));

  (* False-match (comment): the duplicate is in a % comment. *)
  expect "REF-008 does NOT fire when the duplicate is in a comment"
    (not
       (fires "REF-008" "@article{dup, title={A}}\n% @book{dup, title={B}}\n"));

  if !fails = 0 then (
    Printf.printf "[ref-ast-migration] PASS %d cases\n%!" !cases;
    exit 0)
  else (
    Printf.eprintf "[ref-ast-migration] %d/%d FAILED\n%!" !fails !cases;
    exit 1)
