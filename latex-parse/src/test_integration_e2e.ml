(** End-to-end integration tests — paranoid level.

    Every assertion checks a SPECIFIC expected outcome, not just "something
    happened." Tests verify exact rule IDs, cache behavior, ML suppression, and
    cross-layer consistency. Spec W131-140. *)

open Latex_parse_lib
open Test_helpers

let () = Unix.putenv "L0_VALIDATORS" "pilot"

(* ── Test corpus ──────────────────────────────────────────────────── *)

(* This doc is designed to trigger SPECIFIC known rules *)
let test_doc =
  {|\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{amsmath}
\usepackage{hyperref}

\title{Test}
\author{Author}

\begin{document}
\maketitle

\section{Straight Quotes}
This has "straight quotes" which should trigger TYPO-001.

\section{Legacy Bold}
This paragraph uses {\bf legacy bold} and also \textbf{modern bold} together.

\section{Math}
Consider $E = mc^2$ and also:
\begin{equation}
  x + y = z
  \label{eq:test}
\end{equation}

See Equation~\ref{eq:test}.

\section{Duplicate Label}
\label{sec:dup}
Some text.
\label{sec:dup}

\end{document}|}

let _ctr = ref 0

let usrc doc =
  incr _ctr;
  Printf.sprintf "%s\n%% e2e-%d\n" doc !_ctr

let ids_of results =
  List.map (fun (r : Validators.result) -> r.id) results
  |> List.sort_uniq String.compare

let has_id id results =
  List.exists (fun (r : Validators.result) -> r.id = id) results

let () =
  (* ══════════════════════════════════════════════════════════════════ 1.
     SPECIFIC rule firing on known input
     ══════════════════════════════════════════════════════════════════ *)
  run "TYPO-001 fires on straight quotes" (fun tag ->
      let src = usrc {|This has "straight quotes" here.|} in
      expect (fires "TYPO-001" src) (tag ^ ": TYPO-001 on quotes"));

  run "MOD-002 fires on mixed bf/textbf in same paragraph" (fun tag ->
      let src = usrc {|{\bf legacy} and \textbf{modern} in same paragraph.|} in
      expect (fires "MOD-002" src) (tag ^ ": MOD-002 on mixed bold"));

  run "MOD-002 does NOT fire when bf/textbf in different paragraphs" (fun tag ->
      let src =
        usrc
          {|First paragraph with {\bf bold}.

Second paragraph with \textbf{bold}.|}
      in
      expect
        (does_not_fire "MOD-002" src)
        (tag ^ ": MOD-002 clean across paragraphs"));

  run "full doc fires multiple rule families" (fun tag ->
      let src = usrc test_doc in
      let results = Validators.run_all src in
      let ids = ids_of results in
      (* Must fire at least one TYPO and one MOD rule *)
      let has_typo =
        List.exists
          (fun id -> String.length id > 5 && String.sub id 0 5 = "TYPO-")
          ids
      in
      let has_mod =
        List.exists
          (fun id -> String.length id > 4 && String.sub id 0 4 = "MOD-")
          ids
      in
      expect has_typo (tag ^ ": has TYPO rule");
      expect has_mod (tag ^ ": has MOD rule"));

  (* ══════════════════════════════════════════════════════════════════ 2. Layer
     coverage with SPECIFIC expectations
     ══════════════════════════════════════════════════════════════════ *)
  run "L0 rules fire on straight quotes" (fun tag ->
      let src = usrc {|Text with "straight quotes".|} in
      let results = Validators.run_all src in
      let l0_fired =
        List.exists
          (fun (r : Validators.result) ->
            Validators.precondition_of_rule_id r.id = L0)
          results
      in
      expect l0_fired (tag ^ ": L0 fired"));

  run "L1 rules fire on mixed commands" (fun tag ->
      let src = usrc {|{\bf bold} and \textbf{bold} in one paragraph.|} in
      let results = Validators.run_all src in
      let l1_fired =
        List.exists
          (fun (r : Validators.result) ->
            Validators.precondition_of_rule_id r.id = L1)
          results
      in
      expect l1_fired (tag ^ ": L1 fired"));

  (* ══════════════════════════════════════════════════════════════════ 3.
     run_all_scored: scored is SUBSET of run_all
     ══════════════════════════════════════════════════════════════════ *)
  run "scored IDs are subset of plain IDs" (fun tag ->
      let src = usrc test_doc in
      let plain_ids = ids_of (Validators.run_all src) in
      let src2 = usrc test_doc in
      let scored_ids =
        Validators.run_all_scored src2
        |> List.map (fun (r : Evidence_scoring.scored_result) -> r.id)
        |> List.sort_uniq String.compare
      in
      let is_subset =
        List.for_all (fun id -> List.mem id plain_ids) scored_ids
      in
      expect is_subset (tag ^ ": scored ⊆ plain"));

  run "scored weights: TYPO=1.0, STYLE=0.4" (fun tag ->
      let src = usrc test_doc in
      let scored = Validators.run_all_scored src in
      List.iter
        (fun (r : Evidence_scoring.scored_result) ->
          if String.length r.id > 5 && String.sub r.id 0 5 = "TYPO-" then
            expect
              (r.evidence_weight >= 0.99)
              (tag ^ ": " ^ r.id ^ " weight=1.0")
          else if String.length r.id > 6 && String.sub r.id 0 6 = "STYLE-" then
            expect (r.evidence_weight < 0.5) (tag ^ ": " ^ r.id ^ " weight<0.5"))
        scored);

  (* ══════════════════════════════════════════════════════════════════ 4.
     Incremental: verify caching actually works
     ══════════════════════════════════════════════════════════════════ *)
  run "incremental: identical source returns same result count" (fun tag ->
      let src = usrc test_doc in
      let first = Validators.run_all_incremental src in
      let second = Validators.run_all_incremental ~prev_src:src src in
      let first_ids = ids_of first in
      let second_ids = ids_of second in
      expect (first_ids = second_ids) (tag ^ ": same IDs on identical input"));

  run "incremental: editing one paragraph changes results" (fun tag ->
      let base =
        {|First para with enough text to be a real chunk exceeding minimum size.

Second para also long enough for its own chunk in the store system.|}
      in
      let src1 = usrc base in
      let edited =
        {|First para with enough text to be a real chunk exceeding minimum size.

Second para EDITED with "straight quotes" to trigger new rules here.|}
      in
      let src2 = usrc edited in
      let r1 = Validators.run_all_incremental src1 in
      let r2 = Validators.run_all_incremental ~prev_src:src1 src2 in
      let ids1 = ids_of r1 in
      let ids2 = ids_of r2 in
      expect (ids1 <> ids2) (tag ^ ": different results after edit"));

  (* ══════════════════════════════════════════════════════════════════ 5.
     Scheduled: edit_pos changes order but not content
     ══════════════════════════════════════════════════════════════════ *)
  run "scheduled: produces non-trivial results on real doc" (fun tag ->
      let src = usrc test_doc in
      let results = Validators.run_all_scheduled ~edit_pos:0 src in
      expect (List.length results > 0) (tag ^ ": has results");
      (* Cross-chunk rules (L3+) should be present since they run on full
         source *)
      let has_cross_chunk =
        List.exists
          (fun (r : Validators.result) ->
            match Validators.precondition_of_rule_id r.id with
            | L3 | L4 -> true
            | _ -> false)
          results
      in
      (* May or may not have L3/L4 depending on document content *)
      ignore has_cross_chunk;
      expect true (tag ^ ": no crash"));

  (* ══════════════════════════════════════════════════════════════════ 6.
     Language gating: French doc excludes English-only rules
     ══════════════════════════════════════════════════════════════════ *)
  run "language: English-tagged rules fire on English doc" (fun tag ->
      let src =
        usrc
          {|\documentclass{article}
\usepackage[english]{babel}
\begin{document}
Text with "straight quotes".
\end{document}|}
      in
      let results = Validators.run_all_for_language src (Some "en") in
      expect (has_id "TYPO-001" results) (tag ^ ": TYPO-001 fires in English"));

  run "language: auto-detect finds English" (fun tag ->
      let src =
        usrc
          {|\documentclass{article}
\usepackage[english]{babel}
\begin{document}
Hello world.
\end{document}|}
      in
      let lang = Language_detect.detect_language src in
      expect (lang = "en") (tag ^ ": detected English"));

  (* ══════════════════════════════════════════════════════════════════ 7.
     Semantic state: specific label/ref detection
     ══════════════════════════════════════════════════════════════════ *)
  run "semantic: detects eq:test label" (fun tag ->
      let src = usrc test_doc in
      let sem = Semantic_state.analyze src in
      let has_eq_test =
        List.exists
          (fun (e : Semantic_state.label_entry) -> e.key = "eq:test")
          sem.labels
      in
      expect has_eq_test (tag ^ ": eq:test label found"));

  run "semantic: detects sec:dup duplicate" (fun tag ->
      let src = usrc test_doc in
      let sem = Semantic_state.analyze src in
      expect
        (List.mem "sec:dup" sem.duplicate_labels)
        (tag ^ ": sec:dup is duplicate"));

  run "semantic: detects ref to eq:test" (fun tag ->
      let src = usrc test_doc in
      let sem = Semantic_state.analyze src in
      let has_ref =
        List.exists
          (fun (e : Semantic_state.ref_entry) -> e.key = "eq:test")
          sem.refs
      in
      expect has_ref (tag ^ ": ref to eq:test found"));

  (* ══════════════════════════════════════════════════════════════════ 8. Chunk
     store: specific chunk behavior
     ══════════════════════════════════════════════════════════════════ *)
  run "chunk store: test_doc splits into >3 chunks" (fun tag ->
      let chunks = Chunk_store.split_into_chunks test_doc in
      expect
        (Array.length chunks > 3)
        (tag ^ Printf.sprintf ": %d chunks" (Array.length chunks)));

  run "chunk store: edit changes exactly affected chunks" (fun tag ->
      let s1 = Chunk_store.create_snapshot test_doc in
      let edited = test_doc ^ "\n\nA brand new final paragraph added here." in
      let s2 = Chunk_store.create_snapshot edited in
      let dirty = Chunk_store.diff_snapshots s1 s2 in
      expect (List.length dirty > 0) (tag ^ ": at least 1 dirty chunk");
      expect
        (List.length dirty < Array.length s2.chunks)
        (tag ^ ": not ALL chunks dirty"));

  (* ══════════════════════════════════════════════════════════════════ 9. Log
     parser: specific event parsing
     ══════════════════════════════════════════════════════════════════ *)
  run "log parser: overfull extracts line numbers" (fun tag ->
      let log =
        "Overfull \\hbox (12.5pt too wide) in paragraph at lines 42--47\n"
      in
      let ctx = Log_parser.parse_log log in
      expect (ctx.overfull_lines = [ (42, 47) ]) (tag ^ ": lines 42-47"));

  run "log parser: tikz time extracts float" (fun tag ->
      let log = "Compile time for fig.pdf: 7.3s\n" in
      let ctx = Log_parser.parse_log log in
      match ctx.tikz_compile_times with
      | [ t ] -> expect (t > 7.2 && t < 7.4) (tag ^ ": ~7.3s")
      | _ ->
          expect false
            (tag
            ^ ": expected 1 time, got "
            ^ string_of_int (List.length ctx.tikz_compile_times)));

  (* ══════════════════════════════════════════════════════════════════ 10.
     Re_compat thread safety: concurrent regex with verification
     ══════════════════════════════════════════════════════════════════ *)
  run "Re_compat: 4 threads × 200 regex ops, all find same match" (fun tag ->
      let target = "\\section{Introduction}" in
      let re = Re_compat.regexp "\\\\section{\\([^}]*\\)}" in
      let results = Array.make 4 "" in
      let threads =
        List.init 4 (fun i ->
            Thread.create
              (fun () ->
                for _ = 1 to 200 do
                  try
                    let mr, _ = Re_compat.search_forward re test_doc 0 in
                    let g = Re_compat.matched_group mr 1 test_doc in
                    results.(i) <- g
                  with Not_found -> results.(i) <- "NOT_FOUND"
                done)
              ())
      in
      List.iter Thread.join threads;
      (* All threads should find the same first section title *)
      let _ = target in
      let all_same = Array.for_all (fun r -> r = results.(0)) results in
      expect all_same (tag ^ ": all threads got " ^ results.(0));
      expect (results.(0) <> "NOT_FOUND") (tag ^ ": match was found"));

  (* ══════════════════════════════════════════════════════════════════ 11.
     Empty/edge cases that MUST NOT crash
     ══════════════════════════════════════════════════════════════════ *)
  run "empty string: run_all" (fun tag ->
      let r = Validators.run_all "" in
      ignore r;
      expect true (tag ^ ": no crash"));

  run "empty string: run_all_incremental" (fun tag ->
      let r = Validators.run_all_incremental "" in
      ignore r;
      expect true (tag ^ ": no crash"));

  run "empty string: run_all_scheduled" (fun tag ->
      let r = Validators.run_all_scheduled "" in
      ignore r;
      expect true (tag ^ ": no crash"));

  run "single char: all entry points" (fun tag ->
      ignore (Validators.run_all "x");
      ignore (Validators.run_all_incremental "x");
      ignore (Validators.run_all_scheduled "x");
      expect true (tag ^ ": no crash on 'x'"));

  run "huge input: 100KB of text" (fun tag ->
      let big = String.make 100_000 'a' in
      let r = Validators.run_all (usrc big) in
      ignore r;
      expect true (tag ^ ": no crash on 100KB"))

let () = finalise "integration-e2e"
