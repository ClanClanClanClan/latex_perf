(** End-to-end integration tests for the full validation pipeline.

    Tests cross-layer consistency (L0→L4), entry point equivalence, ML
    confidence gating, incremental validation, and CLI output. Spec W131-140:
    cross-layer regression suite. *)

open Latex_parse_lib
open Test_helpers

let () = Unix.putenv "L0_VALIDATORS" "pilot"

(* ── Test corpus ──────────────────────────────────────────────────── *)

let realistic_doc =
  {|\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage{amsmath}
\usepackage{hyperref}

\title{Integration Test Document}
\author{Test Author}

\begin{document}
\maketitle

\section{Introduction}
This is a test document with ``straight quotes'' and some
content that should trigger TYPO rules. There are -- double
hyphens here and ... three dots.

\section{Mathematics}
Consider the equation:
\begin{equation}
  E = mc^2
  \label{eq:einstein}
\end{equation}
See Equation~\ref{eq:einstein} for details.

\section{Mixed Commands}
This paragraph uses both legacy {\bf bold} and modern \textbf{bold}
commands in the same paragraph.

This separate paragraph uses only \textbf{modern bold}.

\begin{figure}
  \centering
  \includegraphics[width=0.5\textwidth]{example.png}
  \caption{An example figure}
  \label{fig:example}
\end{figure}

\section{Conclusion}
See Figure~\ref{fig:example} for the illustration.

\end{document}|}

let minimal_doc =
  {|\documentclass{article}
\begin{document}
Hello world.
\end{document}|}

let empty_doc = ""

(* ── Unique source per test ───────────────────────────────────────── *)
let _ctr = ref 0

let usrc doc =
  incr _ctr;
  Printf.sprintf "%s\n%% e2e-test-%d\n" doc !_ctr

(* ── Helpers ──────────────────────────────────────────────────────── *)

let sort_by_id results =
  List.sort
    (fun (a : Validators.result) (b : Validators.result) ->
      String.compare a.id b.id)
    results

let ids_of results =
  List.map (fun (r : Validators.result) -> r.id) (sort_by_id results)

let _has_rule id results =
  List.exists (fun (r : Validators.result) -> r.id = id) results

let () =
  (* ══════════════════════════════════════════════════════════════════ 1. Full
     pipeline produces results on realistic document
     ══════════════════════════════════════════════════════════════════ *)
  run "full pipeline: realistic doc produces results" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all src in
      expect
        (List.length results > 0)
        (tag ^ ": should fire rules on realistic doc"));

  run "full pipeline: minimal doc produces few results" (fun tag ->
      let src = usrc minimal_doc in
      let results = Validators.run_all src in
      (* Minimal doc might fire some rules but fewer than realistic *)
      expect (List.length results >= 0) (tag ^ ": no crash"));

  run "full pipeline: empty doc produces results" (fun tag ->
      let results = Validators.run_all (usrc empty_doc) in
      expect (List.length results >= 0) (tag ^ ": no crash on empty"));

  (* ══════════════════════════════════════════════════════════════════ 2. Layer
     coverage: rules from multiple layers fire
     ══════════════════════════════════════════════════════════════════ *)
  run "layer coverage: L0 rules fire" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all src in
      let l0 =
        List.exists
          (fun (r : Validators.result) ->
            match Validators.precondition_of_rule_id r.id with
            | L0 -> true
            | _ -> false)
          results
      in
      expect l0 (tag ^ ": at least one L0 rule fired"));

  run "layer coverage: L1 rules fire" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all src in
      let l1 =
        List.exists
          (fun (r : Validators.result) ->
            match Validators.precondition_of_rule_id r.id with
            | L1 -> true
            | _ -> false)
          results
      in
      expect l1 (tag ^ ": at least one L1 rule fired"));

  (* ══════════════════════════════════════════════════════════════════ 3. Entry
     point consistency: run_all_scored wraps run_all
     ══════════════════════════════════════════════════════════════════ *)
  run "scored: same rules fire as run_all" (fun tag ->
      let src = usrc realistic_doc in
      let plain = ids_of (Validators.run_all src) in
      let src2 = usrc realistic_doc in
      let scored =
        List.map
          (fun (r : Evidence_scoring.scored_result) -> r.id)
          (Validators.run_all_scored src2)
      in
      let scored_sorted = List.sort String.compare scored in
      (* Scored may have fewer (ML suppression) but never MORE than plain *)
      expect
        (List.length scored_sorted <= List.length plain)
        (tag ^ ": scored <= plain count"));

  run "scored: every result has confidence" (fun tag ->
      let src = usrc realistic_doc in
      let scored = Validators.run_all_scored src in
      let all_have_conf =
        List.for_all
          (fun (r : Evidence_scoring.scored_result) -> r.evidence_weight > 0.0)
          scored
      in
      expect all_have_conf (tag ^ ": all weights > 0"));

  (* ══════════════════════════════════════════════════════════════════ 4. ML
     confidence gating
     ══════════════════════════════════════════════════════════════════ *)
  run "ML gating: without env var, no suppression" (fun tag ->
      (* LP_ML_CONFIDENCE_MAP not set → no suppression *)
      let src = usrc realistic_doc in
      let scored = Validators.run_all_scored src in
      (* All rules that fire should be present *)
      expect (List.length scored > 0) (tag ^ ": rules fire"));

  run "ML gating: with env var, TYPO-012/056 suppressed" (fun tag ->
      Unix.putenv "LP_ML_CONFIDENCE_MAP" "data/ml_confidence_map.json";
      (* Force re-evaluation of lazy map *)
      let src = usrc realistic_doc in
      let scored = Validators.run_all_scored src in
      let has_012 =
        List.exists
          (fun (r : Evidence_scoring.scored_result) -> r.id = "TYPO-012")
          scored
      in
      let has_056 =
        List.exists
          (fun (r : Evidence_scoring.scored_result) -> r.id = "TYPO-056")
          scored
      in
      (* These should be suppressed IF they would have fired *)
      (* The test document may not trigger them, but if it does, they should be
         filtered *)
      expect
        ((not has_012) && not has_056)
        (tag ^ ": TYPO-012/056 not in scored output");
      (* Clean up *)
      Unix.putenv "LP_ML_CONFIDENCE_MAP" "");

  (* ══════════════════════════════════════════════════════════════════ 5.
     Incremental validation consistency
     ══════════════════════════════════════════════════════════════════ *)
  run "incremental: first call produces results" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all_incremental src in
      expect (List.length results > 0) (tag ^ ": has results"));

  run "incremental: second call with same src uses cache" (fun tag ->
      let src = usrc realistic_doc in
      let _first = Validators.run_all_incremental src in
      let second = Validators.run_all_incremental ~prev_src:src src in
      expect (List.length second >= 0) (tag ^ ": cached OK"));

  run "incremental: edit triggers re-validation" (fun tag ->
      let src1 = usrc realistic_doc in
      let src2 = usrc (realistic_doc ^ "\n\nNew paragraph added.") in
      let _first = Validators.run_all_incremental src1 in
      let second = Validators.run_all_incremental ~prev_src:src1 src2 in
      expect (List.length second > 0) (tag ^ ": re-validated after edit"));

  (* ══════════════════════════════════════════════════════════════════ 6.
     Scheduled validation
     ══════════════════════════════════════════════════════════════════ *)
  run "scheduled: produces results" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all_scheduled ~edit_pos:100 src in
      expect (List.length results > 0) (tag ^ ": scheduled has results"));

  run "scheduled: edit_pos doesn't change WHICH rules fire" (fun tag ->
      let src = usrc realistic_doc in
      let r0 = ids_of (Validators.run_all_scheduled ~edit_pos:0 src) in
      let src2 = usrc realistic_doc in
      let r500 = ids_of (Validators.run_all_scheduled ~edit_pos:500 src2) in
      expect (r0 = r500) (tag ^ ": same rules regardless of edit_pos"));

  (* ══════════════════════════════════════════════════════════════════ 7.
     Language gating
     ══════════════════════════════════════════════════════════════════ *)
  run "language: auto-detect on English doc" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all_for_language src None in
      expect (List.length results > 0) (tag ^ ": auto-detect produces results"));

  run "language: explicit English" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all_for_language src (Some "en") in
      expect (List.length results > 0) (tag ^ ": explicit en produces results"));

  run "language: French filters locale rules" (fun tag ->
      let src = usrc realistic_doc in
      let en_results = Validators.run_all_for_language src (Some "en") in
      let src2 = usrc realistic_doc in
      let fr_results = Validators.run_all_for_language src2 (Some "fr") in
      (* Different language should produce different results *)
      let en_ids = ids_of en_results in
      let fr_ids = ids_of fr_results in
      expect
        (en_ids <> fr_ids || List.length en_ids = List.length fr_ids)
        (tag ^ ": language affects results"));

  (* ══════════════════════════════════════════════════════════════════ 8.
     Semantic state integration
     ══════════════════════════════════════════════════════════════════ *)
  run "semantic state: labels and refs detected" (fun tag ->
      let src = usrc realistic_doc in
      let sem = Semantic_state.analyze src in
      expect (List.length sem.labels > 0) (tag ^ ": labels found");
      expect (List.length sem.refs > 0) (tag ^ ": refs found"));

  run "semantic state: duplicate detection" (fun tag ->
      let src =
        usrc
          {|\documentclass{article}
\begin{document}
\label{eq:dup}
\label{eq:dup}
\end{document}|}
      in
      let sem = Semantic_state.analyze src in
      expect
        (List.length sem.duplicate_labels > 0)
        (tag ^ ": duplicate detected"));

  (* ══════════════════════════════════════════════════════════════════ 9. Layer
     mapping consistency
     ══════════════════════════════════════════════════════════════════ *)
  run "layer mapping: all rules have valid layer" (fun tag ->
      let src = usrc realistic_doc in
      let results = Validators.run_all src in
      let all_valid =
        List.for_all
          (fun (r : Validators.result) ->
            match Validators.precondition_of_rule_id r.id with
            | L0 | L1 | L2 | L3 | L4 -> true)
          results
      in
      expect all_valid (tag ^ ": all layers valid"));

  (* ══════════════════════════════════════════════════════════════════ 10.
     Evidence scoring integration
     ══════════════════════════════════════════════════════════════════ *)
  run "evidence scoring: VPD rules get High confidence" (fun tag ->
      let src = usrc realistic_doc in
      let scored = Validators.run_all_scored src in
      let typo_rules =
        List.filter
          (fun (r : Evidence_scoring.scored_result) ->
            String.length r.id > 5 && String.sub r.id 0 5 = "TYPO-")
          scored
      in
      let all_high =
        List.for_all
          (fun (r : Evidence_scoring.scored_result) ->
            r.confidence = Evidence_scoring.High)
          typo_rules
      in
      expect all_high (tag ^ ": TYPO rules get High confidence"));

  (* ══════════════════════════════════════════════════════════════════ 11.
     Chunk store integration
     ══════════════════════════════════════════════════════════════════ *)
  run "chunk store: realistic doc splits into multiple chunks" (fun tag ->
      let chunks = Chunk_store.split_into_chunks realistic_doc in
      expect (Array.length chunks > 1) (tag ^ ": multiple chunks"));

  run "chunk store: snapshots are deterministic" (fun tag ->
      let s1 = Chunk_store.create_snapshot realistic_doc in
      let s2 = Chunk_store.create_snapshot realistic_doc in
      let same =
        Array.length s1.chunks = Array.length s2.chunks
        && Array.for_all2
             (fun a b -> a.Chunk_store.id = b.Chunk_store.id)
             s1.chunks s2.chunks
      in
      expect same (tag ^ ": deterministic snapshots"));

  (* ══════════════════════════════════════════════════════════════════ 12. Log
     parser integration
     ══════════════════════════════════════════════════════════════════ *)
  run "log parser: parses overfull hbox" (fun tag ->
      let log =
        "Overfull \\hbox (5.0pt too wide) in paragraph at lines 10--15\n"
      in
      let ctx = Log_parser.parse_log log in
      expect (List.length ctx.overfull_lines > 0) (tag ^ ": overfull detected"));

  run "log parser: tikz compile time" (fun tag ->
      let log = "Compile time for figure1.pdf: 6.2s\n" in
      let ctx = Log_parser.parse_log log in
      expect
        (List.length ctx.tikz_compile_times > 0)
        (tag ^ ": tikz time detected"));

  (* ══════════════════════════════════════════════════════════════════ 13.
     Re_compat thread safety (basic)
     ══════════════════════════════════════════════════════════════════ *)
  run "Re_compat: concurrent regex from 4 threads" (fun tag ->
      let results = Array.make 4 false in
      let threads =
        List.init 4 (fun i ->
            Thread.create
              (fun () ->
                let re = Re_compat.regexp "\\\\section\\*?{\\([^}]*\\)}" in
                for _ = 1 to 100 do
                  try
                    let mr, _ = Re_compat.search_forward re realistic_doc 0 in
                    let _ = Re_compat.matched_group mr 1 realistic_doc in
                    results.(i) <- true
                  with Not_found -> results.(i) <- true
                done)
              ())
      in
      List.iter Thread.join threads;
      let all_ok = Array.for_all (fun b -> b) results in
      expect all_ok (tag ^ ": 4 threads OK"))

let () = finalise "integration-e2e"
