(** Differential + mirror-equivalence tests for [Compile_evidence].

    Two claims are exercised:

    1. EXTRACTOR FAITHFULNESS — on real .tex documents the extractor identifies
    a duplicate \label (T4 violation) and a required-but-unsupported feature (T3
    violation), and accepts a clean document.

    2. MIRROR-EQUIVALENCE — the OCaml [project_wf_dec] returns the SAME boolean
    as the Coq [CompileGuaranteeBridge.project_wf_dec] on the shared example
    projects. The Coq side proves these by [vm_compute] as [Example]s
    ([project_wf_dec_true_clean], [project_wf_dec_false_dup],
    [project_wf_dec_false_otf], [project_wf_dec_true_otf_on_xe]); we replay the
    SAME abstract projects here and check the OCaml mirror agrees. Since the
    checker is re-implemented (not Coq-extracted), this equivalence is TESTED,
    not proven. *)

open Latex_parse_lib
open Test_helpers
module CE = Compile_evidence

(* ── Shared example projects, mirroring PdflatexModel / CompileGuaranteeBridge
   witnesses byte-for-byte. ─────────────────────────────────────────────── *)

let root : CE.node = { CE.n_file = 0; n_kind = CE.Tex }
let clean_order = [ root ]
let pf_ok : CE.profile = { CE.prof_engine = CE.Pdflatex; prof_features = [] }
let pf_xe : CE.profile = { CE.prof_engine = CE.Xelatex; prof_features = [] }

(* p_clean: defines label 5, references it. *)
let p_clean : CE.project =
  {
    CE.proj_nodes = [ root ];
    proj_edges = [];
    proj_body = [ CE.BT_label_def 5; CE.BT_label_ref 5 ];
  }

(* p_dup: defines label 5 twice (T4 violation). *)
let p_dup : CE.project =
  {
    CE.proj_nodes = [ root ];
    proj_edges = [];
    proj_body = [ CE.BT_label_def 5; CE.BT_label_def 5 ];
  }

(* p_otf: body needs OpenType fonts. *)
let p_otf : CE.project =
  {
    CE.proj_nodes = [ root ];
    proj_edges = [];
    proj_body = [ CE.BT_needs_feature CE.Opentype_fonts ];
  }

let () =
  (* ── (1) Mirror-equivalence: OCaml checker == Coq vm_compute verdicts ── *)
  run "mirror: clean project accepted (Coq project_wf_dec_true_clean)"
    (fun tag ->
      expect
        (CE.project_wf_dec p_clean pf_ok clean_order = true)
        (tag ^ ": OCaml must agree with Coq = true"));

  run "mirror: duplicate label rejected (Coq project_wf_dec_false_dup)"
    (fun tag ->
      expect
        (CE.project_wf_dec p_dup pf_ok clean_order = false)
        (tag ^ ": OCaml must agree with Coq = false"));

  run "mirror: opentype on pdflatex rejected (Coq project_wf_dec_false_otf)"
    (fun tag ->
      expect
        (CE.project_wf_dec p_otf pf_ok clean_order = false)
        (tag ^ ": OCaml must agree with Coq = false"));

  run "mirror: opentype on xelatex accepted (Coq project_wf_dec_true_otf_on_xe)"
    (fun tag ->
      expect
        (CE.project_wf_dec p_otf pf_xe clean_order = true)
        (tag ^ ": OCaml must agree with Coq = true"));

  (* ── (2) Extractor faithfulness on REAL documents ── *)
  let clean_src =
    "\\documentclass{article}\n\
     \\begin{document}\n\
     \\section{Intro}\\label{sec:intro}\n\
     See \\ref{sec:intro}.\n\
     \\end{document}\n"
  in
  let dup_src =
    "\\documentclass{article}\n\
     \\begin{document}\n\
     \\section{A}\\label{sec:x}\n\
     \\section{B}\\label{sec:x}\n\
     \\end{document}\n"
  in
  let otf_src =
    "\\documentclass{article}\n\
     \\usepackage{fontspec}\n\
     \\setmainfont{Latin Modern Roman}\n\
     \\begin{document}\n\
     Hi.\n\
     \\end{document}\n"
  in

  run "extract: clean document => all premises hold" (fun tag ->
      let p, pf, order = CE.extract ~source:clean_src ~engine:CE.Pdflatex in
      let r = CE.report p pf order in
      expect (CE.all_hold r) (tag ^ ": clean must pass premise check"));

  run "extract: duplicate \\label => T4 fails, others hold" (fun tag ->
      let p, pf, order = CE.extract ~source:dup_src ~engine:CE.Pdflatex in
      let r = CE.report p pf order in
      expect
        ((not r.CE.t4_unique_labels)
        && r.CE.t2_closed
        && r.CE.t3_body
        && r.CE.t3_declared)
        (tag ^ ": exactly T4 must fail"));

  run "extract: duplicate \\label key surfaced" (fun tag ->
      expect
        (CE.duplicate_label_keys dup_src = [ "sec:x" ])
        (tag ^ ": duplicate key sec:x reported"));

  run "extract: fontspec on pdflatex => T3 body fails" (fun tag ->
      let p, pf, order = CE.extract ~source:otf_src ~engine:CE.Pdflatex in
      let r = CE.report p pf order in
      expect
        ((not r.CE.t3_body)
        && r.CE.unsupported_features = [ CE.Opentype_fonts ]
        && r.CE.t4_unique_labels)
        (tag ^ ": T3 body must fail on opentype+pdflatex"));

  run "extract: fontspec on xelatex => all premises hold" (fun tag ->
      let p, pf, order = CE.extract ~source:otf_src ~engine:CE.Xelatex in
      let r = CE.report p pf order in
      expect (CE.all_hold r) (tag ^ ": xelatex admits opentype"));

  (* Label id stability: def and ref of the SAME key hash identically. *)
  run "extract: label def/ref hash to the same id" (fun tag ->
      let p, _, _ = CE.extract ~source:clean_src ~engine:CE.Pdflatex in
      let defs = CE.body_label_defs p.CE.proj_body in
      let has_matching_ref =
        List.exists
          (function CE.BT_label_ref n -> List.mem n defs | _ -> false)
          p.CE.proj_body
      in
      expect
        (defs <> [] && has_matching_ref)
        (tag ^ ": ref of a defined label shares its id"));

  (* Determinism: extraction is a pure function of the source. *)
  run "extract: deterministic" (fun tag ->
      let a, _, _ = CE.extract ~source:dup_src ~engine:CE.Pdflatex in
      let b, _, _ = CE.extract ~source:dup_src ~engine:CE.Pdflatex in
      expect
        (a.CE.proj_body = b.CE.proj_body)
        (tag ^ ": same source => same body"));

  finalise "compile-evidence"
