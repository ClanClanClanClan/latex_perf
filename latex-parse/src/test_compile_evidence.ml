(** Differential + mirror-equivalence tests for [Compile_evidence].

    Two claims are exercised:

    1. EXTRACTOR FAITHFULNESS — on real .tex documents the extractor identifies
    a duplicate \label (T4 violation) and a required-but-unsupported feature (T3
    violation), and accepts a clean document.

    2. EXTRACTED-CHECKER EQUIVALENCE — [Compile_evidence.project_wf_dec] now
    EXECUTES the Coq-EXTRACTED [CompileGuaranteeBridge.project_wf_dec] (module
    [Compile_guarantee_extracted]). We check it returns the SAME boolean as the
    Coq [Example]s ([project_wf_dec_true_clean], [project_wf_dec_false_dup],
    [project_wf_dec_false_otf], [project_wf_dec_true_otf_on_xe], each proved by
    [vm_compute]) on the shared abstract projects — a sanity replay over the
    extracted function itself, and additionally that the runtime wrapper and the
    raw extracted module agree (no mirror in between). *)

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

  (* ── (3) The runtime wrapper IS the extracted checker (no mirror) ── The
     runtime [CE.project_wf_dec] is a thin type-conversion around the
     Coq-extracted [Compile_guarantee_extracted.project_wf_dec]; call the raw
     extracted module directly on the same witnesses and require agreement, and
     the same true/false verdicts as the Coq [Example]s. *)
  let module Ext = Compile_guarantee_extracted in
  let ext_clean : Ext.pdflatex_project =
    {
      Ext.proj_graph =
        {
          Ext.bg_nodes = [ { Ext.n_file = 0; n_kind = Ext.Tex } ];
          bg_edges = [];
        };
      proj_body = [ Ext.BT_label_def 5; Ext.BT_label_ref 5 ];
    }
  in
  let ext_dup : Ext.pdflatex_project =
    {
      ext_clean with
      Ext.proj_body = [ Ext.BT_label_def 5; Ext.BT_label_def 5 ];
    }
  in
  let ext_otf : Ext.pdflatex_project =
    {
      ext_clean with
      Ext.proj_body = [ Ext.BT_needs_feature Ext.Opentype_fonts ];
    }
  in
  let ext_order = [ { Ext.n_file = 0; Ext.n_kind = Ext.Tex } ] in
  let ext_pf_ok : Ext.pdflatex_profile =
    { Ext.prof_engine = Ext.Pdflatex; prof_features = [] }
  in
  let ext_pf_xe : Ext.pdflatex_profile =
    { Ext.prof_engine = Ext.Xelatex; prof_features = [] }
  in
  run "extracted: raw project_wf_dec matches Coq Examples" (fun tag ->
      expect
        (Ext.project_wf_dec ext_clean ext_pf_ok ext_order = true
        && Ext.project_wf_dec ext_dup ext_pf_ok ext_order = false
        && Ext.project_wf_dec ext_otf ext_pf_ok ext_order = false
        && Ext.project_wf_dec ext_otf ext_pf_xe ext_order = true)
        (tag ^ ": extracted checker reproduces the four Coq vm_compute verdicts"));

  run "extracted: runtime wrapper agrees with raw extracted checker" (fun tag ->
      expect
        (CE.project_wf_dec p_clean pf_ok clean_order
         = Ext.project_wf_dec ext_clean ext_pf_ok ext_order
        && CE.project_wf_dec p_dup pf_ok clean_order
           = Ext.project_wf_dec ext_dup ext_pf_ok ext_order
        && CE.project_wf_dec p_otf pf_ok clean_order
           = Ext.project_wf_dec ext_otf ext_pf_ok ext_order
        && CE.project_wf_dec p_otf pf_xe clean_order
           = Ext.project_wf_dec ext_otf ext_pf_xe ext_order)
        (tag ^ ": no mirror — wrapper == extracted verdict"));

  finalise "compile-evidence"
