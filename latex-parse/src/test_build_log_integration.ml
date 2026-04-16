(** Tests for WS1 compile-log integration.

    Exercises Class C execution path isolation, build profiles, execution
    classes, execution policies, and log-coupled rule activation. *)

open Latex_parse_lib
open Test_helpers

(* ── Helpers ─────────────────────────────────────────────────────── *)

let class_c_ids =
  List.map (fun (r : Validators.rule) -> r.id) Validators.rules_class_c

let is_class_c id = List.mem id class_c_ids

let with_log_context log_text f =
  let ctx = Log_parser.parse_log log_text in
  Log_parser.set_log_context ctx;
  Fun.protect ~finally:Log_parser.clear_log_context f

let find_result id results =
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let overfull_log =
  "Overfull \\hbox (3.5pt too wide) in paragraph at lines 10--12\n\
   []\n\
   [1] [2] [3]\n"

let mixed_log =
  "Overfull \\hbox (5.2pt too wide) in paragraph at lines 42--48\n\
   Overfull \\hbox (12.8pt too wide) in paragraph at lines 100--105\n\
   Underfull \\hbox (badness 10000) in paragraph at lines 55\n\
   Underfull \\vbox (badness 5000)\n\
   Widow penalty 150\n\
   Club penalty 150\n\
   LaTeX Warning: Float too large for page by 2.5pt on input line 73\n\
   [1] [2] [3] [4] [5]\n"

let src_minimal =
  "\\documentclass{article}\n\\begin{document}\nHello.\n\\end{document}\n"

(* Resolve repo root from build sandbox, same approach as test_golden_corpus *)
let repo_root =
  let exe_dir = Filename.dirname Sys.argv.(0) in
  let candidates =
    [
      Filename.concat exe_dir "../..";
      ".";
      Filename.concat exe_dir "../../..";
      Filename.concat exe_dir "../../../..";
    ]
  in
  try
    List.find
      (fun d ->
        Sys.file_exists
          (Filename.concat d "corpora/build_logs/overfull_basic.log"))
      candidates
  with Not_found -> "."

let corpus_log name = Filename.concat repo_root ("corpora/build_logs/" ^ name)

(* ── Execution class tests ───────────────────────────────────────── *)

let () =
  run "Execution_class.classify LAY-001 = C" (fun tag ->
      expect
        (Execution_class.classify "LAY-001" = Execution_class.C)
        (tag ^ ": is C"));

  run "Execution_class.classify MATH-026 = C" (fun tag ->
      expect
        (Execution_class.classify "MATH-026" = Execution_class.C)
        (tag ^ ": is C"));

  run "Execution_class.classify FIG-020 = C" (fun tag ->
      expect
        (Execution_class.classify "FIG-020" = Execution_class.C)
        (tag ^ ": is C"));

  run "Execution_class.classify TYPO-001 = A" (fun tag ->
      expect
        (Execution_class.classify "TYPO-001" = Execution_class.A)
        (tag ^ ": is A"));

  run "Execution_class.is_keystroke_safe A = true" (fun tag ->
      expect
        (Execution_class.is_keystroke_safe Execution_class.A)
        (tag ^ ": safe"));

  run "Execution_class.is_keystroke_safe C = false" (fun tag ->
      expect
        (not (Execution_class.is_keystroke_safe Execution_class.C))
        (tag ^ ": not safe"));

  (* ── Execution policy tests ────────────────────────────────────── *)
  run "default policy allows A, disallows C" (fun tag ->
      expect
        (Execution_policy.allows Execution_policy.default Execution_class.A)
        (tag ^ ": A allowed");
      expect
        (not
           (Execution_policy.allows Execution_policy.default Execution_class.C))
        (tag ^ ": C disallowed"));

  run "with_build policy allows A and C" (fun tag ->
      expect
        (Execution_policy.allows Execution_policy.with_build Execution_class.A)
        (tag ^ ": A allowed");
      expect
        (Execution_policy.allows Execution_policy.with_build Execution_class.C)
        (tag ^ ": C allowed"));

  (* ── Isolation tests ───────────────────────────────────────────── *)
  run "run_all excludes Class C rules (no log context)" (fun tag ->
      let results = Validators.run_all src_minimal in
      let has_c =
        List.exists (fun (r : Validators.result) -> is_class_c r.id) results
      in
      expect (not has_c) (tag ^ ": no Class C in run_all"));

  run "run_all excludes Class C rules (even with log context set)" (fun tag ->
      with_log_context mixed_log (fun () ->
          let results = Validators.run_all src_minimal in
          let has_c =
            List.exists (fun (r : Validators.result) -> is_class_c r.id) results
          in
          expect (not has_c) (tag ^ ": still no Class C in run_all")));

  (* ── Activation tests ───────────────────────────────────────────── *)
  run "run_class_c returns [] without log context" (fun tag ->
      Log_parser.clear_log_context ();
      let results = Validators.run_class_c src_minimal in
      expect (results = []) (tag ^ ": empty"));

  run "run_class_c returns results with overfull log" (fun tag ->
      with_log_context overfull_log (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect (results <> []) (tag ^ ": non-empty")));

  run "run_with_build includes both A/B and C results" (fun tag ->
      with_log_context overfull_log (fun () ->
          let results = Validators.run_with_build src_minimal in
          let has_ab =
            List.exists
              (fun (r : Validators.result) -> not (is_class_c r.id))
              results
          in
          let has_c =
            List.exists (fun (r : Validators.result) -> is_class_c r.id) results
          in
          expect has_ab (tag ^ ": has A/B results");
          expect has_c (tag ^ ": has C results")));

  run "run_with_policy default excludes C" (fun tag ->
      with_log_context overfull_log (fun () ->
          let results =
            Validators.run_with_policy Execution_policy.default src_minimal
          in
          let has_c =
            List.exists (fun (r : Validators.result) -> is_class_c r.id) results
          in
          expect (not has_c) (tag ^ ": no C in default")));

  run "run_with_policy with_build includes C" (fun tag ->
      with_log_context overfull_log (fun () ->
          let results =
            Validators.run_with_policy Execution_policy.with_build src_minimal
          in
          let has_c =
            List.exists (fun (r : Validators.result) -> is_class_c r.id) results
          in
          expect has_c (tag ^ ": has C in with_build")));

  (* ── Per-rule smoke tests ───────────────────────────────────────── *)
  run "LAY-001 fires on overfull > 2pt" (fun tag ->
      with_log_context overfull_log (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "LAY-001" results <> None)
            (tag ^ ": LAY-001 fires")));

  run "LAY-001 does not fire on clean log" (fun tag ->
      with_log_context "[1] [2]\n" (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "LAY-001" results = None)
            (tag ^ ": LAY-001 silent")));

  run "LAY-002 fires on widows" (fun tag ->
      with_log_context "Widow penalty 150\n" (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "LAY-002" results <> None)
            (tag ^ ": LAY-002 fires")));

  run "LAY-004 fires on large overflow" (fun tag ->
      with_log_context
        "Overfull \\hbox (12.8pt too wide) in paragraph at lines 1--2\n"
        (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "LAY-004" results <> None)
            (tag ^ ": LAY-004 fires")));

  run "LAY-006 fires on float warning" (fun tag ->
      with_log_context
        "LaTeX Warning: Float too large for page by 2.5pt on input line 73\n"
        (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "LAY-006" results <> None)
            (tag ^ ": LAY-006 fires")));

  run "LAY-009 fires on underfull vbox" (fun tag ->
      with_log_context "Underfull \\vbox (badness 5000)\n" (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "LAY-009" results <> None)
            (tag ^ ": LAY-009 fires")));

  run "LAY-018 fires on underfull vbox" (fun tag ->
      with_log_context "Underfull \\vbox (badness 3000)\n" (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "LAY-018" results <> None)
            (tag ^ ": LAY-018 fires")));

  run "MATH-026 fires on any overfull" (fun tag ->
      with_log_context
        "Overfull \\hbox (1.0pt too wide) in paragraph at lines 5--7\n"
        (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "MATH-026" results <> None)
            (tag ^ ": MATH-026 fires")));

  run "MATH-027 fires on large overflow" (fun tag ->
      with_log_context
        "Overfull \\hbox (6.0pt too wide) in paragraph at lines 5--7\n"
        (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "MATH-027" results <> None)
            (tag ^ ": MATH-027 fires")));

  run "FIG-020 fires on any overfull" (fun tag ->
      with_log_context
        "Overfull \\hbox (0.5pt too wide) in paragraph at lines 1--2\n"
        (fun () ->
          let results = Validators.run_class_c src_minimal in
          expect
            (find_result "FIG-020" results <> None)
            (tag ^ ": FIG-020 fires")));

  run "mixed log fires multiple rules" (fun tag ->
      with_log_context mixed_log (fun () ->
          let results = Validators.run_class_c src_minimal in
          let ids = List.map (fun (r : Validators.result) -> r.id) results in
          expect (List.mem "LAY-001" ids) (tag ^ ": LAY-001");
          expect (List.mem "LAY-002" ids) (tag ^ ": LAY-002");
          expect (List.mem "LAY-004" ids) (tag ^ ": LAY-004");
          expect (List.mem "LAY-006" ids) (tag ^ ": LAY-006")));

  (* ── Build profile tests ────────────────────────────────────────── *)
  run "Build_profile.create finds no log for nonexistent file" (fun tag ->
      let bp =
        Build_profile.create ~tex_path:"/tmp/nonexistent_test_file.tex"
          ~base_dir:"/tmp"
      in
      let bp = Build_profile.load_log bp in
      expect (not (Build_profile.has_log bp)) (tag ^ ": no log"));

  run "Build_profile.load_log_from loads corpus log" (fun tag ->
      let bp = Build_profile.create ~tex_path:"test.tex" ~base_dir:"." in
      let bp =
        Build_profile.load_log_from
          ~log_path:(corpus_log "overfull_basic.log")
          bp
      in
      expect (Build_profile.has_log bp) (tag ^ ": has log"));

  run "Build_profile detects pdflatex engine" (fun tag ->
      let bp = Build_profile.create ~tex_path:"test.tex" ~base_dir:"." in
      let bp =
        Build_profile.load_log_from
          ~log_path:(corpus_log "overfull_basic.log")
          bp
      in
      expect (bp.engine = Build_profile.PDFLaTeX) (tag ^ ": pdflatex detected"));

  (* ── Build artifact state tests ─────────────────────────────────── *)
  run "Build_artifact_state set/get/clear" (fun tag ->
      let bp = Build_profile.create ~tex_path:"test.tex" ~base_dir:"." in
      let bp =
        Build_profile.load_log_from
          ~log_path:(corpus_log "overfull_basic.log")
          bp
      in
      match Build_artifact_state.from_profile bp with
      | None -> expect false (tag ^ ": from_profile returned None")
      | Some state ->
          Build_artifact_state.set state;
          let has = Build_artifact_state.get () <> None in
          let has_log = Log_parser.get_log_context () <> None in
          Build_artifact_state.clear ();
          let no_state = Build_artifact_state.get () = None in
          let no_log = Log_parser.get_log_context () = None in
          expect has (tag ^ ": state set");
          expect has_log (tag ^ ": log context set");
          expect no_state (tag ^ ": state cleared");
          expect no_log (tag ^ ": log context cleared"));

  run "rules_class_c has exactly 13 rules" (fun tag ->
      expect (List.length Validators.rules_class_c = 13) (tag ^ ": 13 rules"))

let () = finalise "build-log-integration"
