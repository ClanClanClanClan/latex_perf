(** Unit tests for [Compile_contract]. *)

open Latex_parse_lib
open Test_helpers

let tmp_dir =
  let d = Filename.temp_file "test_compile_contract_" "" in
  Sys.remove d;
  Unix.mkdir d 0o755;
  d

let write_file name content =
  let path = Filename.concat tmp_dir name in
  let oc = open_out path in
  output_string oc content;
  close_out oc;
  path

let cleanup_dir () =
  Array.iter
    (fun f -> try Sys.remove (Filename.concat tmp_dir f) with _ -> ())
    (Sys.readdir tmp_dir);
  try Unix.rmdir tmp_dir with _ -> ()

let mk_profile ~tex_path =
  Build_profile.create ~tex_path ~base_dir:(Filename.dirname tex_path)

let () =
  (* Happy path: minimal project, default profile, no declared features *)
  run "Ready on minimal valid project" (fun tag ->
      let path = write_file "ok.tex" "\\documentclass{article}\n" in
      match Project_model.of_root path with
      | Error _ -> expect false (tag ^ ": setup failed")
      | Ok proj -> (
          let profile = mk_profile ~tex_path:path in
          match Compile_contract.check_ready_to_compile proj profile with
          | Compile_contract.Ready -> expect true (tag ^ ": Ready")
          | NotReady rs ->
              expect false
                (tag
                ^ ": unexpected NotReady: "
                ^ String.concat "; "
                    (List.map Compile_contract.reason_to_string rs))));

  (* T3: declaring opentype_fonts on pdflatex should fail *)
  run "T3 catches opentype on pdflatex" (fun tag ->
      let path = write_file "bad_font.tex" "\\documentclass{article}\n" in
      match
        Project_model.of_root
          ~declared_features:[ Project_model.Opentype_fonts ]
          path
      with
      | Error _ -> expect false (tag ^ ": setup failed")
      | Ok proj -> (
          let profile = mk_profile ~tex_path:path in
          match Compile_contract.check_ready_to_compile proj profile with
          | NotReady rs ->
              let has_t3 =
                List.exists
                  (function
                    | Compile_contract.T3_profile_incompatible _ -> true
                    | _ -> false)
                  rs
              in
              expect has_t3 (tag ^ ": T3 reason present")
          | Ready -> expect false (tag ^ ": should reject")));

  (* T3: opentype_fonts on xelatex should pass *)
  run "T3 accepts opentype on xelatex" (fun tag ->
      let path = write_file "ok_xe.tex" "\\documentclass{article}\n" in
      match
        Project_model.of_root ~engine:Project_model.Xelatex
          ~declared_features:[ Project_model.Opentype_fonts ]
          path
      with
      | Error _ -> expect false (tag ^ ": setup failed")
      | Ok proj -> (
          let profile = mk_profile ~tex_path:path in
          match Compile_contract.check_ready_to_compile proj profile with
          | Ready -> expect true (tag ^ ": Ready on xelatex+opentype")
          | NotReady _ -> expect false (tag ^ ": should pass")));

  (* T3: lua_scripting on pdflatex fails *)
  run "T3 catches lua_scripting on pdflatex" (fun tag ->
      let path = write_file "bad_lua.tex" "\\documentclass{article}\n" in
      match
        Project_model.of_root
          ~declared_features:[ Project_model.Lua_scripting ]
          path
      with
      | Error _ -> expect false (tag ^ ": setup failed")
      | Ok proj -> (
          let profile = mk_profile ~tex_path:path in
          match Compile_contract.check_ready_to_compile proj profile with
          | NotReady _ -> expect true (tag ^ ": rejected")
          | Ready -> expect false (tag ^ ": should reject")));

  (* T2: missing include file *)
  run "T2 catches missing include" (fun tag ->
      let path =
        write_file "missing_inc.tex"
          "\\documentclass{article}\n\\input{never_exists}\n"
      in
      match Project_model.of_root path with
      | Error _ -> expect false (tag ^ ": setup failed")
      | Ok proj -> (
          let profile = mk_profile ~tex_path:path in
          match Compile_contract.check_ready_to_compile proj profile with
          | NotReady rs ->
              let has_t2 =
                List.exists
                  (function
                    | Compile_contract.T2_project_not_closed _ -> true
                    | _ -> false)
                  rs
              in
              expect has_t2 (tag ^ ": T2 reason present")
          | Ready -> expect false (tag ^ ": should reject")));

  (* T4: aux_path with duplicate labels *)
  run "T4 catches duplicate labels in aux" (fun tag ->
      let tex_path = write_file "dup.tex" "\\documentclass{article}\n" in
      let aux_path =
        write_file "dup.aux"
          {|\newlabel{foo}{{1}{1}{X}{y}{}}
\newlabel{foo}{{2}{2}{Y}{z}{}}
|}
      in
      match Project_model.of_root tex_path with
      | Error _ -> expect false (tag ^ ": setup failed")
      | Ok proj -> (
          let profile = mk_profile ~tex_path in
          match
            Compile_contract.check_ready_to_compile ~aux_path proj profile
          with
          | NotReady rs ->
              let has_t4 =
                List.exists
                  (function
                    | Compile_contract.T4_semantic_incoherent
                        (`Duplicate_labels _) ->
                        true
                    | _ -> false)
                  rs
              in
              expect has_t4 (tag ^ ": T4 duplicate-labels caught")
          | Ready -> expect false (tag ^ ": should reject")));

  (* reason_to_string sanity *)
  run "reason_to_string is informative" (fun tag ->
      let r =
        Compile_contract.T3_profile_incompatible
          { feature = "lua_scripting"; profile = "pdflatex" }
      in
      let s = Compile_contract.reason_to_string r in
      let contains sub =
        let ls = String.length s and lsub = String.length sub in
        let rec go i =
          if i + lsub > ls then false
          else if String.sub s i lsub = sub then true
          else go (i + 1)
        in
        go 0
      in
      expect (contains "T3") (tag ^ ": mentions T3");
      expect (contains "lua_scripting") (tag ^ ": mentions feature"));

  (* ── T0/T5 de-stub tests (v27.1.52) ────────────────────────────── *)
  let has_reason pred rs = List.exists pred rs in
  let is_t0 = function
    | Compile_contract.T0_parse_fails _ -> true
    | _ -> false
  in
  let is_t5 = function
    | Compile_contract.T5_rule_violations _ -> true
    | _ -> false
  in
  let check ~name ~content ?source expect_ready extra =
    run name (fun tag ->
        let path = write_file (name ^ ".tex") content in
        match Project_model.of_root path with
        | Error _ -> expect false (tag ^ ": setup failed")
        | Ok proj -> (
            let profile = mk_profile ~tex_path:path in
            let result =
              Compile_contract.check_ready_to_compile ?source proj profile
            in
            match (result, expect_ready) with
            | Compile_contract.Ready, true -> expect true (tag ^ ": Ready")
            | Ready, false ->
                expect false (tag ^ ": expected NOT-READY but got Ready")
            | NotReady rs, false -> extra tag rs
            | NotReady rs, true ->
                expect false
                  (tag
                  ^ ": expected Ready but got NotReady: "
                  ^ String.concat "; "
                      (List.map Compile_contract.reason_to_string rs))))
  in

  (* READY for a clean LP-Core document (T0 + T5 genuinely pass). *)
  check ~name:"cc_clean"
    ~content:
      "\\documentclass{article}\n\\begin{document}\nHello.\n\\end{document}\n"
    true (fun _ _ -> ());

  (* NOT-READY for an unbalanced brace: the L2 parser does NOT flag this, so it
     must be caught by T5 (DELIM-001), proving T5 actually runs the
     validators. *)
  check ~name:"cc_brace"
    ~content:
      "\\documentclass{article}\n\
       \\begin{document}\n\
       \\textbf{hello\n\
       \\end{document}\n" false (fun tag rs ->
      expect (has_reason is_t5 rs) (tag ^ ": T5 flags unbalanced brace"));

  (* NOT-READY for a genuine parse failure (unclosed inline math): caught by T0,
     proving T0 actually runs Parser_l2. *)
  check ~name:"cc_math"
    ~content:
      "\\documentclass{article}\n\\begin{document}\n$x = 1\n\\end{document}\n"
    false (fun tag rs ->
      expect (has_reason is_t0 rs) (tag ^ ": T0 flags unclosed math"));

  (* NOT-READY for an LP-Foreign construct (\write18 shell-escape): caught by T0
     via the language-profile gate. *)
  check ~name:"cc_foreign"
    ~content:
      "\\documentclass{article}\n\
       \\begin{document}\n\
       \\write18{rm -rf /}\n\
       \\end{document}\n" false (fun tag rs ->
      expect (has_reason is_t0 rs) (tag ^ ": T0 flags LP-Foreign construct"));

  (* Stubbed-Ready regression guard: if T0/T5 ever silently regress to no-ops,
     BOTH the brace doc and the foreign doc would spuriously report Ready.
     Assert directly on the ~source path (bypassing disk) that they do not. *)
  run "cc_regression T0/T5 are not no-op stubs" (fun tag ->
      let path = write_file "cc_reg.tex" "\\documentclass{article}\n" in
      match Project_model.of_root path with
      | Error _ -> expect false (tag ^ ": setup failed")
      | Ok proj -> (
          let profile = mk_profile ~tex_path:path in
          let foreign_src =
            "\\documentclass{article}\n\\immediate\\write18{ls}\n"
          in
          let brace_src = "\\documentclass{article}\n\\textbf{oops\n" in
          let r_foreign =
            Compile_contract.check_ready_to_compile ~source:foreign_src proj
              profile
          in
          let r_brace =
            Compile_contract.check_ready_to_compile ~source:brace_src proj
              profile
          in
          (match r_foreign with
          | Compile_contract.NotReady rs ->
              expect (has_reason is_t0 rs)
                (tag ^ ": T0 not a stub (foreign rejected)")
          | Ready ->
              expect false (tag ^ ": T0 REGRESSED to a stub (foreign->Ready)"));
          match r_brace with
          | Compile_contract.NotReady rs ->
              expect (has_reason is_t5 rs)
                (tag ^ ": T5 not a stub (brace rejected)")
          | Ready ->
              expect false (tag ^ ": T5 REGRESSED to a stub (brace->Ready)")));

  (* SINGLE-SOURCE guard (v27.1.60 audit hardening): t5_check / t5_check_fast
     must classify compile-blocking ids via [Validators.is_compile_blocking],
     the single source of truth — NOT a private duplicate that would make a
     future id-level promotion a silent no-op. We can only observe the predicate
     indirectly (the local was deleted), so we assert
     [Validators.is_compile_blocking] itself behaves as the contract requires
     over a representative sample that includes an id-level (not merely
     prefix-level) entry. *)
  run "is_compile_blocking single-source agreement" (fun tag ->
      let sample =
        [
          (* prefix-level compile-blocking families *)
          ("DELIM-001", true);
          ("ENC-004", true);
          ("PRT-001", true);
          (* an id-level entry: a specific DELIM id is still blocking because it
             shares the family prefix — the predicate is prefix-driven today,
             and this pins that any Validators change stays visible here. *)
          ("DELIM-010", true);
          (* non-blocking: completeness/style faults pdflatex compiles
             through *)
          ("DOC-001", false);
          ("TYPO-001", false);
          ("MATH-014", false);
          ("STYLE-023", false);
        ]
      in
      List.iter
        (fun (id, want) ->
          expect
            (Validators.is_compile_blocking id = want)
            (tag ^ ": is_compile_blocking " ^ id))
        sample);

  cleanup_dir ();
  finalise "compile-contract"
