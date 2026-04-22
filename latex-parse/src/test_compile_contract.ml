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

  cleanup_dir ();
  finalise "compile-contract"
