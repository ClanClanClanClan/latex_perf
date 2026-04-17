(** Tests for project_state: per-file analysis and global projection. *)

open Latex_parse_lib
open Test_helpers

let repo_root =
  let exe_dir = Filename.dirname Sys.argv.(0) in
  let candidates =
    [ Filename.concat exe_dir "../.."; "."; Filename.concat exe_dir "../../.." ]
  in
  try
    List.find
      (fun d ->
        Sys.file_exists (Filename.concat d "corpora/multi_file/main.tex"))
      candidates
  with Not_found -> "."

let corpus p = Filename.concat repo_root ("corpora/multi_file/" ^ p)

let () =
  run "build project state from graph" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let ps = Project_state.build g in
      expect (List.length ps.file_states >= 4) (tag ^ ": >= 4 file states"));

  run "global labels collected" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let ps = Project_state.build g in
      let label_keys = List.map fst ps.global_labels in
      expect (List.mem "main:top" label_keys) (tag ^ ": main:top");
      expect (List.mem "ch1:sec" label_keys) (tag ^ ": ch1:sec");
      expect (List.mem "ch2:fig" label_keys) (tag ^ ": ch2:fig");
      expect (List.mem "shared:eq" label_keys) (tag ^ ": shared:eq"));

  run "global refs collected" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let ps = Project_state.build g in
      let ref_keys = List.map fst ps.global_refs in
      expect (List.mem "ch1:sec" ref_keys) (tag ^ ": ch1:sec ref");
      expect (List.mem "ch2:fig" ref_keys) (tag ^ ": ch2:fig ref"));

  run "cross-file undefined ref detected" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let ps = Project_state.build g in
      let undef_keys = List.map fst ps.cross_file_undefined in
      expect (List.mem "undefined:x" undef_keys) (tag ^ ": undefined:x"));

  run "no false cross-file duplicates" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let ps = Project_state.build g in
      expect (ps.cross_file_duplicates = []) (tag ^ ": no duplicates"));

  run "project context set/get/clear" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let ps = Project_state.build g in
      Project_context.set ps;
      let has = Project_context.get () <> None in
      Project_context.clear ();
      let no = Project_context.get () = None in
      expect has (tag ^ ": context set");
      expect no (tag ^ ": context cleared"));

  run "PRJ validators silent without context" (fun tag ->
      Project_context.clear ();
      let results = Validators.run_all "\\documentclass{article}" in
      let has_prj =
        List.exists
          (fun (r : Validators.result) ->
            String.length r.id >= 3 && String.sub r.id 0 3 = "PRJ")
          results
      in
      expect (not has_prj) (tag ^ ": no PRJ in single-file mode"));

  run "PRJ-003 fires with project context" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let ps = Project_state.build g in
      Project_context.set ps;
      Fun.protect ~finally:Project_context.clear (fun () ->
          (* Use unique source to avoid cache hit from previous test *)
          let src =
            "\\documentclass{article}\n% PRJ-003 test "
            ^ string_of_int (Random.int 999999)
          in
          let results = Validators.run_all src in
          let has_003 =
            List.exists
              (fun (r : Validators.result) -> r.id = "PRJ-003")
              results
          in
          expect has_003 (tag ^ ": PRJ-003 fires")))

let () = finalise "project-state"
