(** Tests for project_graph: graph building and cycle detection. *)

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
  run "build graph from main.tex" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      expect (Project_graph.file_count g >= 4) (tag ^ ": >= 4 files");
      expect (Project_graph.is_acyclic g) (tag ^ ": acyclic"));

  run "root file is correct" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      expect (Filename.basename g.root = "main.tex") (tag ^ ": root=main.tex"));

  run "edges exist" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      expect (List.length g.edges >= 3) (tag ^ ": >= 3 edges"));

  run "shared.tex is reachable" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      let has_shared =
        List.exists (fun f -> Filename.basename f = "shared.tex") g.files
      in
      expect has_shared (tag ^ ": shared.tex in files"));

  run "cycle detection works" (fun tag ->
      let g = Project_graph.build ~root:(corpus "cycle_a.tex") in
      expect (not (Project_graph.is_acyclic g)) (tag ^ ": has cycle");
      expect (g.cycles <> []) (tag ^ ": cycle path reported"));

  run "single file graph" (fun tag ->
      let g = Project_graph.build ~root:(corpus "shared.tex") in
      expect (Project_graph.file_count g = 1) (tag ^ ": 1 file");
      expect (Project_graph.is_acyclic g) (tag ^ ": acyclic"));

  run "unresolved includes reported" (fun tag ->
      let g = Project_graph.build ~root:(corpus "main.tex") in
      (* main.tex includes chapter2 which has no further includes *)
      (* All includes should resolve for the main corpus *)
      expect (g.unresolved = []) (tag ^ ": no unresolved"))

let () = finalise "project-graph"
