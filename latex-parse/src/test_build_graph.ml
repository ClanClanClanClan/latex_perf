(** Unit tests for [Build_graph]. *)

open Latex_parse_lib
open Test_helpers

let tmp_dir =
  let d = Filename.temp_file "test_build_graph_" "" in
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

let () =
  let root = write_file "main.tex" "\\documentclass{article}\n" in
  let proj =
    match Project_model.of_root root with
    | Ok p -> p
    | Error _ -> failwith "setup failed"
  in
  let g = Build_graph.of_project proj in

  run "of_project produces nodes" (fun tag ->
      let ns = Build_graph.nodes g in
      expect (List.length ns >= 3) (tag ^ ": at least tex + aux + pdf nodes"));

  run "has a Tex node for root" (fun tag ->
      let ns = Build_graph.nodes g in
      let has_tex =
        List.exists (fun (n : Build_graph.node) -> n.kind = Build_graph.Tex) ns
      in
      expect has_tex (tag ^ ": Tex node present"));

  run "has an Aux node predicted" (fun tag ->
      let ns = Build_graph.nodes g in
      let has_aux =
        List.exists (fun (n : Build_graph.node) -> n.kind = Build_graph.Aux) ns
      in
      expect has_aux (tag ^ ": Aux node present"));

  run "has a Pdf node for root" (fun tag ->
      let ns = Build_graph.nodes g in
      let has_pdf =
        List.exists (fun (n : Build_graph.node) -> n.kind = Build_graph.Pdf) ns
      in
      expect has_pdf (tag ^ ": Pdf node present"));

  run "edges exist tex→aux and tex→pdf" (fun tag ->
      let es = Build_graph.edges g in
      expect (List.length es >= 2) (tag ^ ": at least 2 edges"));

  run "is_acyclic on fresh graph" (fun tag ->
      expect (Build_graph.is_acyclic g) (tag ^ ": should be acyclic"));

  run "find_by_path finds the root .tex" (fun tag ->
      match Build_graph.find_by_path g root with
      | Some n ->
          expect (n.kind = Build_graph.Tex) (tag ^ ": Tex kind");
          expect n.exists (tag ^ ": file exists")
      | None -> expect false (tag ^ ": should find the root"));

  run "kind_to_string" (fun tag ->
      expect (Build_graph.kind_to_string Build_graph.Aux = "aux") (tag ^ ": aux"));

  cleanup_dir ();
  finalise "build-graph"
