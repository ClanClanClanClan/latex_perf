(** Tests for dependency_graph: graph building and affected set propagation. *)

open Latex_parse_lib
open Test_helpers

let mk_edge kind src dst =
  { Semantic_edges.kind; source_chunk = src; target_chunk = dst }

let () =
  run "transitive propagation: A→B→C" (fun tag ->
      let edges = [ mk_edge (LabelRef "x") 0 1; mk_edge (LabelRef "y") 1 2 ] in
      let g = Dependency_graph.build edges 3 in
      let affected = Dependency_graph.affected_set g [ 0 ] in
      expect (List.mem 0 affected) (tag ^ ": 0 in set");
      expect (List.mem 1 affected) (tag ^ ": 1 in set");
      expect (List.mem 2 affected) (tag ^ ": 2 in set"));

  run "no spurious propagation" (fun tag ->
      let edges = [ mk_edge (LabelRef "x") 1 2 ] in
      let g = Dependency_graph.build edges 3 in
      let affected = Dependency_graph.affected_set g [ 0 ] in
      expect (List.mem 0 affected) (tag ^ ": 0 in set");
      expect (not (List.mem 1 affected)) (tag ^ ": 1 not in set");
      expect (not (List.mem 2 affected)) (tag ^ ": 2 not in set"));

  run "empty graph: dirty set unchanged" (fun tag ->
      let g = Dependency_graph.build [] 5 in
      let affected = Dependency_graph.affected_set g [ 2; 3 ] in
      expect (List.length affected = 2) (tag ^ ": 2 affected");
      expect (List.mem 2 affected) (tag ^ ": 2 in set");
      expect (List.mem 3 affected) (tag ^ ": 3 in set"));

  run "full connectivity: all affected" (fun tag ->
      let edges =
        [
          mk_edge (LabelRef "a") 0 1;
          mk_edge (LabelRef "b") 1 2;
          mk_edge (LabelRef "c") 2 3;
          mk_edge (LabelRef "d") 3 4;
        ]
      in
      let g = Dependency_graph.build edges 5 in
      let affected = Dependency_graph.affected_set g [ 0 ] in
      expect (List.length affected = 5) (tag ^ ": all 5 affected"));

  run "diamond: no duplication" (fun tag ->
      let edges =
        [
          mk_edge (LabelRef "a") 0 1;
          mk_edge (LabelRef "b") 0 2;
          mk_edge (LabelRef "c") 1 3;
          mk_edge (LabelRef "d") 2 3;
        ]
      in
      let g = Dependency_graph.build edges 4 in
      let affected = Dependency_graph.affected_set g [ 0 ] in
      expect (List.length affected = 4) (tag ^ ": 4 unique"));

  run "isolated dirty chunk" (fun tag ->
      let edges = [ mk_edge (LabelRef "x") 2 3 ] in
      let g = Dependency_graph.build edges 5 in
      let affected = Dependency_graph.affected_set g [ 4 ] in
      expect (affected = [ 4 ]) (tag ^ ": only chunk 4"));

  run "multiple dirty seeds" (fun tag ->
      let edges = [ mk_edge (LabelRef "a") 0 2; mk_edge (LabelRef "b") 1 3 ] in
      let g = Dependency_graph.build edges 4 in
      let affected = Dependency_graph.affected_set g [ 0; 1 ] in
      expect (List.length affected = 4) (tag ^ ": all 4"))

let () = finalise "dependency-graph"
