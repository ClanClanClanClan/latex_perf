(** Tests for semantic_edges: label→ref and macro def→use edge extraction. *)

open Latex_parse_lib
open Test_helpers

let mk_chunks texts =
  Array.of_list
    (List.mapi
       (fun i content ->
         {
           Chunk_store.id = Int64.of_int i;
           start = 0;
           length = String.length content;
           content;
         })
       texts)

let () =
  run "label→ref edge across chunks" (fun tag ->
      let chunks =
        mk_chunks [ "\\label{eq:1}\nSome text."; "See \\ref{eq:1}." ]
      in
      let edges = Semantic_edges.extract_edges chunks in
      let has_lr =
        List.exists
          (fun e ->
            e.Semantic_edges.kind = LabelRef "eq:1"
            && e.source_chunk = 0
            && e.target_chunk = 1)
          edges
      in
      expect has_lr (tag ^ ": label→ref edge found"));

  run "label and ref in same chunk: no cross-chunk edge" (fun tag ->
      let chunks = mk_chunks [ "\\label{x} \\ref{x}" ] in
      let edges = Semantic_edges.extract_edges chunks in
      let cross =
        List.filter
          (fun e -> e.Semantic_edges.source_chunk <> e.target_chunk)
          edges
      in
      expect (cross = []) (tag ^ ": no cross-chunk edges"));

  run "multiple labels, multiple refs" (fun tag ->
      let chunks =
        mk_chunks
          [
            "\\label{a} \\label{b}"; "\\ref{a} \\ref{c}"; "\\label{c} \\ref{b}";
          ]
      in
      let edges = Semantic_edges.extract_edges chunks in
      let lr_edges =
        List.filter
          (fun e ->
            match e.Semantic_edges.kind with LabelRef _ -> true | _ -> false)
          edges
      in
      expect (List.length lr_edges >= 3) (tag ^ ": >= 3 label→ref edges"));

  run "eqref produces edge" (fun tag ->
      let chunks =
        mk_chunks [ "\\label{eq:2}\nFormula."; "See \\eqref{eq:2}." ]
      in
      let edges = Semantic_edges.extract_edges chunks in
      expect (edges <> []) (tag ^ ": eqref edge found"));

  run "autoref produces edge" (fun tag ->
      let chunks =
        mk_chunks [ "\\label{fig:1}\nFigure."; "See \\autoref{fig:1}." ]
      in
      let edges = Semantic_edges.extract_edges chunks in
      expect (edges <> []) (tag ^ ": autoref edge found"));

  run "newcommand def→use edge" (fun tag ->
      let chunks =
        mk_chunks [ "\\newcommand{\\myop}{stuff}"; "Use \\myop here." ]
      in
      let edges = Semantic_edges.extract_edges chunks in
      let has_macro =
        List.exists
          (fun e ->
            e.Semantic_edges.kind = MacroDef "myop"
            && e.source_chunk = 0
            && e.target_chunk = 1)
          edges
      in
      expect has_macro (tag ^ ": macro def→use edge found"));

  run "empty chunks: no edges" (fun tag ->
      let chunks = mk_chunks [ ""; "" ] in
      let edges = Semantic_edges.extract_edges chunks in
      expect (edges = []) (tag ^ ": no edges"));

  run "single chunk: no cross-chunk edges" (fun tag ->
      let chunks =
        mk_chunks [ "\\label{x} \\ref{x} \\newcommand{\\f}{y} \\f" ]
      in
      let edges = Semantic_edges.extract_edges chunks in
      let cross =
        List.filter
          (fun e -> e.Semantic_edges.source_chunk <> e.target_chunk)
          edges
      in
      expect (cross = []) (tag ^ ": no cross-chunk"));

  run "ref to undefined label: no edge" (fun tag ->
      let chunks = mk_chunks [ "text only"; "\\ref{nonexistent}" ] in
      let edges = Semantic_edges.extract_edges chunks in
      let lr =
        List.filter
          (fun e ->
            match e.Semantic_edges.kind with LabelRef _ -> true | _ -> false)
          edges
      in
      expect (lr = []) (tag ^ ": no edge for undefined label"))

let () = finalise "semantic-edges"
