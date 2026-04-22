(** Build-pipeline dependency graph. See [build_graph.mli]. *)

type node_id = int
type artefact_kind = Tex | Aux | Bbl | Bib | Pdf | Log
type node = { id : node_id; kind : artefact_kind; path : string; exists : bool }
type edge = { from_id : node_id; to_id : node_id; reason : string }
type t = { nodes : node list; edges : edge list }

let kind_to_string = function
  | Tex -> "tex"
  | Aux -> "aux"
  | Bbl -> "bbl"
  | Bib -> "bib"
  | Pdf -> "pdf"
  | Log -> "log"

(* Predict the artefact path from a .tex path. pdflatex places .aux, .log, .pdf
   next to the .tex by default. v26.2 doesn't track \jobname / -output-directory
   overrides — callers with custom output dirs should build their own graph. *)
let predict_path (tex_path : string) (k : artefact_kind) : string =
  let base = Filename.remove_extension tex_path in
  match k with
  | Tex -> tex_path
  | Aux -> base ^ ".aux"
  | Log -> base ^ ".log"
  | Pdf -> base ^ ".pdf"
  | Bbl -> base ^ ".bbl"
  | Bib -> base ^ ".bib" (* only used for isolated bib files *)

let of_project (proj : Project_model.t) : t =
  let next_id = ref 0 in
  let mk_id () =
    let i = !next_id in
    next_id := i + 1;
    i
  in
  let nodes = ref [] in
  let edges = ref [] in
  (* For each .tex in the project, add Tex and predicted Aux nodes and the
     tex→aux edge. The root .tex also gets a predicted .pdf node. *)
  List.iter
    (fun (f : Project_model.file_entry) ->
      let tex_id = mk_id () in
      let tex_node =
        {
          id = tex_id;
          kind = Tex;
          path = f.path;
          exists = Sys.file_exists f.path;
        }
      in
      nodes := tex_node :: !nodes;
      (* Each .tex predicts an .aux *)
      let aux_path = predict_path f.path Aux in
      let aux_id = mk_id () in
      let aux_node =
        {
          id = aux_id;
          kind = Aux;
          path = aux_path;
          exists = Sys.file_exists aux_path;
        }
      in
      nodes := aux_node :: !nodes;
      edges :=
        { from_id = tex_id; to_id = aux_id; reason = "pdflatex pass" } :: !edges;
      (* Root additionally predicts a .pdf *)
      if f.is_root then (
        let pdf_path = predict_path f.path Pdf in
        let pdf_id = mk_id () in
        let pdf_node =
          {
            id = pdf_id;
            kind = Pdf;
            path = pdf_path;
            exists = Sys.file_exists pdf_path;
          }
        in
        nodes := pdf_node :: !nodes;
        edges :=
          { from_id = tex_id; to_id = pdf_id; reason = "final pdflatex pass" }
          :: !edges))
    (Project_model.all_files proj);
  { nodes = List.rev !nodes; edges = List.rev !edges }

let nodes (t : t) : node list = t.nodes
let edges (t : t) : edge list = t.edges

let find_node (t : t) (id : node_id) : node option =
  List.find_opt (fun n -> n.id = id) t.nodes

let find_by_path (t : t) (path : string) : node option =
  List.find_opt (fun n -> n.path = path) t.nodes

(* DFS-based cycle detection. In the build graph this is always acyclic in
   well-formed projects (no build artefact circularly depends on itself). Here
   for completeness and as a T2 check. *)
let is_acyclic (t : t) : bool =
  let adj = Hashtbl.create 16 in
  List.iter (fun n -> Hashtbl.replace adj n.id []) t.nodes;
  List.iter
    (fun e ->
      let cur = try Hashtbl.find adj e.from_id with Not_found -> [] in
      Hashtbl.replace adj e.from_id (e.to_id :: cur))
    t.edges;
  let visiting = Hashtbl.create 16 in
  let visited = Hashtbl.create 16 in
  let rec dfs n =
    if Hashtbl.mem visiting n then false (* back edge *)
    else if Hashtbl.mem visited n then true
    else (
      Hashtbl.replace visiting n ();
      let ok =
        let succs = try Hashtbl.find adj n with Not_found -> [] in
        List.for_all dfs succs
      in
      Hashtbl.remove visiting n;
      Hashtbl.replace visited n ();
      ok)
  in
  List.for_all (fun n -> dfs n.id) t.nodes
