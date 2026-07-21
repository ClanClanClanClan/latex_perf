(** Compile-guarantee evidence extractor. See [compile_evidence.mli].

    Two halves: 1. An OCaml MIRROR of [CompileGuaranteeBridge.project_wf_dec]
    and the Coq data model — kept byte-for-byte faithful so the
    mirror-equivalence tests are meaningful. 2. An EXTRACTOR from a real .tex
    (via [Ast_semantic_state] for labels/refs and direct package scanning for T3
    features) to those structures.

    The Coq lemma [project_wf_dec_sound] proves the checker's [true] verdict is
    sufficient for [pdflatex_compile_safe]; this OCaml side is the runtime
    counterpart, connected by the TESTED mirror-equivalence. *)

type feature =
  | UTF8_inputenc
  | UTF8_direct
  | Unicode_math
  | Opentype_fonts
  | Lua_scripting
  | Japanese_cjk
  | Bibtex
  | Biber

type engine = Pdflatex | Xelatex | Lualatex | Ptex_uptex
type artefact_kind = Tex | Aux | Bbl | Bib | Pdf | Log
type node = { n_file : int; n_kind : artefact_kind }

type body_token =
  | BT_text
  | BT_label_def of int
  | BT_label_ref of int
  | BT_needs_feature of feature

type project = {
  proj_nodes : node list;
  proj_edges : (node * node) list;
  proj_body : body_token list;
}

type profile = { prof_engine : engine; prof_features : feature list }

let feature_to_string = function
  | UTF8_inputenc -> "utf8_inputenc"
  | UTF8_direct -> "utf8_direct"
  | Unicode_math -> "unicode_math"
  | Opentype_fonts -> "opentype_fonts"
  | Lua_scripting -> "lua_scripting"
  | Japanese_cjk -> "japanese_cjk"
  | Bibtex -> "bibtex"
  | Biber -> "biber"

let engine_to_string = function
  | Pdflatex -> "pdflatex"
  | Xelatex -> "xelatex"
  | Lualatex -> "lualatex"
  | Ptex_uptex -> "ptex_uptex"

(* MIRROR of BuildProfileSound.compatible — keep byte-identical to the Coq table
   AND to Compile_contract.feature_compatible. *)
let feature_compatible (f : feature) (e : engine) : bool =
  match (f, e) with
  | UTF8_inputenc, Ptex_uptex -> false
  | UTF8_inputenc, _ -> true
  | UTF8_direct, (Xelatex | Lualatex) -> true
  | UTF8_direct, _ -> false
  | Unicode_math, (Xelatex | Lualatex) -> true
  | Unicode_math, _ -> false
  | Opentype_fonts, (Xelatex | Lualatex) -> true
  | Opentype_fonts, _ -> false
  | Lua_scripting, Lualatex -> true
  | Lua_scripting, _ -> false
  | Japanese_cjk, Ptex_uptex -> true
  | Japanese_cjk, _ -> false
  | Bibtex, _ -> true
  | Biber, _ -> true

let rec body_required_features = function
  | [] -> []
  | BT_needs_feature f :: rest -> f :: body_required_features rest
  | _ :: rest -> body_required_features rest

let rec body_label_defs = function
  | [] -> []
  | BT_label_def n :: rest -> n :: body_label_defs rest
  | _ :: rest -> body_label_defs rest

(* ── OCaml mirror of the Coq boolean checkers ─────────────────────── *)

let node_eqb (a : node) (b : node) : bool =
  a.n_file = b.n_file && a.n_kind = b.n_kind

let node_in_b (n : node) (ns : node list) : bool =
  List.exists (fun m -> node_eqb m n) ns

let edges_closed_b (nodes : node list) (edges : (node * node) list) : bool =
  List.for_all (fun (u, v) -> node_in_b u nodes && node_in_b v nodes) edges

(* Mirror of ProjectClosure.index_of. *)
let index_of (n : node) (order : node list) : int option =
  let rec go i = function
    | [] -> None
    | x :: xs -> if node_eqb x n then Some i else go (i + 1) xs
  in
  go 0 order

let index_lt_b (order : node list) (u : node) (v : node) : bool =
  match (index_of u order, index_of v order) with
  | Some iu, Some iv -> iv < iu
  | _, _ -> false

let valid_topo_b (edges : (node * node) list) (order : node list) : bool =
  List.for_all (fun (u, v) -> index_lt_b order u v) edges

let project_closed_b (nodes : node list) (edges : (node * node) list)
    (order : node list) : bool =
  edges_closed_b nodes edges && valid_topo_b edges order

let all_features_compatible (fs : feature list) (e : engine) : bool =
  List.for_all (fun f -> feature_compatible f e) fs

let nodup_nat_b (l : int list) : bool =
  let rec go seen = function
    | [] -> true
    | x :: xs -> (not (List.mem x seen)) && go (x :: seen) xs
  in
  go [] l

let project_wf_dec (p : project) (pf : profile) (order : node list) : bool =
  project_closed_b p.proj_nodes p.proj_edges order
  && all_features_compatible pf.prof_features pf.prof_engine
  && all_features_compatible (body_required_features p.proj_body) pf.prof_engine
  && nodup_nat_b (body_label_defs p.proj_body)

type premise_report = {
  t2_closed : bool;
  t3_declared : bool;
  t3_body : bool;
  t4_unique_labels : bool;
  duplicate_labels : string list;
  unsupported_features : feature list;
}

let all_hold (r : premise_report) : bool =
  r.t2_closed && r.t3_declared && r.t3_body && r.t4_unique_labels

(* ── Extraction ───────────────────────────────────────────────────── *)

(* Stable, collision-resistant key -> nat. Uses a 30-bit FNV-1a fold so the id
   fits an OCaml int on all platforms and the SAME key hashes identically for a
   \label def and its \ref uses. Distinct keys can in principle collide; the
   T4/T2 verdicts are conservative under collision (a collision can only MERGE
   two labels, i.e. flag a spurious duplicate — a SAFE false NOT-READY, never a
   false READY). *)
let mask30 = 0x3fffffff

let label_id (key : string) : int =
  let h = ref 0x811c9dc5 in
  String.iter
    (fun c ->
      let xored = Int.logand (Int.logxor !h (Char.code c)) mask30 in
      h := Int.logand (xored * 0x01000193) mask30)
    key;
  !h

let feature_of_project_feature (f : Project_model.declared_feature) :
    feature option =
  match f with
  | Project_model.UTF8_inputenc -> Some UTF8_inputenc
  | Project_model.UTF8_direct -> Some UTF8_direct
  | Project_model.Unicode_math -> Some Unicode_math
  | Project_model.Opentype_fonts -> Some Opentype_fonts
  | Project_model.Lua_scripting -> Some Lua_scripting
  | Project_model.Japanese_cjk -> Some Japanese_cjk
  | Project_model.Bibtex -> Some Bibtex
  | Project_model.Biblatex -> Some Biber
  (* Features outside the Coq T3 model are IGNORED (return None), exactly as the
     Coq [compatible] table has no case for them. *)
  | Project_model.Babel_standard | Project_model.Polyglossia
  | Project_model.Amsmath | Project_model.Hyperref
  | Project_model.Graphicx_eps_only | Project_model.Graphicx_multi
  | Project_model.Natbib | Project_model.Other _ ->
      None

(* Substring search (case-sensitive), no regex dep. *)
let contains (hay : string) (needle : string) : bool =
  let nl = String.length needle and hl = String.length hay in
  if nl = 0 then true
  else if nl > hl then false
  else
    let rec go i =
      if i + nl > hl then false
      else if String.sub hay i nl = needle then true
      else go (i + 1)
    in
    go 0

(* Detect the T3-relevant document features from real source. Each is a genuine
   package/primitive whose presence makes the document REQUIRE the feature; the
   engine must then admit it (T3). Conservative: only fires on an unambiguous
   marker. *)
let detect_body_features (source : string) : feature list =
  let acc = ref [] in
  let add f = if not (List.mem f !acc) then acc := f :: !acc in
  if
    contains source "\\usepackage{fontspec}"
    || contains source "\\usepackage[no-math]{fontspec}"
    || contains source "\\setmainfont"
  then add Opentype_fonts;
  if
    contains source "\\usepackage{unicode-math}"
    || contains source "\\setmathfont"
  then add Unicode_math;
  if contains source "\\usepackage{luacode}" || contains source "\\directlua"
  then add Lua_scripting;
  if
    contains source "\\usepackage{CJK}"
    || contains source "\\begin{CJK}"
    || contains source "\\usepackage{luatexja}"
  then add Japanese_cjk;
  if contains source "\\usepackage[utf8]{inputenc}" then add UTF8_inputenc;
  List.rev !acc

(* Body token stream: label defs, label refs, then one BT_needs_feature per
   detected feature, then a BT_text marker if the doc is otherwise non-empty.
   Order within defs/refs follows document order (offset). *)
let extract_body (source : string) : body_token list =
  let labels = Ast_semantic_state.labels source in
  let refs = Ast_semantic_state.refs source in
  let events =
    List.map
      (fun (l : Ast_semantic_state.label_entry) ->
        (l.off, BT_label_def (label_id l.key)))
      labels
    @ List.map
        (fun (r : Ast_semantic_state.ref_entry) ->
          (r.off, BT_label_ref (label_id r.key)))
        refs
  in
  let ordered =
    List.stable_sort (fun (a, _) (b, _) -> compare a b) events |> List.map snd
  in
  let feats =
    List.map (fun f -> BT_needs_feature f) (detect_body_features source)
  in
  let text_marker = if String.trim source = "" then [] else [ BT_text ] in
  ordered @ feats @ text_marker

(* Map a Build_graph.artefact_kind to the Coq-model artefact_kind. *)
let map_kind : Build_graph.artefact_kind -> artefact_kind = function
  | Build_graph.Tex -> Tex
  | Build_graph.Aux -> Aux
  | Build_graph.Bbl -> Bbl
  | Build_graph.Bib -> Bib
  | Build_graph.Pdf -> Pdf
  | Build_graph.Log -> Log

(* Build the Coq-model nodes/edges from a real Build_graph, using each node's
   unique [id] as [n_file] (so nodes stay distinct), and compute a topological
   [order] satisfying Coq's [valid_topo] (for edge (u,v): index_of v < index_of
   u — the CONSUMER v precedes the PRODUCER u). This is the reverse-postorder of
   a DFS on the producer->consumer edges; the build graph is a DAG by
   construction ([Build_graph.is_acyclic]). *)
let graph_of_build_graph (g : Build_graph.t) :
    node list * (node * node) list * node list =
  let bg_nodes = Build_graph.nodes g in
  (* [Build_graph.node_id] is abstract; assign each node a stable sequential
     [n_file] by its position in [Build_graph.nodes], and resolve edge endpoints
     through [find_node] (which returns the node record whose unique [path] is
     the identity key). *)
  let idx = Hashtbl.create 16 in
  List.iteri
    (fun i (bn : Build_graph.node) -> Hashtbl.replace idx bn.path i)
    bg_nodes;
  let mk (bn : Build_graph.node) =
    { n_file = Hashtbl.find idx bn.path; n_kind = map_kind bn.kind }
  in
  let nodes = List.map mk bg_nodes in
  let node_by_id id =
    match Build_graph.find_node g id with
    | Some bn -> mk bn
    | None -> { n_file = -1; n_kind = Tex }
  in
  let edges =
    List.map
      (fun (e : Build_graph.edge) -> (node_by_id e.from_id, node_by_id e.to_id))
      (Build_graph.edges g)
  in
  (* Topological order: we need, for every edge (u,v), v EARLIER than u.
     Equivalently, order consumers before producers = reverse topological order
     of the producer->consumer DAG. Kahn on REVERSED edges (v -> u) then the
     natural emission order already puts v before u. *)
  let adj = Hashtbl.create 16 in
  let indeg = Hashtbl.create 16 in
  List.iter (fun n -> Hashtbl.replace indeg n.n_file 0) nodes;
  List.iter
    (fun (u, v) ->
      (* reversed edge v -> u *)
      let cur = try Hashtbl.find adj v.n_file with Not_found -> [] in
      Hashtbl.replace adj v.n_file (u :: cur);
      Hashtbl.replace indeg u.n_file
        ((try Hashtbl.find indeg u.n_file with Not_found -> 0) + 1))
    edges;
  let queue = Queue.create () in
  List.iter
    (fun n -> if Hashtbl.find indeg n.n_file = 0 then Queue.add n queue)
    nodes;
  let order = ref [] in
  while not (Queue.is_empty queue) do
    let n = Queue.pop queue in
    order := n :: !order;
    let succs = try Hashtbl.find adj n.n_file with Not_found -> [] in
    List.iter
      (fun m ->
        let d = Hashtbl.find indeg m.n_file - 1 in
        Hashtbl.replace indeg m.n_file d;
        if d = 0 then Queue.add m queue)
      succs
  done;
  let order = List.rev !order in
  (* If a cycle slipped in (indeg never hit 0 for some node), fall back to the
     raw node list; project_closed_b will then correctly return false on the
     valid_topo check rather than certify an unsound order. *)
  let order = if List.length order = List.length nodes then order else nodes in
  (nodes, edges, order)

let extract ~(source : string) ~(engine : engine) :
    project * profile * node list =
  (* Trivial single-Tex-node build graph (no project include resolution). *)
  let root = { n_file = 0; n_kind = Tex } in
  let nodes = [ root ] in
  let edges = [] in
  let order = [ root ] in
  let body = extract_body source in
  let p = { proj_nodes = nodes; proj_edges = edges; proj_body = body } in
  (* No declared-feature list at this layer; the T3 obligation is driven by the
     BODY's required features (Residual-3), which is the load-bearing one. *)
  let pf = { prof_engine = engine; prof_features = [] } in
  (p, pf, order)

let engine_of_project (proj : Project_model.t) : engine =
  match proj.Project_model.engine with
  | Project_model.Pdflatex -> Pdflatex
  | Project_model.Xelatex -> Xelatex
  | Project_model.Lualatex -> Lualatex
  | Project_model.Ptex_uptex -> Ptex_uptex

let extract_of_project ~(source : string) (proj : Project_model.t) :
    project * profile * node list =
  let g = Build_graph.of_project proj in
  let nodes, edges, order = graph_of_build_graph g in
  let body = extract_body source in
  let p = { proj_nodes = nodes; proj_edges = edges; proj_body = body } in
  let declared =
    List.filter_map feature_of_project_feature
      proj.Project_model.declared_features
  in
  let pf = { prof_engine = engine_of_project proj; prof_features = declared } in
  (p, pf, order)

(* Recover the offending duplicate label keys (for reporting), by re-hashing. *)
let duplicate_label_keys (source : string) : string list =
  let labels = Ast_semantic_state.labels source in
  let seen = Hashtbl.create 16 in
  let dups = ref [] in
  List.iter
    (fun (l : Ast_semantic_state.label_entry) ->
      let id = label_id l.key in
      if Hashtbl.mem seen id then (
        if not (List.mem l.key !dups) then dups := l.key :: !dups)
      else Hashtbl.replace seen id ())
    labels;
  List.rev !dups

let report (p : project) (pf : profile) (order : node list) : premise_report =
  let body_feats = body_required_features p.proj_body in
  let unsupported =
    List.filter (fun f -> not (feature_compatible f pf.prof_engine)) body_feats
  in
  {
    t2_closed = project_closed_b p.proj_nodes p.proj_edges order;
    t3_declared = all_features_compatible pf.prof_features pf.prof_engine;
    t3_body = all_features_compatible body_feats pf.prof_engine;
    t4_unique_labels = nodup_nat_b (body_label_defs p.proj_body);
    duplicate_labels = [];
    unsupported_features = unsupported;
  }
