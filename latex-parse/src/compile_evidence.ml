(** Compile-guarantee evidence extractor. See [compile_evidence.mli].

    Two halves: 1. The premise DECISION is now the Coq-EXTRACTED
    [CompileGuaranteeBridge.project_wf_dec] (module
    [Compile_guarantee_extracted], generated from
    proofs/CompileGuaranteeExtract.v). The runtime keeps its own OCaml surface
    types ([node]/[feature]/[body_token]/…) and converts them into the extracted
    Coq types, then calls the EXTRACTED boolean checkers — so the executed
    decision IS the proven code, not a hand-written mirror. 2. An EXTRACTOR from
    a real .tex (via [Ast_semantic_state] for labels/refs and direct package
    scanning for T3 features) to those structures.

    The Coq lemma [project_wf_dec_sound] (Qed, 0 admits) proves the checker's
    [true] verdict is sufficient for [pdflatex_compile_safe]; because the
    runtime now EXECUTES the extracted [project_wf_dec], residual (a) of the
    compilation guarantee is closed: the only trusted glue is the
    bytes->body_token extraction and the runtime->extracted-type conversion
    below. *)

module Ext = Compile_guarantee_extracted

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

(* ── Runtime surface type -> extracted Coq type conversions ─────────── *)

(* These are the ONLY trusted glue between the runtime and the PROVEN decision
   (besides the bytes->body_token extractor further down). Each is a direct 1:1
   constructor map onto the Coq-extracted inductives / records. *)

let to_ext_feature : feature -> Ext.feature = function
  | UTF8_inputenc -> Ext.UTF8_inputenc
  | UTF8_direct -> Ext.UTF8_direct
  | Unicode_math -> Ext.Unicode_math
  | Opentype_fonts -> Ext.Opentype_fonts
  | Lua_scripting -> Ext.Lua_scripting
  | Japanese_cjk -> Ext.Japanese_cjk
  | Bibtex -> Ext.Bibtex
  | Biber -> Ext.Biber

let to_ext_engine : engine -> Ext.engine = function
  | Pdflatex -> Ext.Pdflatex
  | Xelatex -> Ext.Xelatex
  | Lualatex -> Ext.Lualatex
  | Ptex_uptex -> Ext.Ptex_uptex

let to_ext_kind : artefact_kind -> Ext.artefact_kind = function
  | Tex -> Ext.Tex
  | Aux -> Ext.Aux
  | Bbl -> Ext.Bbl
  | Bib -> Ext.Bib
  | Pdf -> Ext.Pdf
  | Log -> Ext.Log

let to_ext_node (n : node) : Ext.node =
  { Ext.n_file = n.n_file; n_kind = to_ext_kind n.n_kind }

let to_ext_body_token : body_token -> Ext.body_token = function
  | BT_text -> Ext.BT_text
  | BT_label_def n -> Ext.BT_label_def n
  | BT_label_ref n -> Ext.BT_label_ref n
  | BT_needs_feature f -> Ext.BT_needs_feature (to_ext_feature f)

let to_ext_graph (nodes : node list) (edges : (node * node) list) :
    Ext.build_graph =
  {
    Ext.bg_nodes = List.map to_ext_node nodes;
    bg_edges = List.map (fun (u, v) -> (to_ext_node u, to_ext_node v)) edges;
  }

let to_ext_project (p : project) : Ext.pdflatex_project =
  {
    Ext.proj_graph = to_ext_graph p.proj_nodes p.proj_edges;
    proj_body = List.map to_ext_body_token p.proj_body;
  }

let to_ext_profile (pf : profile) : Ext.pdflatex_profile =
  {
    Ext.prof_engine = to_ext_engine pf.prof_engine;
    prof_features = List.map to_ext_feature pf.prof_features;
  }

(* ── The premise decision: the Coq-EXTRACTED proven checkers ────────── *)

(* [feature_compatible] is [BuildProfileSound.compatible], executed via the
   extraction (was a hand-written mirror table). *)
let feature_compatible (f : feature) (e : engine) : bool =
  Ext.compatible (to_ext_feature f) (to_ext_engine e)

let body_required_features (body : body_token list) : feature list =
  (* Delegate the SELECTION to the extracted function, then map back. The Coq
     [feature] and runtime [feature] are isomorphic; we invert the 1:1 map. *)
  let of_ext_feature : Ext.feature -> feature = function
    | Ext.UTF8_inputenc -> UTF8_inputenc
    | Ext.UTF8_direct -> UTF8_direct
    | Ext.Unicode_math -> Unicode_math
    | Ext.Opentype_fonts -> Opentype_fonts
    | Ext.Lua_scripting -> Lua_scripting
    | Ext.Japanese_cjk -> Japanese_cjk
    | Ext.Bibtex -> Bibtex
    | Ext.Biber -> Biber
  in
  List.map of_ext_feature
    (Ext.body_required_features (List.map to_ext_body_token body))

let body_label_defs (body : body_token list) : int list =
  Ext.body_label_defs (List.map to_ext_body_token body)

let all_features_compatible (fs : feature list) (e : engine) : bool =
  Ext.all_features_compatible (List.map to_ext_feature fs) (to_ext_engine e)

let project_closed_b (nodes : node list) (edges : (node * node) list)
    (order : node list) : bool =
  Ext.project_closed_b (to_ext_graph nodes edges) (List.map to_ext_node order)

let nodup_nat_b (l : int list) : bool = Ext.nodup_nat_b l

(* The whole premise-check is the extracted [project_wf_dec]. A [true] verdict
   is PROVEN sufficient for [pdflatex_compile_safe] by
   [project_wf_dec_sound]. *)
let project_wf_dec (p : project) (pf : profile) (order : node list) : bool =
  Ext.project_wf_dec (to_ext_project p) (to_ext_profile pf)
    (List.map to_ext_node order)

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

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

(* Options-tolerant package-load detector. Returns true iff [source] loads [pkg]
   via \usepackage or \RequirePackage, tolerating an optional [..] option group
   (with arbitrary options) and comma-separated package lists with surrounding
   whitespace/newlines — e.g. \usepackage[ligatures=TeX]{fontspec} and
   \usepackage{amsmath, fontspec} both count.

   v27.1.62 (Bug 2): the old exact-string needle `\usepackage{fontspec}` was
   trivially evaded by any option group, manufacturing a false-READY (the doc
   needs opentype_fonts but T3 never saw the feature). OVER-detection is the
   conservative/safe direction for T3 (it can only add a NOT-READY), so this
   scanner errs toward matching. *)
let uses_package (source : string) (pkg : string) : bool =
  let hl = String.length source in
  let loaders = [ "\\usepackage"; "\\RequirePackage" ] in
  let skip_ws j =
    let rec go j = if j < hl && is_ws source.[j] then go (j + 1) else j in
    go j
  in
  (* Match a loader macro at [i] with a control-word boundary after it. *)
  let match_loader i =
    let rec try_all = function
      | [] -> None
      | ldr :: rest ->
          let ll = String.length ldr in
          if
            i + ll <= hl
            && String.sub source i ll = ldr
            && (i + ll >= hl || not (is_alpha source.[i + ll]))
          then Some (i + ll)
          else try_all rest
    in
    try_all loaders
  in
  (* From just after the loader: optionally skip a [..] group, then read the
     {..} package-name group and test membership of [pkg]. *)
  let group_has_pkg j =
    let j = skip_ws j in
    let j =
      if j < hl && source.[j] = '[' then (
        let rec go k = if k < hl && source.[k] <> ']' then go (k + 1) else k in
        let k = go (j + 1) in
        if k < hl then skip_ws (k + 1) else k)
      else j
    in
    if j < hl && source.[j] = '{' then (
      let rec go k = if k < hl && source.[k] <> '}' then go (k + 1) else k in
      let k = go (j + 1) in
      if k < hl then
        String.sub source (j + 1) (k - (j + 1))
        |> String.split_on_char ','
        |> List.exists (fun n -> String.trim n = pkg)
      else false)
    else false
  in
  let rec scan i =
    if i >= hl then false
    else if source.[i] = '\\' then
      match match_loader i with
      | Some j -> if group_has_pkg j then true else scan (i + 1)
      | None -> scan (i + 1)
    else scan (i + 1)
  in
  scan 0

(* Detect the T3-relevant document features from real source. Each is a genuine
   package/primitive whose presence makes the document REQUIRE the feature; the
   engine must then admit it (T3). Conservative: over-detects (any option group
   or comma-list still matches) so it can only add a NOT-READY, never a
   false-READY. *)
let detect_body_features (source : string) : feature list =
  let acc = ref [] in
  let add f = if not (List.mem f !acc) then acc := f :: !acc in
  if uses_package source "fontspec" || contains source "\\setmainfont" then
    add Opentype_fonts;
  if uses_package source "unicode-math" || contains source "\\setmathfont" then
    add Unicode_math;
  if uses_package source "luacode" || contains source "\\directlua" then
    add Lua_scripting;
  if
    uses_package source "CJK"
    || contains source "\\begin{CJK}"
    || uses_package source "luatexja"
  then add Japanese_cjk;
  if
    uses_package source "inputenc"
    && (contains source "utf8" (* utf8 or utf8x option *))
  then add UTF8_inputenc;
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

(* ── The VERIFIED bytes->body_token front-end ─────────────────────────── *)

module Vfe = Body_token_frontend_extracted

(* Map the Coq-EXTRACTED body_token/feature inductives (which are nominally
   distinct from, but structurally identical to, the runtime ones) back to the
   runtime surface types. Mirror of [to_ext_feature]/[to_ext_body_token] in the
   reverse direction. This is mechanical 1:1 glue. *)
let of_vfe_feature : Vfe.feature -> feature = function
  | Vfe.UTF8_inputenc -> UTF8_inputenc
  | Vfe.UTF8_direct -> UTF8_direct
  | Vfe.Unicode_math -> Unicode_math
  | Vfe.Opentype_fonts -> Opentype_fonts
  | Vfe.Lua_scripting -> Lua_scripting
  | Vfe.Japanese_cjk -> Japanese_cjk
  | Vfe.Bibtex -> Bibtex
  | Vfe.Biber -> Biber

let of_vfe_body_token : Vfe.body_token -> body_token = function
  | Vfe.BT_text -> BT_text
  | Vfe.BT_label_def n -> BT_label_def n
  | Vfe.BT_label_ref n -> BT_label_ref n
  | Vfe.BT_needs_feature f -> BT_needs_feature (of_vfe_feature f)

(* The PROVEN bytes->body_token front-end, executed on a real source string. The
   inputs are built exactly as the Coq model expects (nat extracts to OCaml int
   via ExtrOcamlNatInt): [src] is the byte list of the source, and [protected]
   is THE SAME protected-range set the [Ast_semantic_state] scanners consult
   ([Validators_common.find_verbatim_comment_url_ranges], half-open [a,b)) — so
   the verified front-end sees identical protected bytes and parity with
   [extract_body] holds. *)
let extract_body_verified (source : string) : body_token list =
  let src = List.init (String.length source) (fun i -> Char.code source.[i]) in
  let protected = Validators_common.find_verbatim_comment_url_ranges source in
  List.map of_vfe_body_token (Vfe.body_of_source src protected)

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
  let body = extract_body_verified source in
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
  let body = extract_body_verified source in
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
