(* ══════════════════════════════════════════════════════════════════════
   Project_graph — directed inclusion graph with cycle detection

   Builds a graph of file inclusions starting from a root .tex file. Recursively
   follows \input and \include, detects cycles via DFS with Gray/Black coloring.
   Respects \includeonly from root file.
   ══════════════════════════════════════════════════════════════════════ *)

type edge = { src : string; dst : string; command : string }

type project_graph = {
  root : string;
  files : string list;
  edges : edge list;
  cycles : string list list;
  unresolved : (string * string) list;
}

(* ── Helpers ─────────────────────────────────────────────────────── *)

let read_file path =
  try
    let ic = open_in path in
    Fun.protect
      ~finally:(fun () -> close_in ic)
      (fun () ->
        let n = in_channel_length ic in
        really_input_string ic n)
  with Sys_error _ -> ""

let normalize_path path =
  try Unix.realpath path with Unix.Unix_error _ -> path

type color = White | Gray | Black

(* ── Graph construction ──────────────────────────────────────────── *)

let build ~(root : string) : project_graph =
  let root = normalize_path root in
  let color = Hashtbl.create 32 in
  let edges = ref [] in
  let topo = ref [] in
  let cycles = ref [] in
  let unresolved = ref [] in
  let max_depth = 100 in
  (* Parse includeonly from root *)
  let root_src = read_file root in
  let includeonly = Include_resolver.extract_includeonly root_src in
  let includeonly_set =
    if includeonly = [] then None
    else
      let tbl = Hashtbl.create 16 in
      List.iter (fun name -> Hashtbl.replace tbl name ()) includeonly;
      Some tbl
  in
  let is_allowed entry =
    match includeonly_set with
    | None -> true
    | Some tbl ->
        entry.Include_resolver.command = "input"
        || Hashtbl.mem tbl
             (Filename.chop_extension entry.Include_resolver.raw_path
             |> Filename.basename)
        || Hashtbl.mem tbl entry.Include_resolver.raw_path
  in
  let rec visit path depth =
    if depth > max_depth then ()
    else
      let c =
        match Hashtbl.find_opt color path with Some c -> c | None -> White
      in
      match c with
      | Gray -> cycles := [ path ] :: !cycles
      | Black -> ()
      | White ->
          Hashtbl.replace color path Gray;
          let src = read_file path in
          let dir = Filename.dirname path in
          let entries = Include_resolver.extract_includes src in
          let resolved = Include_resolver.resolve_all ~base_dir:dir entries in
          List.iter
            (fun (ri : Include_resolver.resolved_include) ->
              if is_allowed ri.entry then
                match ri.resolved_path with
                | Some dst ->
                    let dst = normalize_path dst in
                    edges :=
                      { src = path; dst; command = ri.entry.command } :: !edges;
                    visit dst (depth + 1)
                | None -> unresolved := (path, ri.entry.raw_path) :: !unresolved)
            resolved;
          Hashtbl.replace color path Black;
          topo := path :: !topo
  in
  visit root 0;
  {
    root;
    files = List.rev !topo;
    edges = List.rev !edges;
    cycles = !cycles;
    unresolved = List.rev !unresolved;
  }

let is_acyclic (g : project_graph) : bool = g.cycles = []
let file_count (g : project_graph) : int = List.length g.files
