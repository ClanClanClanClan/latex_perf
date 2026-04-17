(* ══════════════════════════════════════════════════════════════════════
   Semantic_edges — typed dependency edges between chunks

   Extracts label→ref and macro def→use edges per chunk for dependency-aware
   invalidation. Reuses Semantic_state.extract_labels and extract_refs for
   label/ref detection.
   ══════════════════════════════════════════════════════════════════════ *)

type edge_kind = LabelRef of string | MacroDef of string
type edge = { kind : edge_kind; source_chunk : int; target_chunk : int }

(* ── Label/ref edge extraction ───────────────────────────────────── *)

let extract_label_ref_edges (chunks : Chunk_store.chunk array) : edge list =
  let n = Array.length chunks in
  (* Build label→chunk index map *)
  let label_chunks = Hashtbl.create 32 in
  for i = 0 to n - 1 do
    let labels = Semantic_state.extract_labels chunks.(i).content in
    List.iter
      (fun (l : Semantic_state.label_entry) ->
        Hashtbl.replace label_chunks l.key i)
      labels
  done;
  (* For each ref, create an edge from the label's chunk to the ref's chunk *)
  let edges = ref [] in
  for i = 0 to n - 1 do
    let refs = Semantic_state.extract_refs chunks.(i).content in
    List.iter
      (fun (r : Semantic_state.ref_entry) ->
        match Hashtbl.find_opt label_chunks r.key with
        | Some src_chunk when src_chunk <> i ->
            edges :=
              {
                kind = LabelRef r.key;
                source_chunk = src_chunk;
                target_chunk = i;
              }
              :: !edges
        | _ -> ())
      refs
  done;
  !edges

(* ── Macro def/use edge extraction ───────────────────────────────── *)

let re_newcmd =
  Re_compat.regexp
    {|\\\(newcommand\|renewcommand\|providecommand\).*{?\\\([a-zA-Z]+\)|}

let re_backslash_name = Re_compat.regexp {|\\\([a-zA-Z]+\)|}

let extract_macro_defs content =
  let defs = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re_newcmd content !i in
       let name = Re_compat.matched_group _mr 2 content in
       defs := name :: !defs;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  !defs

let extract_macro_uses content =
  let uses = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re_backslash_name content !i in
       let name = Re_compat.matched_group _mr 1 content in
       uses := name :: !uses;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  !uses

let extract_macro_edges (chunks : Chunk_store.chunk array) : edge list =
  let n = Array.length chunks in
  (* Build macro name → defining chunk index *)
  let macro_chunks = Hashtbl.create 16 in
  for i = 0 to n - 1 do
    let defs = extract_macro_defs chunks.(i).content in
    List.iter (fun name -> Hashtbl.replace macro_chunks name i) defs
  done;
  (* For each chunk, find uses of user-defined macros *)
  let edges = ref [] in
  for i = 0 to n - 1 do
    let uses = extract_macro_uses chunks.(i).content in
    List.iter
      (fun name ->
        match Hashtbl.find_opt macro_chunks name with
        | Some src_chunk when src_chunk <> i ->
            if
              not
                (List.exists
                   (fun e ->
                     e.source_chunk = src_chunk
                     && e.target_chunk = i
                     && e.kind = MacroDef name)
                   !edges)
            then
              edges :=
                {
                  kind = MacroDef name;
                  source_chunk = src_chunk;
                  target_chunk = i;
                }
                :: !edges
        | _ -> ())
      uses
  done;
  !edges

(* ── Combined extraction ─────────────────────────────────────────── *)

let extract_edges (chunks : Chunk_store.chunk array) : edge list =
  let lr = extract_label_ref_edges chunks in
  let md = extract_macro_edges chunks in
  lr @ md
