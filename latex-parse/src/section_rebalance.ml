(* ══════════════════════════════════════════════════════════════════════
   Section_rebalance — section tree extraction + renumbering (spec W48-49)

   Extracts a tree of sections from a LaTeX document, supports renumbering after
   insertions/deletions, and validates structural consistency (no level-skip
   violations like section → subsubsection).
   ══════════════════════════════════════════════════════════════════════ *)

type section_node = {
  level : int; (* 0=chapter, 1=section, 2=subsection, 3=subsubsection *)
  title : string;
  number : int; (* ordinal within parent *)
  label : string option;
  children : section_node list;
  source_offset : int; (* byte offset in source *)
}
(** A node in the section tree. *)

type section_tree = section_node list
(** Section tree = forest of top-level sections. *)

type violation = {
  v_title : string;
  v_expected_max_level : int;
  v_actual_level : int;
  v_offset : int;
}
(** Level-skip violation. *)

(* ── Regex for section commands ───────────────────────────────────── *)

let section_re =
  Str.regexp "\\\\\\(chapter\\|section\\|subsection\\|subsubsection\\)[*]?{"

let level_of_name = function
  | "chapter" -> 0
  | "section" -> 1
  | "subsection" -> 2
  | "subsubsection" -> 3
  | _ -> 4

(* ── Extract flat list of sections from source ────────────────────── *)

type raw_section = {
  rs_level : int;
  rs_name : string;
  rs_title : string;
  rs_label : string option;
  rs_offset : int;
}

let extract_brace_arg (s : string) (start : int) : string * int =
  let len = String.length s in
  if start >= len || s.[start] <> '{' then ("", start)
  else
    let depth = ref 1 in
    let i = ref (start + 1) in
    while !i < len && !depth > 0 do
      if s.[!i] = '{' then incr depth else if s.[!i] = '}' then decr depth;
      incr i
    done;
    (String.sub s (start + 1) (!i - start - 2), !i)

let find_label_after (s : string) (start : int) (limit : int) : string option =
  let label_re = Str.regexp {|\\label{|} in
  try
    let pos = Str.search_forward label_re s start in
    if pos > limit then None
    else
      let lbl, _ = extract_brace_arg s (pos + 7 - 1) in
      Some lbl
  with Not_found -> None

let extract_sections (source : string) : raw_section list =
  let sects = ref [] in
  let start = ref 0 in
  (try
     while true do
       let pos = Str.search_forward section_re source !start in
       let matched = Str.matched_string source in
       (* Extract command name *)
       let name_end = String.index_from matched 0 '{' in
       let name_raw = String.sub matched 1 (name_end - 1) in
       let name =
         if
           String.length name_raw > 0
           && name_raw.[String.length name_raw - 1] = '*'
         then String.sub name_raw 0 (String.length name_raw - 1)
         else name_raw
       in
       let level = level_of_name name in
       let brace_start = pos + String.length matched - 1 in
       let title, title_end = extract_brace_arg source brace_start in
       let label = find_label_after source title_end (title_end + 100) in
       sects :=
         {
           rs_level = level;
           rs_name = name;
           rs_title = title;
           rs_label = label;
           rs_offset = pos;
         }
         :: !sects;
       start := title_end
     done
   with Not_found -> ());
  List.rev !sects

(* ── Build tree from flat list ────────────────────────────────────── *)

let build_tree (raw : raw_section list) : section_tree =
  (* Recursive descent: consume sections at this level, collecting children *)
  let pos = ref 0 in
  let arr = Array.of_list raw in
  let n = Array.length arr in
  let rec collect (parent_level : int) : section_node list =
    let nodes = ref [] in
    let num = ref 0 in
    while !pos < n && arr.(!pos).rs_level > parent_level do
      let rs = arr.(!pos) in
      incr pos;
      incr num;
      let children = collect rs.rs_level in
      nodes :=
        {
          level = rs.rs_level;
          title = rs.rs_title;
          number = !num;
          label = rs.rs_label;
          children;
          source_offset = rs.rs_offset;
        }
        :: !nodes
    done;
    List.rev !nodes
  in
  collect (-1)

(* ── Renumber tree (after insert/delete) ──────────────────────────── *)

let rec renumber_children (nodes : section_node list) : section_node list =
  List.mapi
    (fun i n ->
      { n with number = i + 1; children = renumber_children n.children })
    nodes

let renumber (tree : section_tree) : section_tree = renumber_children tree

(* ── Validate structure (no level-skip violations) ────────────────── *)

let validate (tree : section_tree) : violation list =
  let violations = ref [] in
  let rec check (parent_level : int) (nodes : section_node list) =
    let prev_level = ref parent_level in
    List.iter
      (fun n ->
        (* Violation if we skip more than one level from the previous sibling or
           parent *)
        if n.level > !prev_level + 1 && !prev_level >= 0 then
          violations :=
            {
              v_title = n.title;
              v_expected_max_level = !prev_level + 1;
              v_actual_level = n.level;
              v_offset = n.source_offset;
            }
            :: !violations;
        prev_level := n.level;
        check n.level n.children)
      nodes
  in
  check (-1) tree;
  List.rev !violations

(* ── Flatten tree back to ordered list ────────────────────────────── *)

let rec flatten (tree : section_tree) : raw_section list =
  List.concat_map
    (fun n ->
      {
        rs_level = n.level;
        rs_name =
          (match n.level with
          | 0 -> "chapter"
          | 1 -> "section"
          | 2 -> "subsection"
          | 3 -> "subsubsection"
          | _ -> "paragraph");
        rs_title = n.title;
        rs_label = n.label;
        rs_offset = n.source_offset;
      }
      :: flatten n.children)
    tree

(* ── High-level API ───────────────────────────────────────────────── *)

let extract_tree (source : string) : section_tree =
  let raw = extract_sections source in
  build_tree raw
