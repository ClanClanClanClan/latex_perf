(* ══════════════════════════════════════════════════════════════════════
   Include_resolver — parse and resolve \input, \include, \includeonly

   Extracts include directives from LaTeX source and resolves them to file
   system paths relative to a base directory.
   ══════════════════════════════════════════════════════════════════════ *)

type include_entry = { command : string; raw_path : string; position : int }
type resolved_include = { entry : include_entry; resolved_path : string option }

(* ── Extraction ──────────────────────────────────────────────────── *)

let re_input = Re_compat.regexp {|\\input{\([^}]+\)}|}
let re_include = Re_compat.regexp {|\\include{\([^}]+\)}|}
let re_includeonly = Re_compat.regexp {|\\includeonly{\([^}]+\)}|}

let extract_with_re re cmd src =
  let entries = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re src !i in
       let path = Re_compat.matched_group _mr 1 src in
       entries :=
         { command = cmd; raw_path = String.trim path; position = pos }
         :: !entries;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  List.rev !entries

let extract_includes (src : string) : include_entry list =
  let inputs = extract_with_re re_input "input" src in
  let includes = extract_with_re re_include "include" src in
  List.sort (fun a b -> compare a.position b.position) (inputs @ includes)

let extract_includeonly (src : string) : string list =
  try
    let _mr, _ = Re_compat.search_forward re_includeonly src 0 in
    let content = Re_compat.matched_group _mr 1 src in
    List.map String.trim (String.split_on_char ',' content)
  with Not_found -> []

(* ── Resolution ──────────────────────────────────────────────────── *)

let resolve_include ~(base_dir : string) (entry : include_entry) :
    resolved_include =
  let raw = entry.raw_path in
  let candidates =
    let full =
      if Filename.is_relative raw then Filename.concat base_dir raw else raw
    in
    [ full; full ^ ".tex" ]
  in
  let resolved_path = List.find_opt Sys.file_exists candidates in
  { entry; resolved_path }

let resolve_all ~(base_dir : string) (entries : include_entry list) :
    resolved_include list =
  List.map (resolve_include ~base_dir) entries
