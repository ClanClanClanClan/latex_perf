(* ══════════════════════════════════════════════════════════════════════
   Semantic_state — L3 semantic reducer + label/ref tracking (spec §4 L3,
   W53-57)

   Maintains document-level semantic state: - Label table: all \label{...}
   declarations with positions - Reference table: all \ref{...}, \eqref{...},
   etc. with positions - Duplicate detection - Forward reference detection -
   Label/ref consistency checking
   ══════════════════════════════════════════════════════════════════════ *)

type label_entry = {
  key : string;
  position : int;
  prefix : string; (* "fig:", "eq:", "sec:", "tab:", or "" *)
}

type ref_entry = {
  key : string;
  position : int;
  command : string; (* "ref", "eqref", "autoref", "cref", etc. *)
}

type semantic_state = {
  labels : label_entry list;
  refs : ref_entry list;
  duplicate_labels : string list;
  undefined_refs : string list;
  forward_refs : string list;
}

(* ── Label/ref extraction ───────────────────────────────────── *)

let extract_label_prefix (key : string) : string =
  match String.index_opt key ':' with
  | Some i -> String.sub key 0 (i + 1)
  | None -> ""

let re_label = Re_compat.regexp {|\\label{\([^}]+\)}|}
let re_ref = Re_compat.regexp {|\\ref{\([^}]+\)}|}
let re_eqref = Re_compat.regexp {|\\eqref{\([^}]+\)}|}
let re_autoref = Re_compat.regexp {|\\autoref{\([^}]+\)}|}
let re_cref = Re_compat.regexp {|\\cref{\([^}]+\)}|}
let re_cref_cap = Re_compat.regexp {|\\Cref{\([^}]+\)}|}

let extract_labels (s : string) : label_entry list =
  let entries = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, _ = Re_compat.search_forward re_label s !i in
       ignore _mr;
       let key = Re_compat.matched_group _mr 1 s in
       let pos = Re_compat.match_beginning _mr in
       entries :=
         { key; position = pos; prefix = extract_label_prefix key } :: !entries;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  List.rev !entries

let extract_refs (s : string) : ref_entry list =
  let entries = ref [] in
  let patterns =
    [
      (re_ref, "ref");
      (re_eqref, "eqref");
      (re_autoref, "autoref");
      (re_cref, "cref");
      (re_cref_cap, "Cref");
    ]
  in
  List.iter
    (fun (re, cmd) ->
      let i = ref 0 in
      try
        while true do
          let _mr, _ = Re_compat.search_forward re s !i in
          ignore _mr;
          let key = Re_compat.matched_group _mr 1 s in
          let pos = Re_compat.match_beginning _mr in
          entries := { key; position = pos; command = cmd } :: !entries;
          i := Re_compat.match_end _mr
        done
      with Not_found -> ())
    patterns;
  List.sort (fun a b -> compare a.position b.position) !entries

(* ── Semantic analysis ──────────────────────────────────────── *)

let analyze (s : string) : semantic_state =
  let labels = extract_labels s in
  let refs = extract_refs s in
  (* Duplicate labels: same key appears more than once *)
  let label_keys = List.map (fun (l : label_entry) -> l.key) labels in
  let sorted_keys = List.sort String.compare label_keys in
  let duplicate_labels =
    let rec find_dups acc = function
      | [] | [ _ ] -> List.rev acc
      | a :: (b :: _ as rest) ->
          find_dups (if a = b then a :: acc else acc) rest
    in
    List.sort_uniq String.compare (find_dups [] sorted_keys)
  in
  (* Undefined refs: ref key not in any label *)
  let label_set = Hashtbl.create 64 in
  List.iter (fun (l : label_entry) -> Hashtbl.replace label_set l.key ()) labels;
  let undefined_refs =
    List.filter_map
      (fun r -> if not (Hashtbl.mem label_set r.key) then Some r.key else None)
      refs
    |> List.sort_uniq String.compare
  in
  (* Forward refs: ref appears before its label *)
  let label_positions = Hashtbl.create 64 in
  List.iter
    (fun (l : label_entry) -> Hashtbl.replace label_positions l.key l.position)
    labels;
  let forward_refs =
    List.filter_map
      (fun r ->
        match Hashtbl.find_opt label_positions r.key with
        | Some lpos when r.position < lpos -> Some r.key
        | _ -> None)
      refs
    |> List.sort_uniq String.compare
  in
  { labels; refs; duplicate_labels; undefined_refs; forward_refs }

let build_state = analyze

(* ── Thread-local state for validators ──────────────────────── *)

let _state_tbl : (int, semantic_state) Hashtbl.t = Hashtbl.create 4

let set_state (st : semantic_state) : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.replace _state_tbl tid st

let get_state () : semantic_state option =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.find_opt _state_tbl tid

let clear_state () : unit =
  let tid = Thread.id (Thread.self ()) in
  Hashtbl.remove _state_tbl tid
