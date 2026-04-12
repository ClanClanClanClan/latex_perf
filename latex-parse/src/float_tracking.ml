(* ══════════════════════════════════════════════════════════════════════
   Float_tracking — track float/figure positions in document (spec W58)

   Computes distance between float declarations (\begin{figure}) and their
   references (\ref{fig:X}) in the source. Used by FIG-018 (float distance > 3
   pages) and FIG-015 (figure before first ref).
   ══════════════════════════════════════════════════════════════════════ *)

type float_entry = {
  kind : string; (* "figure", "table", etc. *)
  label : string option;
  position : int; (* byte offset in source *)
  line : int;
}

type ref_entry = { key : string; position : int; line : int }

type float_distances = {
  entries : (float_entry * ref_entry * int) list;
  (* (float, ref, char_distance) *)
  max_distance : int;
  before_first_ref : float_entry list;
      (* floats that appear before any reference *)
}

let re_begin_figure = Re_compat.regexp {|\\begin{figure\*?}|}
let re_begin_table = Re_compat.regexp {|\\begin{table\*?}|}
let re_label = Re_compat.regexp {|\\label{\([^}]+\)}|}
let re_ref = Re_compat.regexp {|\\ref{\([^}]+\)}\|\\autoref{\([^}]+\)}|}

let line_at (s : string) (pos : int) : int =
  let cnt = ref 1 in
  for i = 0 to min pos (String.length s - 1) do
    if String.unsafe_get s i = '\n' then incr cnt
  done;
  !cnt

let extract_floats (s : string) : float_entry list =
  let entries = ref [] in
  let scan re kind =
    let i = ref 0 in
    try
      while true do
        let _mr, pos = Re_compat.search_forward re s !i in
        let after = Re_compat.match_end _mr in
        (* Find label inside this float environment *)
        let label =
          try
            let end_pos =
              try
                let _mr, _p =
                  Re_compat.search_forward
                    (Re_compat.regexp_string "\\end{")
                    s after
                in
                ignore _mr;
                _p
              with Not_found -> String.length s
            in
            let body = String.sub s after (end_pos - after) in
            try
              let _mr, _ = Re_compat.search_forward re_label body 0 in
              ignore _mr;
              Some (Re_compat.matched_group _mr 1 body)
            with Not_found -> None
          with _ -> None
        in
        entries :=
          { kind; label; position = pos; line = line_at s pos } :: !entries;
        i := after
      done
    with Not_found -> ()
  in
  scan re_begin_figure "figure";
  scan re_begin_table "table";
  List.rev !entries

let extract_refs (s : string) : ref_entry list =
  let entries = ref [] in
  let i = ref 0 in
  (try
     while true do
       let _mr, pos = Re_compat.search_forward re_ref s !i in
       let key =
         try Re_compat.matched_group _mr 1 s
         with Not_found -> (
           try Re_compat.matched_group _mr 2 s with Not_found -> "")
       in
       entries := { key; position = pos; line = line_at s pos } :: !entries;
       i := Re_compat.match_end _mr
     done
   with Not_found -> ());
  List.rev !entries

let compute_distances (s : string) : float_distances =
  let floats = extract_floats s in
  let refs = extract_refs s in
  let entries = ref [] in
  let before_first_ref = ref [] in
  List.iter
    (fun fl ->
      match fl.label with
      | None -> ()
      | Some lbl ->
          let matching_refs = List.filter (fun r -> r.key = lbl) refs in
          if matching_refs = [] then before_first_ref := fl :: !before_first_ref
          else
            List.iter
              (fun r ->
                let dist = abs (r.position - fl.position) in
                entries := (fl, r, dist) :: !entries;
                if r.position > fl.position then ()
                else before_first_ref := fl :: !before_first_ref)
              matching_refs)
    floats;
  let max_distance = List.fold_left (fun mx (_, _, d) -> max mx d) 0 !entries in
  {
    entries = List.rev !entries;
    max_distance;
    before_first_ref = List.rev !before_first_ref;
  }
