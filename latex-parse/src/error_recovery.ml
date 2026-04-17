(* ══════════════════════════════════════════════════════════════════════
   Error_recovery — recovery boundary detection and repair predicates

   Finds structural recovery points (paragraph breaks, environments, sections)
   near parse errors. Provides monotonic repair predicate.
   ══════════════════════════════════════════════════════════════════════ *)

type recovery_point = { position : int; kind : string }

(* ── Recovery point detection ────────────────────────────────────── *)

let re_para_break = Re_compat.regexp {|\n\n|}
let re_begin_env = Re_compat.regexp {|\\begin{\([^}]+\)}|}

let re_section =
  Re_compat.regexp {|\\\(section\|subsection\|subsubsection\|chapter\|part\)|}

let find_recovery_points (src : string) (error_pos : int) : recovery_point list
    =
  let n = String.length src in
  let points = ref [] in
  (* Scan forward from error position *)
  let search_from = error_pos in
  (* Paragraph breaks *)
  (try
     let _mr, pos = Re_compat.search_forward re_para_break src search_from in
     ignore _mr;
     points := { position = pos; kind = "paragraph" } :: !points
   with Not_found -> ());
  (* Environment boundaries *)
  (try
     let _mr, pos = Re_compat.search_forward re_begin_env src search_from in
     ignore _mr;
     points := { position = pos; kind = "environment" } :: !points
   with Not_found -> ());
  (* Section commands *)
  (try
     let _mr, pos = Re_compat.search_forward re_section src search_from in
     ignore _mr;
     points := { position = pos; kind = "section" } :: !points
   with Not_found -> ());
  (* Also check backward for closest boundary *)
  (if error_pos > 0 then
     let rev_search = String.sub src 0 error_pos in
     let rev_n = String.length rev_search in
     (* Find last paragraph break before error *)
     let i = ref (rev_n - 2) in
     while !i >= 0 do
       if !i + 1 < rev_n && rev_search.[!i] = '\n' && rev_search.[!i + 1] = '\n'
       then (
         points := { position = !i; kind = "paragraph" } :: !points;
         i := -1 (* break *))
       else decr i
     done);
  ignore n;
  (* Sort by proximity to error_pos *)
  List.sort
    (fun a b ->
      compare (abs (a.position - error_pos)) (abs (b.position - error_pos)))
    !points

(* ── Repair predicate ────────────────────────────────────────────── *)

let error_key (msg, (loc : Parser_l2.loc)) = (msg, loc.offset)

let is_repaired ~(old_errors : (string * Parser_l2.loc) list)
    ~(new_errors : (string * Parser_l2.loc) list) : bool =
  let old_set = List.map error_key old_errors |> List.sort_uniq compare in
  let new_set = List.map error_key new_errors |> List.sort_uniq compare in
  (* Strict subset: new errors ⊂ old errors (fewer = repaired) *)
  List.length new_set < List.length old_set
  && List.for_all (fun e -> List.mem e old_set) new_set
