(* ══════════════════════════════════════════════════════════════════════
   Partial_cst — partial parse state classification with trust zones

   Classifies a parsed document into trust zones based on error locations. Error
   damage is bounded to the containing paragraph; regions outside error
   paragraphs maintain Complete confidence.
   ══════════════════════════════════════════════════════════════════════ *)

type parse_confidence = Complete | Partial | Broken
type hole = { position : int; reason : string }

type trust_zone = {
  start_pos : int;
  end_pos : int;
  confidence : parse_confidence;
}

type partial_document = {
  confidence : parse_confidence;
  holes : hole list;
  trust_zones : trust_zone list;
  error_regions : (int * int * string) list;
}

let confidence_to_string = function
  | Complete -> "complete"
  | Partial -> "partial"
  | Broken -> "broken"

(* ── Paragraph boundary detection ────────────────────────────────── *)

let paragraph_bounds (src : string) : (int * int) list =
  Validators_common.split_into_paragraphs src

let find_containing_paragraph (paras : (int * int) list) (pos : int) : int * int
    =
  match
    List.find_opt (fun (start, len) -> pos >= start && pos < start + len) paras
  with
  | Some (start, len) -> (start, start + len)
  | None ->
      (* Fallback: entire document *)
      (0, max 1 pos)

(* ── Damage radius ───────────────────────────────────────────────── *)

let damage_radius ~(error_pos : int) (src : string) : int * int =
  let paras = paragraph_bounds src in
  find_containing_paragraph paras error_pos

(* ── Classification ──────────────────────────────────────────────── *)

let classify (src : string) (errors : (string * Parser_l2.loc) list) :
    partial_document =
  if errors = [] then
    {
      confidence = Complete;
      holes = [];
      trust_zones =
        [
          { start_pos = 0; end_pos = String.length src; confidence = Complete };
        ];
      error_regions = [];
    }
  else
    let paras = paragraph_bounds src in
    let n = String.length src in
    (* Find which paragraphs contain errors *)
    let error_paras = Hashtbl.create 8 in
    let error_regions = ref [] in
    let holes = ref [] in
    List.iter
      (fun (msg, (loc : Parser_l2.loc)) ->
        let start, end_ = find_containing_paragraph paras loc.offset in
        Hashtbl.replace error_paras start ();
        error_regions := (start, end_, msg) :: !error_regions;
        holes := { position = loc.offset; reason = msg } :: !holes)
      errors;
    (* Build trust zones from paragraphs *)
    let trust_zones =
      List.map
        (fun (start, len) ->
          let end_ = start + len in
          let conf =
            if Hashtbl.mem error_paras start then Broken
            else
              (* Adjacent to error paragraph = Partial *)
              let adjacent =
                List.exists
                  (fun (ps, pl) ->
                    let pe = ps + pl in
                    Hashtbl.mem error_paras ps
                    && (pe = start
                       || end_ = ps
                       || (pe > start && pe <= start + 2)
                       || (end_ > ps && end_ <= ps + 2)))
                  paras
              in
              if adjacent then Partial else Complete
          in
          { start_pos = start; end_pos = end_; confidence = conf })
        paras
    in
    (* Fill gap if paragraphs don't cover entire source *)
    let trust_zones =
      if trust_zones = [] then
        [ { start_pos = 0; end_pos = n; confidence = Broken } ]
      else trust_zones
    in
    let overall =
      if List.exists (fun z -> (z : trust_zone).confidence = Broken) trust_zones
      then Broken
      else if
        List.exists (fun z -> (z : trust_zone).confidence = Partial) trust_zones
      then Partial
      else Complete
    in
    {
      confidence = overall;
      holes = List.rev !holes;
      trust_zones;
      error_regions = List.rev !error_regions;
    }

(* PR #241 (p1.2, memo §6 E3): expose stable node_ids for trust zones so
   consumers can track a zone across edits. The [command_hash] slot encodes the
   confidence tag: 0 = Complete, 1 = Partial, 2 = Broken. Matches
   proofs/StableNodeIds.v::of_located_stable_under_local_edit — zones whose span
   is outside an edit keep the same content_id. *)
let zone_id (z : trust_zone) : Node_id.t =
  let conf_tag =
    match z.confidence with Complete -> 0 | Partial -> 1 | Broken -> 2
  in
  Node_id.of_located
    ~node_length:(max 0 (z.end_pos - z.start_pos))
    ~command_hash:conf_tag
    { Parser_l2.line = 0; col = 0; offset = z.start_pos }
