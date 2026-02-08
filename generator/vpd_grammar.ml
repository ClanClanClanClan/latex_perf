(* VPD Grammar — YAML front-end for the VPD pipeline.

   Reads rules_v3.yaml (rule catalogue) and vpd_patterns.json (pattern
   annotations) and produces a VPD manifest JSON suitable for vpd_compile.

   Usage: vpd_grammar <rules.yaml> <patterns.json> [-o <manifest.json>]
   [--filter ID,ID,...] [--validate] *)

(* ------------------------------------------------------------------ *)
(*  Minimal YAML-subset parser for flat-record lists                  *)
(* ------------------------------------------------------------------ *)

type yaml_record = { id : string; fields : (string * string) list }
(** A YAML record is a list of (key, value) pairs keyed by "id". *)

let strip_quotes s =
  let n = String.length s in
  if n >= 2 && s.[0] = '"' && s.[n - 1] = '"' then String.sub s 1 (n - 2) else s

let trim s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && (s.[!i] = ' ' || s.[!i] = '\t') do
    incr i
  done;
  let j = ref (n - 1) in
  while !j >= !i && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\r') do
    decr j
  done;
  if !i > !j then "" else String.sub s !i (!j - !i + 1)

(** Parse a flat YAML list of records. Each record starts with [- id: ...] and
    continues with [  key: value] lines until the next record or EOF. Comments
    (#) and blank lines are skipped. *)
let parse_yaml_records (path : string) : yaml_record list =
  let ic = open_in path in
  let records = ref [] in
  let cur_fields = ref [] in
  let cur_id = ref "" in
  let flush () =
    if !cur_id <> "" then
      records := { id = !cur_id; fields = List.rev !cur_fields } :: !records;
    cur_fields := [];
    cur_id := ""
  in
  (try
     while true do
       let raw = input_line ic in
       let line = trim raw in
       if line = "" || line.[0] = '#' then ()
       else if String.length line > 4 && String.sub line 0 4 = "- id" then (
         (* New record: "- id: ..." *)
         flush ();
         let colon_pos =
           match String.index_opt line ':' with
           | Some p -> p
           | None -> failwith ("vpd_grammar: missing colon in: " ^ line)
         in
         let value =
           trim
             (String.sub line (colon_pos + 1)
                (String.length line - colon_pos - 1))
         in
         cur_id := strip_quotes value)
       else
         (* Continuation field: " key: value" *)
         let colon_pos =
           match String.index_opt line ':' with
           | Some p -> p
           | None -> failwith ("vpd_grammar: missing colon in: " ^ line)
         in
         let key = trim (String.sub line 0 colon_pos) in
         let value =
           trim
             (String.sub line (colon_pos + 1)
                (String.length line - colon_pos - 1))
         in
         let value = strip_quotes value in
         cur_fields := (key, value) :: !cur_fields
     done
   with End_of_file -> flush ());
  close_in ic;
  List.rev !records

(* ------------------------------------------------------------------ *)
(*  Pattern companion JSON loader                                     *)
(* ------------------------------------------------------------------ *)

(** Load vpd_patterns.json → association list of (id, json_object). *)
let load_patterns (path : string) : (string * Yojson.Basic.t) list =
  let json = Yojson.Basic.from_file path in
  match json with
  | `Assoc pairs -> pairs
  | _ -> failwith "vpd_grammar: vpd_patterns.json must be a JSON object"

(* ------------------------------------------------------------------ *)
(*  Merge + emit                                                      *)
(* ------------------------------------------------------------------ *)

let find_yaml_record (records : yaml_record list) (id : string) :
    yaml_record option =
  List.find_opt (fun r -> r.id = id) records

let string_of_assoc key (fields : (string * string) list) : string =
  match List.assoc_opt key fields with
  | Some v -> v
  | None -> failwith (Printf.sprintf "vpd_grammar: missing field %S" key)

let json_member key (json : Yojson.Basic.t) : Yojson.Basic.t =
  match json with
  | `Assoc pairs -> (
      match List.assoc_opt key pairs with
      | Some v -> v
      | None -> failwith (Printf.sprintf "vpd_grammar: missing JSON key %S" key)
      )
  | _ -> failwith "vpd_grammar: expected JSON object"

let json_string key (json : Yojson.Basic.t) : string =
  match json_member key json with
  | `String s -> s
  | _ -> failwith (Printf.sprintf "vpd_grammar: expected string for key %S" key)

(** Merge a YAML record and a pattern entry into a VPD manifest rule JSON. *)
let merge_rule (yaml : yaml_record) (pattern_json : Yojson.Basic.t) :
    Yojson.Basic.t =
  let layer = json_string "layer" pattern_json in
  let severity = json_string "severity" pattern_json in
  let message = json_string "message" pattern_json in
  let pattern = json_member "pattern" pattern_json in
  let description = string_of_assoc "description" yaml.fields in
  `Assoc
    [
      ("id", `String yaml.id);
      ("description", `String description);
      ("layer", `String layer);
      ("severity", `String severity);
      ("message", `String message);
      ("pattern", pattern);
    ]

(** Emit a complete VPD manifest JSON. *)
let emit_manifest (rules : Yojson.Basic.t list) : Yojson.Basic.t =
  `Assoc [ ("version", `String "0.2.0"); ("rules", `List rules) ]

(* ------------------------------------------------------------------ *)
(*  Validation                                                        *)
(* ------------------------------------------------------------------ *)

let validate_patterns (records : yaml_record list)
    (patterns : (string * Yojson.Basic.t) list) : unit =
  let errors = ref 0 in
  List.iter
    (fun (id, _pjson) ->
      match find_yaml_record records id with
      | Some _ -> ()
      | None ->
          Printf.eprintf "[vpd_grammar] WARNING: pattern entry %S not in YAML\n"
            id;
          incr errors)
    patterns;
  if !errors > 0 then
    Printf.eprintf "[vpd_grammar] %d validation warning(s)\n" !errors

(* ------------------------------------------------------------------ *)
(*  CLI                                                               *)
(* ------------------------------------------------------------------ *)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let validate_flag = List.mem "--validate" args in
  let args = List.filter (( <> ) "--validate") args in
  (* Extract --filter *)
  let filter_ids, args =
    let rec extract acc = function
      | "--filter" :: ids :: rest ->
          let split =
            String.split_on_char ',' ids
            |> List.map trim
            |> List.filter (fun s -> s <> "")
          in
          extract (acc @ split) rest
      | x :: rest ->
          extract acc (x :: rest |> function _ :: r -> r | [] -> [])
      | [] -> (acc, [])
    in
    (* Simpler approach: scan for --filter, collect its argument *)
    let rec find_filter prev = function
      | "--filter" :: ids :: rest ->
          let split =
            String.split_on_char ',' ids
            |> List.map trim
            |> List.filter (fun s -> s <> "")
          in
          (split, List.rev prev @ rest)
      | x :: rest -> find_filter (x :: prev) rest
      | [] -> ([], List.rev prev)
    in
    ignore extract;
    find_filter [] args
  in
  (* Extract -o *)
  let output_path, args =
    let rec find_output prev = function
      | "-o" :: path :: rest -> (Some path, List.rev prev @ rest)
      | x :: rest -> find_output (x :: prev) rest
      | [] -> (None, List.rev prev)
    in
    find_output [] args
  in
  match args with
  | [ yaml_path; patterns_path ] -> (
      let records = parse_yaml_records yaml_path in
      let patterns = load_patterns patterns_path in
      if validate_flag then validate_patterns records patterns;
      (* Filter patterns if --filter given *)
      let active_patterns =
        match filter_ids with
        | [] -> patterns
        | ids -> List.filter (fun (id, _) -> List.mem id ids) patterns
      in
      (* Merge each pattern entry with its YAML record *)
      let rules =
        List.filter_map
          (fun (id, pjson) ->
            match find_yaml_record records id with
            | Some yaml -> Some (merge_rule yaml pjson)
            | None ->
                Printf.eprintf
                  "[vpd_grammar] WARNING: skipping %S (not in YAML)\n" id;
                None)
          active_patterns
      in
      let manifest = emit_manifest rules in
      let json_str = Yojson.Basic.pretty_to_string ~std:true manifest ^ "\n" in
      match output_path with
      | Some path ->
          let oc = open_out path in
          output_string oc json_str;
          close_out oc;
          Printf.eprintf "[vpd_grammar] Generated %d rules -> %s\n"
            (List.length rules) path
      | None -> print_string json_str)
  | _ ->
      Printf.eprintf
        "Usage: %s <rules.yaml> <patterns.json> [-o <out.json>] [--filter \
         ID,...] [--validate]\n"
        Sys.argv.(0);
      exit 2
