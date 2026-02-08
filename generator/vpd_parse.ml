(* VPD Parse — Read JSON manifest into VPD types *)

open Vpd_types

let severity_of_string = function
  | "Error" | "error" -> Error
  | "Warning" | "warning" -> Warning
  | "Info" | "info" -> Info
  | s -> failwith (Printf.sprintf "vpd_parse: unknown severity %S" s)

let layer_of_string = function
  | "L0_Lexer" | "L0" -> L0_Lexer
  | "L1_Expanded" | "L1" -> L1_Expanded
  | "L2_Ast" | "L2" -> L2_Ast
  | "L3_Semantics" | "L3" -> L3_Semantics
  | "L4_Style" | "L4" -> L4_Style
  | s -> failwith (Printf.sprintf "vpd_parse: unknown layer %S" s)

let string_member key json =
  match Yojson.Basic.Util.member key json with
  | `String s -> s
  | _ -> failwith (Printf.sprintf "vpd_parse: expected string for key %S" key)

let string_list_member key json =
  match Yojson.Basic.Util.member key json with
  | `List lst ->
      List.map
        (function
          | `String s -> s
          | _ ->
              failwith
                (Printf.sprintf "vpd_parse: expected string in list for key %S"
                   key))
        lst
  | _ -> failwith (Printf.sprintf "vpd_parse: expected list for key %S" key)

let int_member key json =
  match Yojson.Basic.Util.member key json with
  | `Int i -> i
  | _ -> failwith (Printf.sprintf "vpd_parse: expected int for key %S" key)

let int_list_member_opt key json =
  match Yojson.Basic.Util.member key json with
  | `Null -> []
  | `List lst ->
      List.map
        (function
          | `Int i -> i
          | _ ->
              failwith
                (Printf.sprintf "vpd_parse: expected int in list for key %S" key))
        lst
  | _ -> []

let parse_pattern (json : Yojson.Basic.t) : pattern =
  let family = string_member "family" json in
  match family with
  | "count_char" ->
      let c = string_member "char" json in
      if String.length c <> 1 then
        failwith "vpd_parse: count_char expects single char";
      Count_char c.[0]
  | "count_char_strip_math" ->
      let c = string_member "char" json in
      if String.length c <> 1 then
        failwith "vpd_parse: count_char_strip_math expects single char";
      Count_char_strip_math c.[0]
  | "count_substring" ->
      let sub = string_member "needle" json in
      Count_substring sub
  | "count_substring_strip_math" ->
      let sub = string_member "needle" json in
      Count_substring_strip_math sub
  | "multi_substring" ->
      let needles = string_list_member "needles" json in
      Multi_substring needles
  | "multi_substring_strip_math" ->
      let needles = string_list_member "needles" json in
      Multi_substring_strip_math needles
  | "char_range" ->
      let lo = int_member "lo" json in
      let hi = int_member "hi" json in
      let exclude = int_list_member_opt "exclude" json in
      Char_range { lo; hi; exclude }
  | "regex" ->
      let re = string_member "regex" json in
      Regex re
  | "line_pred" ->
      let name = string_member "predicate" json in
      Line_pred name
  | "custom" ->
      let body = string_member "body" json in
      Custom body
  | _ -> failwith (Printf.sprintf "vpd_parse: unknown pattern family %S" family)

let parse_rule (json : Yojson.Basic.t) : rule_spec =
  let id = string_member "id" json in
  let description = string_member "description" json in
  let layer = layer_of_string (string_member "layer" json) in
  let severity = severity_of_string (string_member "severity" json) in
  let message = string_member "message" json in
  let pattern_json = Yojson.Basic.Util.member "pattern" json in
  let pattern = parse_pattern pattern_json in
  { id; description; layer; severity; message; pattern }

let parse_manifest (json : Yojson.Basic.t) : manifest =
  let version = string_member "version" json in
  let rules_json = Yojson.Basic.Util.member "rules" json in
  let rules =
    match rules_json with
    | `List lst -> List.map parse_rule lst
    | _ -> failwith "vpd_parse: expected rules array"
  in
  { version; rules }

let parse_file (path : string) : manifest =
  let json = Yojson.Basic.from_file path in
  parse_manifest json
