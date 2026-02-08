(* VPD Emit — Generate OCaml validator code from VPD rule specs.

   Generates a snippet meant to be inserted into validators.ml, where the helper
   functions (count_char, count_substring, strip_math_segments, etc.) and types
   (severity, result, rule) are already defined. *)

open Vpd_types

let severity_to_ocaml = function
  | Error -> "Error"
  | Warning -> "Warning"
  | Info -> "Info"

let ocaml_char_literal c =
  match c with
  | '\'' -> "'\\''"
  | '\\' -> "'\\\\'"
  | '\n' -> "'\\n'"
  | '\r' -> "'\\r'"
  | '\t' -> "'\\t'"
  | c when Char.code c >= 32 && Char.code c < 127 -> Printf.sprintf "'%c'" c
  | c -> Printf.sprintf "(Char.chr %d)" (Char.code c)

(** Normalise a rule ID to a valid OCaml identifier. "TYPO-034" -> "r_typo_034" *)
let rule_ident id =
  "r_"
  ^ String.map
      (fun c ->
        if c = '-' then '_'
        else if c >= 'A' && c <= 'Z' then Char.chr (Char.code c + 32)
        else c)
      id

(** Emit the counting expression for a pattern. Assumes helpers are in scope. *)
let emit_count_expr buf (p : pattern) =
  match p with
  | Count_char c ->
      Printf.bprintf buf "    let cnt = count_char s %s in\n"
        (ocaml_char_literal c)
  | Count_char_strip_math c ->
      Printf.bprintf buf
        "    let s = strip_math_segments s in\n\
        \    let cnt = count_char s %s in\n"
        (ocaml_char_literal c)
  | Count_substring needle ->
      Printf.bprintf buf "    let cnt = count_substring s %S in\n" needle
  | Count_substring_strip_math needle ->
      Printf.bprintf buf
        "    let s = strip_math_segments s in\n\
        \    let cnt = count_substring s %S in\n"
        needle
  | Multi_substring needles ->
      Printf.bprintf buf "    let cnt =\n";
      List.iteri
        (fun i needle ->
          if i = 0 then Printf.bprintf buf "      count_substring s %S\n" needle
          else Printf.bprintf buf "      + count_substring s %S\n" needle)
        needles;
      Printf.bprintf buf "    in\n"
  | Multi_substring_strip_math needles ->
      Printf.bprintf buf "    let s = strip_math_segments s in\n";
      Printf.bprintf buf "    let cnt =\n";
      List.iteri
        (fun i needle ->
          if i = 0 then Printf.bprintf buf "      count_substring s %S\n" needle
          else Printf.bprintf buf "      + count_substring s %S\n" needle)
        needles;
      Printf.bprintf buf "    in\n"
  | Char_range { lo; hi; exclude } ->
      Printf.bprintf buf "    let n = String.length s in\n";
      Printf.bprintf buf "    let rec loop i acc =\n";
      Printf.bprintf buf "      if i >= n then acc\n";
      Printf.bprintf buf "      else\n";
      Printf.bprintf buf
        "        let code = Char.code (String.unsafe_get s i) in\n";
      Printf.bprintf buf "        if code >= %d && code <= %d" lo hi;
      List.iter (fun ex -> Printf.bprintf buf " && code <> %d" ex) exclude;
      Printf.bprintf buf " then loop (i + 1) (acc + 1)\n";
      Printf.bprintf buf "        else loop (i + 1) acc\n";
      Printf.bprintf buf "    in\n";
      Printf.bprintf buf "    let cnt = loop 0 0 in\n"
  | Regex re ->
      Printf.bprintf buf "    let re = Str.regexp %S in\n" re;
      Printf.bprintf buf "    let rec loop i acc =\n";
      Printf.bprintf buf
        "      try ignore (Str.search_forward re s i); loop (Str.match_end ()) \
         (acc + 1)\n";
      Printf.bprintf buf "      with Not_found -> acc\n";
      Printf.bprintf buf "    in\n";
      Printf.bprintf buf "    let cnt = loop 0 0 in\n"
  | Line_pred pred_name ->
      Printf.bprintf buf "    let _total, cnt = any_line_pred s %s in\n"
        pred_name
  | Custom body -> Printf.bprintf buf "    let cnt = (%s) s in\n" body

(** Emit a single rule definition *)
let emit_rule buf (r : rule_spec) =
  let ident = rule_ident r.id in
  Printf.bprintf buf "(* %s *)\n" r.description;
  Printf.bprintf buf "let %s : rule =\n" ident;
  Printf.bprintf buf "  let run s =\n";
  emit_count_expr buf r.pattern;
  Printf.bprintf buf "    if cnt > 0 then\n";
  Printf.bprintf buf "      Some\n";
  Printf.bprintf buf "        {\n";
  Printf.bprintf buf "          id = %S;\n" r.id;
  Printf.bprintf buf "          severity = %s;\n" (severity_to_ocaml r.severity);
  Printf.bprintf buf "          message = %S;\n" r.message;
  Printf.bprintf buf "          count = cnt;\n";
  Printf.bprintf buf "        }\n";
  Printf.bprintf buf "    else None\n";
  Printf.bprintf buf "  in\n";
  Printf.bprintf buf "  { id = %S; run }\n\n" r.id

(** Emit the rule list binding *)
let emit_rule_list buf (rules : rule_spec list) =
  Printf.bprintf buf "let rules_vpd_gen : rule list =\n";
  Printf.bprintf buf "  [\n";
  List.iter (fun r -> Printf.bprintf buf "    %s;\n" (rule_ident r.id)) rules;
  Printf.bprintf buf "  ]\n"

(** Emit the complete snippet for inclusion in validators.ml. *)
let emit_module ~internal:_ (m : manifest) : string =
  let buf = Buffer.create 4096 in
  Printf.bprintf buf
    "(* BEGIN VPD-generated validators v%s — DO NOT EDIT BELOW THIS LINE *)\n\n"
    m.version;
  List.iter (emit_rule buf) m.rules;
  emit_rule_list buf m.rules;
  Printf.bprintf buf "\n(* END VPD-generated validators *)\n";
  Buffer.contents buf
