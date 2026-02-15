(** Golden corpus CI gate — parses golden YAML files and verifies validator
    results match expect/forbid/expect_msgs assertions. *)

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[golden] FAIL: %s\n%!" msg;
    incr fails)

(* ────────────────────────────────────────────────────────────────── Minimal
   golden YAML parser Handles the fixed structure: cases: - file: PATH expect:
   ["ID", ...] forbid: ["ID", ...] # optional expect_msgs: # optional - "MSG"
   ────────────────────────────────────────────────────────────────── *)

type golden_case = {
  file : string;
  expect : string list;
  forbid : string list;
  expect_msgs : string list;
}

(* Parse a JSON-like ["A", "B"] array from a string *)
let parse_string_array s =
  let s = String.trim s in
  if s = "[]" then []
  else
    (* Strip outer brackets *)
    let inner =
      if String.length s >= 2 && s.[0] = '[' && s.[String.length s - 1] = ']'
      then String.sub s 1 (String.length s - 2)
      else s
    in
    let parts = String.split_on_char ',' inner in
    List.map
      (fun p ->
        let p = String.trim p in
        (* Strip surrounding quotes *)
        if String.length p >= 2 && p.[0] = '"' && p.[String.length p - 1] = '"'
        then String.sub p 1 (String.length p - 2)
        else p)
      parts
    |> List.filter (fun s -> String.length s > 0)

(* Unescape YAML double-quoted string: \\ → \, \" → " *)
let unescape_yaml_str s =
  let buf = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && s.[!i] = '\\' then (
      (match s.[!i + 1] with
      | '\\' -> Buffer.add_char buf '\\'
      | '"' -> Buffer.add_char buf '"'
      | 'n' -> Buffer.add_char buf '\n'
      | c ->
          Buffer.add_char buf '\\';
          Buffer.add_char buf c);
      i := !i + 2)
    else (
      Buffer.add_char buf s.[!i];
      incr i)
  done;
  Buffer.contents buf

(* Strip surrounding quotes from a YAML string value and unescape *)
let strip_quotes s =
  let s = String.trim s in
  if String.length s >= 2 && s.[0] = '"' && s.[String.length s - 1] = '"' then
    unescape_yaml_str (String.sub s 1 (String.length s - 2))
  else s

let starts_with ~prefix s =
  let plen = String.length prefix in
  String.length s >= plen && String.sub s 0 plen = prefix

let parse_golden_yaml path =
  let ic = open_in path in
  let lines = ref [] in
  (try
     while true do
       lines := input_line ic :: !lines
     done
   with End_of_file -> ());
  close_in ic;
  let lines = List.rev !lines in
  let current_case =
    ref { file = ""; expect = []; forbid = []; expect_msgs = [] }
  in
  let result = ref [] in
  let in_expect_msgs = ref false in
  List.iter
    (fun line ->
      let trimmed = String.trim line in
      if trimmed = "" || trimmed = "cases:" || trimmed.[0] = '#' then
        (* skip blank, top-level, comments *)
        ()
      else if starts_with ~prefix:"- file:" trimmed then (
        (* Start of new case — flush previous if it has a file *)
        if !current_case.file <> "" then result := !current_case :: !result;
        let value =
          String.trim (String.sub trimmed 7 (String.length trimmed - 7))
        in
        current_case :=
          { file = value; expect = []; forbid = []; expect_msgs = [] };
        in_expect_msgs := false)
      else if starts_with ~prefix:"expect:" trimmed then (
        let value =
          String.trim (String.sub trimmed 7 (String.length trimmed - 7))
        in
        current_case := { !current_case with expect = parse_string_array value };
        in_expect_msgs := false)
      else if starts_with ~prefix:"forbid:" trimmed then (
        let value =
          String.trim (String.sub trimmed 7 (String.length trimmed - 7))
        in
        current_case := { !current_case with forbid = parse_string_array value };
        in_expect_msgs := false)
      else if starts_with ~prefix:"expect_msgs:" trimmed then
        in_expect_msgs := true
      else if !in_expect_msgs && starts_with ~prefix:"- " trimmed then
        let value =
          String.trim (String.sub trimmed 2 (String.length trimmed - 2))
        in
        current_case :=
          {
            !current_case with
            expect_msgs = !current_case.expect_msgs @ [ strip_quotes value ];
          }
      else in_expect_msgs := false)
    lines;
  (* Flush last case *)
  if !current_case.file <> "" then result := !current_case :: !result;
  List.rev !result

(* ────────────────────────────────────────────────────────────────── Test
   runner ────────────────────────────────────────────────────────────────── *)

(* Resolve file path relative to project root *)
let resolve_path base_dir file_path =
  if Filename.is_relative file_path then Filename.concat base_dir file_path
  else file_path

(* Pipeline mode: mirrors the REST smoke test — expand then validate at L1 *)
type pipeline_mode = Raw_all | Expand_l1

let run_golden_suite ?(mode = Raw_all) suite_name yaml_path base_dir =
  let golden_cases = parse_golden_yaml yaml_path in
  List.iter
    (fun (gc : golden_case) ->
      incr cases;
      let full_path = resolve_path base_dir gc.file in
      (* Read .tex file *)
      let content =
        try
          let ic = open_in full_path in
          let n = in_channel_length ic in
          let s = Bytes.create n in
          really_input ic s 0 n;
          close_in ic;
          Bytes.to_string s
        with Sys_error msg ->
          expect false
            (Printf.sprintf "%s: %s: cannot read file: %s" suite_name gc.file
               msg);
          ""
      in
      if content <> "" || gc.expect = [] then (
        (* Run validators through the appropriate pipeline *)
        let results =
          match mode with
          | Raw_all -> Latex_parse_lib.Validators.run_all content
          | Expand_l1 ->
              let cfg = Rest_simple_expander.default in
              let expanded = Rest_simple_expander.expand_fix cfg content in
              let xs, _, _ =
                Latex_parse_lib.Validators.run_all_with_timings_for_layer
                  expanded Latex_parse_lib.Validators.L1
              in
              xs
        in
        let fired_ids =
          List.map (fun (r : Latex_parse_lib.Validators.result) -> r.id) results
        in
        let fired_msgs =
          List.map
            (fun (r : Latex_parse_lib.Validators.result) ->
              r.id ^ ":" ^ r.message)
            results
        in
        (* Check expect: each expected ID must fire *)
        List.iter
          (fun expected_id ->
            expect
              (List.mem expected_id fired_ids)
              (Printf.sprintf "%s: %s: expected %s to fire but it didn't"
                 suite_name gc.file expected_id))
          gc.expect;
        (* Check forbid: each forbidden ID must NOT fire *)
        List.iter
          (fun forbidden_id ->
            expect
              (not (List.mem forbidden_id fired_ids))
              (Printf.sprintf "%s: %s: %s should NOT fire but it did" suite_name
                 gc.file forbidden_id))
          gc.forbid;
        (* Check expect_msgs: each expected message must appear *)
        List.iter
          (fun expected_msg ->
            expect
              (List.mem expected_msg fired_msgs)
              (Printf.sprintf
                 "%s: %s: expected message [%s] not found in results" suite_name
                 gc.file expected_msg))
          gc.expect_msgs))
    golden_cases

(* ────────────────────────────────────────────────────────────────── Main
   ────────────────────────────────────────────────────────────────── *)

let () =
  (* Enable pilot mode so TYPO rules are included in run_all *)
  Unix.putenv "L0_VALIDATORS" "pilot";
  (* Determine project root: we're run from _build/default/latex-parse/src/ so
     project root is 4 levels up. But for dune test with deps, files are copied
     to the build sandbox. We detect base_dir by checking if specs/ exists
     relative to various candidate roots. *)
  let exe_dir = Filename.dirname Sys.argv.(0) in
  let candidates =
    [
      (* dune runtest: cwd is _build/default *)
      Filename.concat exe_dir "../..";
      (* direct invocation from project root *)
      ".";
      (* fallback *)
      Filename.concat exe_dir "../../..";
      Filename.concat exe_dir "../../../..";
    ]
  in
  let base_dir =
    try
      List.find
        (fun d ->
          Sys.file_exists (Filename.concat d "specs/rules/l1_golden.yaml"))
        candidates
    with Not_found ->
      Printf.eprintf
        "[golden] ERROR: cannot locate specs/rules/l1_golden.yaml from \
         exe_dir=%s\n\
         %!"
        exe_dir;
      exit 2
  in
  Printf.printf "[golden] base_dir = %s\n%!" base_dir;
  run_golden_suite ~mode:Expand_l1 "l1"
    (Filename.concat base_dir "specs/rules/l1_golden.yaml")
    base_dir;
  run_golden_suite "pilot_v1"
    (Filename.concat base_dir "specs/rules/pilot_v1_golden.yaml")
    base_dir;
  run_golden_suite "unicode"
    (Filename.concat base_dir "specs/rules/unicode_golden.yaml")
    base_dir;
  run_golden_suite "locale"
    (Filename.concat base_dir "specs/rules/locale_golden.yaml")
    base_dir;
  if !fails > 0 then (
    Printf.eprintf "[golden] %d failure(s) in %d cases\n%!" !fails !cases;
    exit 1)
  else Printf.printf "[golden] PASS %d cases\n%!" !cases
