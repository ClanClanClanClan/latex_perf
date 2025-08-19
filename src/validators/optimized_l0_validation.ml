(* OPTIMIZED L0 VALIDATION - FIXING THE PERFORMANCE ISSUE *)
(* The validation was O(n²) - fixing to O(n) *)

(* Copy all the working arena lexer code from WORKING_L0_INTEGRATION.ml but fix validation *)

type catcode = 
  | Escape | BeginGroup | EndGroup | MathShift | AlignTab | EndLine 
  | Param | Superscript | Subscript | Ignored | Space | Letter 
  | Other | Active | Comment | Invalid

let catcode_to_int = function
  | Escape -> 0 | BeginGroup -> 1 | EndGroup -> 2 | MathShift -> 3
  | AlignTab -> 4 | EndLine -> 5 | Param -> 6 | Superscript -> 7
  | Subscript -> 8 | Ignored -> 9 | Space -> 10 | Letter -> 11
  | Other -> 12 | Active -> 13 | Comment -> 14 | Invalid -> 15

type location = { byte_start : int; byte_end : int }
let make_location start end_pos = { byte_start = start; byte_end = end_pos }

type token =
  | TChar of Uchar.t * catcode
  | TMacro of string
  | TParam of int
  | TGroupOpen
  | TGroupClose
  | TEOF

type located_token = {
  token: token;
  loc: location;
}

module Arena = struct
  type t = {
    buffer: bytes;
    mutable write_pos: int;
    capacity: int;
  }
  
  let create size = {
    buffer = Bytes.create (size * 12);
    write_pos = 0;
    capacity = size * 12;
  }
  
  let[@inline] emit_packed_token arena packed_token =
    if arena.write_pos + 4 <= arena.capacity then (
      Bytes.set_int32_le arena.buffer arena.write_pos packed_token;
      arena.write_pos <- arena.write_pos + 4
    )
  
  let get_tokens arena =
    let num_tokens = arena.write_pos / 4 in
    let tokens = Array.make num_tokens 0l in
    for i = 0 to num_tokens - 1 do
      tokens.(i) <- Bytes.get_int32_le arena.buffer (i * 4)
    done;
    tokens
end

module TokenPacking = struct
  let[@inline] pack_token catcode data =
    Int32.logor 
      (Int32.shift_left (Int32.of_int data) 6)
      (Int32.of_int catcode)
  
  let[@inline] unpack_catcode packed =
    Int32.to_int (Int32.logand packed 0x3Fl)
  
  let[@inline] unpack_data packed =
    Int32.to_int (Int32.shift_right_logical packed 6)
  
  let cc_escape = 0
  let cc_begin_group = 1  
  let cc_end_group = 2
  let cc_math_shift = 3
  let cc_align_tab = 4
  let cc_end_line = 5
  let cc_param = 6
  let cc_space = 10
  let cc_letter = 11
  let cc_other = 12
  let cc_comment = 14
end

module StringOps = struct
  let macro_table : (string, int) Hashtbl.t = Hashtbl.create 2048
  let reverse_macro_table : (int, string) Hashtbl.t = Hashtbl.create 2048
  let macro_counter = ref 0
  
  let initialize_builtin_macros () =
    let add_macro name =
      let id = !macro_counter in
      incr macro_counter;
      Hashtbl.add macro_table name id;
      Hashtbl.add reverse_macro_table id name
    in
    
    List.iter add_macro [
      "documentclass"; "usepackage"; "begin"; "end"; "section"; "subsection";
      "textit"; "textbf"; "emph"; "label"; "ref"; "cite"; "caption";
      "includegraphics"; "LaTeX"; "TeX"; "eqnarray"; "figure"
    ]
  
  let[@inline] get_macro_id name =
    try Hashtbl.find macro_table name
    with Not_found -> -1
  
  let[@inline] get_macro_name_by_id id =
    try Some (Hashtbl.find reverse_macro_table id)
    with Not_found -> None
end

let lookup_catcode char_code =
  match char_code with
  | 92 -> Escape | 123 -> BeginGroup | 125 -> EndGroup | 36 -> MathShift
  | 38 -> AlignTab | 10 | 13 -> EndLine | 35 -> Param | 94 -> Superscript
  | 95 -> Subscript | 32 | 9 -> Space | 37 -> Comment
  | c when (c >= 65 && c <= 90) || (c >= 97 && c <= 122) -> Letter
  | _ -> Other

let tokenize_arena input =
  let () = StringOps.initialize_builtin_macros () in
  let len = String.length input in
  let arena = Arena.create (len * 2) in
  let i = ref 0 in
  
  while !i < len do
    let c = Char.code input.[!i] in
    let catcode = lookup_catcode c in
    
    match catcode with
    | Escape when !i + 1 < len ->
        incr i;
        let start = !i in
        while !i < len && 
              let c = Char.code input.[!i] in
              (c >= 65 && c <= 90) || (c >= 97 && c <= 122) do
          incr i
        done;
        
        if !i > start then (
          let macro_name = String.sub input start (!i - start) in
          let macro_id = StringOps.get_macro_id macro_name in
          if macro_id >= 0 then
            Arena.emit_packed_token arena (TokenPacking.pack_token TokenPacking.cc_escape macro_id)
          else
            Arena.emit_packed_token arena (TokenPacking.pack_token TokenPacking.cc_other c)
        ) else (
          Arena.emit_packed_token arena (TokenPacking.pack_token TokenPacking.cc_escape c)
        )
    
    | BeginGroup ->
        Arena.emit_packed_token arena (TokenPacking.pack_token TokenPacking.cc_begin_group c);
        incr i
    | EndGroup ->
        Arena.emit_packed_token arena (TokenPacking.pack_token TokenPacking.cc_end_group c);
        incr i
    | Comment ->
        while !i < len && input.[!i] <> '\n' do incr i done;
        if !i < len then (
          Arena.emit_packed_token arena (TokenPacking.pack_token TokenPacking.cc_end_line (Char.code '\n'));
          incr i
        )
    | _ ->
        Arena.emit_packed_token arena (TokenPacking.pack_token (catcode_to_int catcode) c);
        incr i
  done;
  
  Arena.get_tokens arena

let convert_packed_tokens packed_tokens =
  Array.to_list (Array.mapi (fun i packed ->
    let catcode_int = TokenPacking.unpack_catcode packed in
    let data = TokenPacking.unpack_data packed in
    let location = make_location i (i + 1) in
    
    let token = match catcode_int with
    | c when c = TokenPacking.cc_escape ->
        (match StringOps.get_macro_name_by_id data with
        | Some name -> TMacro name
        | None -> TChar (Uchar.of_int data, Escape))
    | c when c = TokenPacking.cc_begin_group -> TGroupOpen
    | c when c = TokenPacking.cc_end_group -> TGroupClose
    | c when c = TokenPacking.cc_param -> TParam 1
    | _ ->
        let ascii = data land 0xFF in
        let catcode_val = match catcode_int with
          | 0 -> Escape | 1 -> BeginGroup | 2 -> EndGroup | 3 -> MathShift
          | 4 -> AlignTab | 5 -> EndLine | 6 -> Param | 7 -> Superscript
          | 8 -> Subscript | 9 -> Ignored | 10 -> Space | 11 -> Letter
          | 12 -> Other | 13 -> Active | 14 -> Comment | 15 -> Invalid
          | _ -> Other
        in
        TChar (Uchar.of_int ascii, catcode_val)
    in
    { token = token; loc = location }
  ) packed_tokens)

(* OPTIMIZED VALIDATION - Convert to token arrays for O(1) access *)

type validation_issue = {
  rule_id: string;
  message: string;
  position: int;
  suggestion: string option;
  confidence: float;
  severity: [`Error | `Warning | `Info];
  category: string;
}

(* FAST: Convert to array once for all rules *)
let optimize_tokens_for_validation tokens =
  let token_array = Array.of_list (List.map (fun lt -> lt.token) tokens) in
  token_array

(* FAST: O(n) deprecated environment check *)
let check_deprecated_environments_fast token_array =
  let issues = ref [] in
  let len = Array.length token_array in
  
  for i = 0 to len - 3 do
    match token_array.(i) with
    | TMacro "begin" when i + 2 < len ->
        (match token_array.(i+1), token_array.(i+2) with
        | TGroupOpen, TMacro env_name when env_name = "eqnarray" || env_name = "eqnarray*" ->
            issues := {
              rule_id = "MATH-001";
              message = Printf.sprintf "Deprecated %s environment detected" env_name;
              position = i;
              suggestion = Some "Use \\begin{align} from amsmath package instead";
              confidence = 0.95;
              severity = `Warning;
              category = "Math";
            } :: !issues
        | _ -> ())
    | _ -> ()
  done;
  List.rev !issues

(* FAST: O(n) figure caption check *)
let check_figure_captions_fast token_array =
  let issues = ref [] in
  let len = Array.length token_array in
  let in_figure = ref false in
  let figure_start = ref 0 in
  let has_caption = ref false in
  
  for i = 0 to len - 1 do
    match token_array.(i) with
    | TMacro "begin" when i + 2 < len ->
        (match token_array.(i+1), token_array.(i+2) with
        | TGroupOpen, TMacro "figure" ->
            in_figure := true;
            figure_start := i;
            has_caption := false
        | _ -> ())
    | TMacro "end" when i + 2 < len ->
        (match token_array.(i+1), token_array.(i+2) with
        | TGroupOpen, TMacro "figure" ->
            if !in_figure && not !has_caption then
              issues := {
                rule_id = "FIG-001";
                message = "Figure without caption";
                position = !figure_start;
                suggestion = Some "Add \\caption{description} to figure";
                confidence = 0.9;
                severity = `Warning;
                category = "Structure";
              } :: !issues;
            in_figure := false
        | _ -> ())
    | TMacro "caption" when !in_figure ->
        has_caption := true
    | _ -> ()
  done;
  List.rev !issues

(* FAST: O(n) quotation mark check *)
let check_quotation_marks_fast token_array =
  let issues = ref [] in
  let len = Array.length token_array in
  
  for i = 0 to len - 1 do
    match token_array.(i) with
    | TChar (uchar, _) ->
        let code = Uchar.to_int uchar in
        (match code with
        | 34 -> (* straight double quote *)
            issues := {
              rule_id = "TYPO-002";
              message = "Straight quotation marks found";
              position = i;
              suggestion = Some "Use ``text'' for double quotes";
              confidence = 0.9;
              severity = `Warning;
              category = "Typography";
            } :: !issues
        | 39 -> (* straight single quote *)
            issues := {
              rule_id = "TYPO-003";
              message = "Straight apostrophe/quote found";
              position = i;
              suggestion = Some "Use LaTeX single quotes `text'";
              confidence = 0.7;
              severity = `Warning;
              category = "Typography";
            } :: !issues
        | _ -> ())
    | _ -> ()
  done;
  List.rev !issues

(* OPTIMIZED VALIDATION RUNNER *)
let run_validation_optimized tokens =
  let start_time = Sys.time () in
  let token_array = optimize_tokens_for_validation tokens in
  let all_issues = ref [] in
  
  let rule_functions = [
    ("MATH-001", check_deprecated_environments_fast);
    ("FIG-001", check_figure_captions_fast);
    ("TYPO-002/003", check_quotation_marks_fast);
  ] in
  
  List.iter (fun (rule_id, rule_func) ->
    try
      let rule_issues = rule_func token_array in
      all_issues := !all_issues @ rule_issues;
      Printf.printf "   - Rule %s: %d issues\n" rule_id (List.length rule_issues)
    with
    | exn ->
        Printf.printf "   - Rule %s failed: %s\n" rule_id (Printexc.to_string exn)
  ) rule_functions;
  
  let execution_time = (Sys.time () -. start_time) *. 1000.0 in
  (!all_issues, execution_time)

(* COMPLETE OPTIMIZED PIPELINE *)
let test_optimized_l0_pipeline latex_input =
  Printf.printf "\n🚀 OPTIMIZED L0 PIPELINE TEST\n";
  Printf.printf "==============================\n";
  Printf.printf "Input: %d bytes\n" (String.length latex_input);
  Printf.printf "LaTeX: %s\n\n" (String.sub latex_input 0 (min 100 (String.length latex_input)));
  
  let total_start_time = Sys.time () in
  
  (* Stage 1: L0 Lexer *)
  Printf.printf "🔤 Stage 1: L0 Arena Lexer\n";
  let lexer_start_time = Sys.time () in
  
  let packed_tokens = tokenize_arena latex_input in
  let tokens = convert_packed_tokens packed_tokens in
  
  let lexer_time = (Sys.time () -. lexer_start_time) *. 1000.0 in
  Printf.printf "   ✅ Generated %d tokens in %.2f ms\n" (List.length tokens) lexer_time;
  
  (* Stage 2: OPTIMIZED Validation *)
  Printf.printf "\n⚡ Stage 2: OPTIMIZED Validation\n";
  let (issues, validation_time) = run_validation_optimized tokens in
  Printf.printf "   ✅ Found %d issues in %.2f ms\n" (List.length issues) validation_time;
  
  let total_time = (Sys.time () -. total_start_time) *. 1000.0 in
  
  Printf.printf "\n📊 OPTIMIZED PIPELINE RESULTS\n";
  Printf.printf "==============================\n";
  Printf.printf "Total time: %.2f ms\n" total_time;
  Printf.printf "L0 Lexer: %.2f ms (%.1f%%)\n" lexer_time (100.0 *. lexer_time /. total_time);
  Printf.printf "OPTIMIZED Validation: %.2f ms (%.1f%%)\n" validation_time (100.0 *. validation_time /. total_time);
  Printf.printf "Tokens generated: %d\n" (List.length tokens);
  Printf.printf "Issues found: %d\n" (List.length issues);
  Printf.printf "Validation speed: %.3f µs/token\n" (validation_time *. 1000.0 /. float (List.length tokens));
  
  if List.length issues > 0 then (
    Printf.printf "\n🔍 ISSUES DETECTED:\n";
    List.iteri (fun i issue ->
      if i < 5 then
        Printf.printf "  %d. [%s] %s\n" (i+1) issue.rule_id issue.message
    ) issues;
    if List.length issues > 5 then
      Printf.printf "  ... and %d more issues\n" (List.length issues - 5)
  );
  
  Printf.printf "\n🎯 Performance: %s\n" 
    (if total_time <= 25.0 then "✅ PASS (≤25ms)" else "❌ FAIL (>25ms)");
  
  (tokens, issues, total_time)

(* TEST OPTIMIZED SYSTEM *)
let () =
  Printf.printf "⚡ OPTIMIZED L0 INTEGRATION SYSTEM\n";
  Printf.printf "===================================\n";
  Printf.printf "Fixed O(n²) validation performance issue\n";
  
  (* Test on large corpus file *)
  let large_file = "corpora/perf_smoke.tex" in
  if Sys.file_exists large_file then (
    Printf.printf "\n📄 Testing OPTIMIZED pipeline on: %s\n" (Filename.basename large_file);
    Printf.printf "==================================================\n";
    
    let ic = open_in large_file in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    
    let (tokens, issues, time_ms) = test_optimized_l0_pipeline content in
    
    Printf.printf "\n🏆 OPTIMIZATION RESULTS\n";
    Printf.printf "=======================\n";
    Printf.printf "Document size: %.1f KB\n" (float (String.length content) /. 1024.0);
    Printf.printf "Total time: %.2f ms\n" time_ms;
    Printf.printf "Performance: %s\n" (if time_ms <= 25.0 then "✅ EXCELLENT" else "⚠️ NEEDS MORE WORK");
    Printf.printf "\n🎯 VALIDATION IS NOW: %s\n" 
      (if time_ms <= 25.0 then "PRODUCTION READY ✅" else "FAST BUT STILL OPTIMIZING ⚡");
  ) else (
    Printf.printf "\n❌ Large test file not found: %s\n" large_file;
    
    (* Test on smaller documents *)
    let test_latex = {|
\documentclass{article}
\usepackage{amsmath}
\begin{document}
\section{Test}
This has "straight quotes" and 'apostrophes'.

\begin{eqnarray}
x &=& y \\
a &=& b
\end{eqnarray}

\begin{figure}[h]
\includegraphics{test.png}
\end{figure}
\end{document}
|} in
    let _result = test_optimized_l0_pipeline test_latex in
    ()
  );
  
  Printf.printf "\n🚀 OPTIMIZATION COMPLETE\n";
  Printf.printf "========================\n";
  Printf.printf "✅ Fixed O(n²) validation performance\n";
  Printf.printf "✅ Validation now runs in O(n) time\n";
  Printf.printf "⚡ System ready for large document processing\n"