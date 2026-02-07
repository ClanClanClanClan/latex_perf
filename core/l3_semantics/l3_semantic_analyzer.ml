(* L3 Semantic Analyzer - LaTeX Perfectionist v25 *)
(* Week 2-3 Implementation: Semantic analysis and context tracking *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

type semantic_context = {
  (* Document structure *)
  document_class : string option;
  packages : string list;
  preamble_complete : bool;
  (* Current context *)
  current_section : string option;
  section_depth : int;
  in_math_mode : bool;
  in_verbatim : bool;
  (* Environments *)
  environment_stack : string list;
  (* Cross-references *)
  labels : (string * Location.t) list;
  refs : (string * Location.t) list;
  citations : (string * Location.t) list;
  (* Counters *)
  equation_count : int;
  figure_count : int;
  table_count : int;
  footnote_count : int;
  (* Semantic issues *)
  warnings : semantic_warning list;
  errors : semantic_error list;
}
(** Semantic context for LaTeX document analysis *)

and semantic_warning = {
  level : warning_level;
  message : string;
  location : Location.t;
  suggestion : string option;
}

and warning_level = Hint | Info | Warning

and semantic_error = {
  severity : error_severity;
  message : string;
  location : Location.t;
  fix : string option;
}

and error_severity = Minor | Major | Critical

(** Document structure analysis *)
module DocumentStructure = struct
  type section_info = {
    level : int; (* 0=chapter, 1=section, 2=subsection, etc *)
    title : string;
    label : string option;
    location : Location.t;
    word_count : int;
  }

  type document_outline = {
    sections : section_info list;
    max_depth : int;
    total_sections : int;
    avg_section_length : float;
  }

  let analyze_structure tokens =
    let sections = ref [] in
    let current_depth = ref 0 in

    let rec scan = function
      | [] -> ()
      | TMacro "chapter" :: rest ->
          current_depth := 0;
          extract_section 0 rest
      | TMacro "section" :: rest ->
          current_depth := 1;
          extract_section 1 rest
      | TMacro "subsection" :: rest ->
          current_depth := 2;
          extract_section 2 rest
      | TMacro "subsubsection" :: rest ->
          current_depth := 3;
          extract_section 3 rest
      | _ :: rest -> scan rest
    and extract_section level = function
      | TGroupOpen :: rest ->
          let title_tokens, remaining = extract_until_group_close rest in
          let title = tokens_to_string title_tokens in
          sections :=
            {
              level;
              title;
              label = None;
              (* Note: Extract from preceding \label *)
              location = Location.make 0 0;
              (* Note: Track actual location *)
              word_count = count_words title;
            }
            :: !sections;
          scan remaining
      | rest -> scan rest
    and extract_until_group_close tokens =
      let rec aux acc = function
        | [] -> (List.rev acc, [])
        | TGroupClose :: rest -> (List.rev acc, rest)
        | tok :: rest -> aux (tok :: acc) rest
      in
      aux [] tokens
    and tokens_to_string tokens =
      String.concat " "
        (List.filter_map
           (function
             | TChar (uc, _) ->
                 let buf = Buffer.create 4 in
                 Buffer.add_utf_8_uchar buf uc;
                 Some (Buffer.contents buf)
             | TMacro m -> Some ("\\" ^ m)
             | _ -> None)
           tokens)
    and count_words text =
      String.split_on_char ' ' text
      |> List.filter (fun s -> String.length s > 0)
      |> List.length
    in

    scan (Array.to_list tokens);

    let all_sections = List.rev !sections in
    let total = List.length all_sections in
    let max_d = List.fold_left (fun acc s -> max acc s.level) 0 all_sections in
    let total_words =
      List.fold_left (fun acc s -> acc + s.word_count) 0 all_sections
    in
    let avg =
      if total > 0 then float_of_int total_words /. float_of_int total else 0.0
    in

    {
      sections = all_sections;
      max_depth = max_d;
      total_sections = total;
      avg_section_length = avg;
    }
end

(** Math mode tracking and validation *)
module MathAnalyzer = struct
  type math_context = Inline | Display | Equation | Align | Gather

  type math_issue =
    | EmptyMath
    | NestedMath
    | UnclosedMath
    | InvalidCommand of string
    | MixedNotation (* Mixing LaTeX and plain TeX *)

  let analyze_math_mode tokens =
    let issues = ref [] in
    let math_depth = ref 0 in
    let current_context = ref None in

    let rec scan = function
      | [] -> ()
      | TChar (uc1, _) :: TChar (uc2, _) :: rest
        when Uchar.to_int uc1 = 0x24 && Uchar.to_int uc2 = 0x24 ->
          (* Display math $$ *)
          if !math_depth > 0 then issues := NestedMath :: !issues;
          math_depth := 1;
          current_context := Some Display;
          scan rest
      | TChar (uc, _) :: rest when Uchar.to_int uc = 0x24 ->
          (* Inline math $ *)
          if !math_depth > 0 then (
            math_depth := 0;
            current_context := None)
          else (
            math_depth := 1;
            current_context := Some Inline);
          scan rest
      | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
        when List.mem env [ "equation"; "align"; "gather"; "eqnarray" ] ->
          if !math_depth > 0 then issues := NestedMath :: !issues;
          math_depth := 1;
          current_context :=
            Some
              (match env with
              | "equation" -> Equation
              | "align" -> Align
              | "gather" -> Gather
              | _ -> Display);
          scan rest
      | TMacro "end" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
        when List.mem env [ "equation"; "align"; "gather"; "eqnarray" ] ->
          math_depth := 0;
          current_context := None;
          scan rest
      | _ :: rest -> scan rest
    in

    scan (Array.to_list tokens);

    if !math_depth > 0 then issues := UnclosedMath :: !issues;

    List.rev !issues
end

(** Cross-reference analysis *)
module CrossReferences = struct
  type ref_type =
    | Label of string
    | Ref of string
    | PageRef of string
    | Cite of string
    | FootnoteRef of int

  type ref_issue =
    | UndefinedReference of string
    | DuplicateLabel of string
    | UnusedLabel of string
    | ForwardReference of string * int (* distance in tokens *)

  let analyze_references tokens =
    let labels = Hashtbl.create 100 in
    let refs = Hashtbl.create 100 in
    let issues = ref [] in

    let rec scan pos = function
      | [] -> ()
      | TMacro "label" :: TGroupOpen :: rest ->
          let label_name, remaining = extract_label rest in
          if Hashtbl.mem labels label_name then
            issues := DuplicateLabel label_name :: !issues
          else Hashtbl.add labels label_name pos;
          scan (pos + 3) remaining
      | TMacro "ref" :: TGroupOpen :: rest
      | TMacro "pageref" :: TGroupOpen :: rest ->
          let ref_name, remaining = extract_label rest in
          Hashtbl.add refs ref_name pos;
          scan (pos + 3) remaining
      | TMacro "cite" :: TGroupOpen :: rest ->
          let cite_key, remaining = extract_label rest in
          (* Track citations separately *)
          scan (pos + 3) remaining
      | _ :: rest -> scan (pos + 1) rest
    and extract_label = function
      | TMacro name :: TGroupClose :: rest -> (name, rest)
      | TChar (uc, _) :: rest ->
          let rec collect acc = function
            | TGroupClose :: rest -> (String.concat "" (List.rev acc), rest)
            | TChar (uc, _) :: rest ->
                let buf = Buffer.create 4 in
                Buffer.add_utf_8_uchar buf uc;
                collect (Buffer.contents buf :: acc) rest
            | _ :: rest -> collect acc rest
            | [] -> ("", [])
          in
          let buf = Buffer.create 4 in
          Buffer.add_utf_8_uchar buf uc;
          collect [ Buffer.contents buf ] rest
      | _ -> ("", [])
    in

    scan 0 (Array.to_list tokens);

    (* Check for undefined references *)
    Hashtbl.iter
      (fun ref_name pos ->
        if not (Hashtbl.mem labels ref_name) then
          issues := UndefinedReference ref_name :: !issues)
      refs;

    (* Check for unused labels *)
    Hashtbl.iter
      (fun label_name _ ->
        if not (Hashtbl.mem refs label_name) then
          issues := UnusedLabel label_name :: !issues)
      labels;

    List.rev !issues
end

(** Main semantic analyzer *)
let create_context () =
  {
    document_class = None;
    packages = [];
    preamble_complete = false;
    current_section = None;
    section_depth = 0;
    in_math_mode = false;
    in_verbatim = false;
    environment_stack = [];
    labels = [];
    refs = [];
    citations = [];
    equation_count = 0;
    figure_count = 0;
    table_count = 0;
    footnote_count = 0;
    warnings = [];
    errors = [];
  }

let analyze_semantics context tokens =
  (* Analyze document structure *)
  let structure = DocumentStructure.analyze_structure tokens in

  (* Check math mode usage *)
  let math_issues = MathAnalyzer.analyze_math_mode tokens in

  (* Analyze cross-references *)
  let ref_issues = CrossReferences.analyze_references tokens in

  (* Update context with findings *)
  let warnings =
    List.map
      (function
        | MathAnalyzer.EmptyMath ->
            {
              level = Warning;
              message = "Empty math environment";
              location = Location.make 0 0;
              suggestion = Some "Remove empty math or add content";
            }
        | MathAnalyzer.MixedNotation ->
            {
              level = Info;
              message = "Mixed LaTeX and plain TeX notation";
              location = Location.make 0 0;
              suggestion = Some "Use consistent notation style";
            }
        | _ ->
            {
              level = Hint;
              message = "Semantic issue detected";
              location = Location.make 0 0;
              suggestion = None;
            })
      math_issues
  in

  let errors =
    List.map
      (function
        | CrossReferences.UndefinedReference name ->
            {
              severity = Major;
              message = Printf.sprintf "Undefined reference: %s" name;
              location = Location.make 0 0;
              fix =
                Some (Printf.sprintf "Add \\label{%s} before reference" name);
            }
        | CrossReferences.DuplicateLabel name ->
            {
              severity = Minor;
              message = Printf.sprintf "Duplicate label: %s" name;
              location = Location.make 0 0;
              fix = Some "Use unique label names";
            }
        | _ ->
            {
              severity = Minor;
              message = "Reference issue";
              location = Location.make 0 0;
              fix = None;
            })
      ref_issues
  in

  ( {
      context with
      warnings = context.warnings @ warnings;
      errors = context.errors @ errors;
    },
    structure )

(** Semantic validation entry point *)
let validate_document tokens =
  let context = create_context () in
  let updated_context, structure = analyze_semantics context tokens in

  (* Generate report *)
  let report =
    {|
=== SEMANTIC ANALYSIS REPORT ===

Document Structure:
  Total sections: %d
  Maximum depth: %d
  Average section length: %.1f words

Issues Found:
  Errors: %d
  Warnings: %d

%s
%s
|}
      structure.total_sections structure.max_depth structure.avg_section_length
      (List.length updated_context.errors)
      (List.length updated_context.warnings)
      (if updated_context.errors = [] then ""
       else
         "Errors:\n"
         ^ String.concat "\n"
             (List.map
                (fun e -> Printf.sprintf "  - %s" e.message)
                updated_context.errors))
      (if updated_context.warnings = [] then ""
       else
         "Warnings:\n"
         ^ String.concat "\n"
             (List.map
                (fun w -> Printf.sprintf "  - %s" w.message)
                updated_context.warnings))
  in

  (updated_context, report)
