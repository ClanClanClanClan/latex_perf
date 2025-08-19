(* PIPELINE CORE - UNIFIED TYPE SYSTEM FOR ENTIRE L0-L2-VALIDATION PIPELINE *)
(* This module defines the authoritative types that ALL components must use *)

(* Import existing data modules for compatibility *)
module Location = struct
  type t = { byte_start : int; byte_end : int }
  
  let length { byte_start; byte_end } = byte_end - byte_start
  
  let merge a b =
    if a.byte_end < b.byte_start || b.byte_end < a.byte_start then None
    else
      Some {
        byte_start = Int.min a.byte_start b.byte_start;
        byte_end   = Int.max a.byte_end   b.byte_end;
      }
  
  let make start_pos end_pos = 
    { byte_start = start_pos; byte_end = end_pos }
  
  let make_single pos = 
    { byte_start = pos; byte_end = pos + 1 }
  
  let pp fmt { byte_start; byte_end } =
    Format.fprintf fmt "(%d,%d)" byte_start byte_end
end

module Catcode = struct
  (** LaTeX character category codes - AUTHORITATIVE DEFINITION *)
  type t = 
    | Escape      (* 0: Starts commands like \ *)
    | BeginGroup  (* 1: Begin group { *)
    | EndGroup    (* 2: End group } *)
    | MathShift   (* 3: Math mode $ *)
    | AlignTab    (* 4: Alignment & *)
    | EndLine     (* 5: Line ending *)
    | Param       (* 6: Parameter # *)
    | Superscript (* 7: Superscript ^ *)
    | Subscript   (* 8: Subscript _ *)
    | Ignored     (* 9: Ignored characters *)
    | Space       (* 10: Space characters *)
    | Letter      (* 11: Letters a-z A-Z *)
    | Other       (* 12: Other characters *)
    | Active      (* 13: Active characters *)
    | Comment     (* 14: Comment % *)
    | Invalid     (* 15: Invalid characters *)

  let to_int = function
    | Escape -> 0 | BeginGroup -> 1 | EndGroup -> 2 | MathShift -> 3
    | AlignTab -> 4 | EndLine -> 5 | Param -> 6 | Superscript -> 7
    | Subscript -> 8 | Ignored -> 9 | Space -> 10 | Letter -> 11
    | Other -> 12 | Active -> 13 | Comment -> 14 | Invalid -> 15

  let to_string = function
    | Escape -> "Escape" | BeginGroup -> "BeginGroup" | EndGroup -> "EndGroup"
    | MathShift -> "MathShift" | AlignTab -> "AlignTab" | EndLine -> "EndLine"
    | Param -> "Param" | Superscript -> "Superscript" | Subscript -> "Subscript"
    | Ignored -> "Ignored" | Space -> "Space" | Letter -> "Letter"
    | Other -> "Other" | Active -> "Active" | Comment -> "Comment" | Invalid -> "Invalid"

  (* Standard TeX catcode lookup table *)
  let standard_catcode_table = 
    let tbl = Array.make 256 Other in
    tbl.(Char.code '\\') <- Escape;
    tbl.(Char.code '{') <- BeginGroup;
    tbl.(Char.code '}') <- EndGroup;
    tbl.(Char.code '$') <- MathShift;
    tbl.(Char.code '&') <- AlignTab;
    tbl.(Char.code '\r') <- EndLine;
    tbl.(Char.code '\n') <- EndLine;
    tbl.(Char.code '#') <- Param;
    tbl.(Char.code '^') <- Superscript;
    tbl.(Char.code '_') <- Subscript;
    tbl.(Char.code ' ') <- Space;
    tbl.(Char.code '\t') <- Space;
    tbl.(Char.code '%') <- Comment;
    
    (* Letters *)
    for i = Char.code 'a' to Char.code 'z' do
      tbl.(i) <- Letter
    done;
    for i = Char.code 'A' to Char.code 'Z' do
      tbl.(i) <- Letter
    done;
    
    tbl

  let lookup_catcode char_code =
    if char_code >= 0 && char_code < 256 then
      standard_catcode_table.(char_code)
    else
      Other
end

(* === UNIFIED TOKEN SYSTEM === *)

(** AUTHORITATIVE TOKEN TYPE - used by ALL pipeline components *)
type token =
  | TChar of Uchar.t * Catcode.t    (* Character with its catcode *)
  | TMacro of string                (* Macro name without backslash *)
  | TParam of int                   (* Parameter #1 .. #9 *)
  | TGroupOpen                      (* Begin group { *)
  | TGroupClose                     (* End group } *)
  | TMathShift                      (* Math mode shift $ (explicit) *)
  | TAlignTab                       (* Alignment tab & (explicit) *)
  | TEndLine                        (* End of line *)
  | TSpace                          (* Space *)
  | TComment of string              (* Comment content *)
  | TEOF                            (* End of file *)

(** Token with location information *)
type located_token = {
  token: token;
  location: Location.t;
  source_line: int;
  source_column: int;
}

(** Token classification for processing *)
type token_class = 
  | Character | Macro | Parameter | Grouping | MathMode | Alignment 
  | Whitespace | Comment | EndOfInput

let classify_token = function
  | TChar _ -> Character
  | TMacro _ -> Macro
  | TParam _ -> Parameter
  | TGroupOpen | TGroupClose -> Grouping
  | TMathShift -> MathMode
  | TAlignTab -> Alignment
  | TEndLine | TSpace -> Whitespace
  | TComment _ -> Comment
  | TEOF -> EndOfInput

(** Token to string conversion for debugging *)
let token_to_string = function
  | TChar (uchar, catcode) -> 
      let code = Uchar.to_int uchar in
      let char_str = if code >= 32 && code <= 126 then 
        Printf.sprintf "'%c'" (Char.chr code)
      else 
        Printf.sprintf "U+%04X" code 
      in
      Printf.sprintf "TChar(%s,%s)" char_str (Catcode.to_string catcode)
  | TMacro s -> Printf.sprintf "TMacro(%s)" s
  | TParam n -> Printf.sprintf "TParam(%d)" n
  | TGroupOpen -> "TGroupOpen"
  | TGroupClose -> "TGroupClose"
  | TMathShift -> "TMathShift"
  | TAlignTab -> "TAlignTab"
  | TEndLine -> "TEndLine"
  | TSpace -> "TSpace"
  | TComment s -> Printf.sprintf "TComment(%s)" (if String.length s > 20 then String.sub s 0 17 ^ "..." else s)
  | TEOF -> "TEOF"

let pp_located_token fmt tok =
  Format.fprintf fmt "@[%d:%d-%d %s@]" 
    tok.source_line tok.location.byte_start tok.location.byte_end 
    (token_to_string tok.token)

(** Convert between token representations *)
module TokenConversion = struct
  
  (* Convert our unified token to validation system compatible format *)
  let to_validation_token = function
    | TChar (uchar, catcode) -> (Uchar.to_int uchar, Catcode.to_int catcode)
    | TMacro name -> `Macro name
    | TParam n -> `Param n
    | TGroupOpen -> `GroupOpen
    | TGroupClose -> `GroupClose
    | TMathShift -> `MathShift
    | TAlignTab -> `AlignTab
    | TEndLine -> `EndLine
    | TSpace -> `Space
    | TComment _ -> `Comment
    | TEOF -> `EOF

  (* Convert from old validation format to unified format *)
  let from_validation_int_pair (unicode_val, catcode_int) =
    let uchar = Uchar.of_int unicode_val in
    let catcode = match catcode_int with
      | 0 -> Catcode.Escape | 1 -> BeginGroup | 2 -> EndGroup | 3 -> MathShift
      | 4 -> AlignTab | 5 -> EndLine | 6 -> Param | 7 -> Superscript
      | 8 -> Subscript | 9 -> Ignored | 10 -> Space | 11 -> Letter
      | 12 -> Other | 13 -> Active | 14 -> Comment | 15 -> Invalid
      | _ -> Other
    in
    TChar (uchar, catcode)

end

(* === PIPELINE STAGE INTERFACES === *)

(** Common result type for all pipeline stages *)
type ('success, 'error) stage_result = 
  | Success of 'success
  | Error of 'error

(** Performance metrics for pipeline stages *)
type stage_metrics = {
  stage_name: string;
  input_size: int;
  output_size: int;
  execution_time_ms: float;
  memory_used_kb: int;
  errors_encountered: int;
}

(** Pipeline stage interface - ALL stages must implement this *)
module type PipelineStage = sig
  type input
  type output  
  type error
  type options
  
  val stage_name : string
  val default_options : options
  
  val process : options -> input -> (output * stage_metrics, error) stage_result
  
  val validate_input : input -> bool
  val validate_output : output -> bool
end

(* === L0 LEXER INTERFACE === *)
module type L0_Lexer = sig
  include PipelineStage with 
    type input = string and 
    type output = located_token list and 
    type error = string

  val tokenize_string : ?options:options -> string -> (located_token list * stage_metrics, error) stage_result
end

(* === L1 EXPANDER INTERFACE === *)
module type L1_Expander = sig
  include PipelineStage with 
    type input = located_token list and 
    type output = located_token list and 
    type error = string

  type macro_def = {
    name: string;
    params: int;
    replacement: token list;
    is_builtin: bool;
  }

  val expand_tokens : ?options:options -> located_token list -> (located_token list * stage_metrics, error) stage_result
  val load_macro_catalog : string -> (macro_def list, error) stage_result
end

(* === L2 PARSER INTERFACE === *)
module type L2_Parser = sig
  type inline = 
    | Command of { name: string; args: string list }
    | Text of string
    | MathInline of inline list
    | Group of inline list

  type block = 
    | Section of { level: int; title: inline list; content: block list }
    | Environment of { name: string; body: block list }
    | Paragraph of inline list
    | MathDisplay of inline list

  type document = {
    preamble: block list;
    body: block list;
    metadata: (string * string) list;
  }

  include PipelineStage with 
    type input = located_token list and 
    type output = document and 
    type error = string

  val parse_tokens : ?options:options -> located_token list -> (document * stage_metrics, error) stage_result
end

(* === VALIDATION SYSTEM INTERFACE === *)
module type ValidationSystem = sig
  type issue = {
    rule_id: string;
    message: string;
    position: Location.t;
    suggestion: string option;
    confidence: float;
    severity: [`Error | `Warning | `Info];
    category: string;
  }

  type validation_metrics = {
    total_tokens: int;
    total_issues: int;
    execution_time_ms: float;
    rules_triggered: string list;
    false_positive_estimate: float;
  }

  include PipelineStage with 
    type input = located_token list and 
    type output = issue list * validation_metrics and 
    type error = string

  val run_validation : ?options:options -> located_token list -> (issue list * validation_metrics * stage_metrics, error) stage_result
  val get_available_rules : unit -> string list
  val get_rule_description : string -> string option
end

(* === UNIFIED PIPELINE ORCHESTRATOR === *)

module Pipeline = struct
  
  type pipeline_options = {
    l0_options: (module L0_Lexer).options option;
    l1_options: (module L1_Expander).options option;  
    l2_options: (module L2_Parser).options option;
    validation_options: (module ValidationSystem).options option;
    stop_on_error: bool;
    collect_metrics: bool;
  }

  type pipeline_result = {
    original_input: string;
    l0_result: located_token list option;
    l1_result: located_token list option;
    l2_result: (module L2_Parser).document option;
    validation_result: (module ValidationSystem).issue list option;
    total_time_ms: float;
    stage_metrics: stage_metrics list;
    success: bool;
    error_message: string option;
  }

  type pipeline_error = 
    | L0_Error of string * stage_metrics option
    | L1_Error of string * stage_metrics option  
    | L2_Error of string * stage_metrics option
    | Validation_Error of string * stage_metrics option
    | Configuration_Error of string

  let create_default_options () = {
    l0_options = None;
    l1_options = None;
    l2_options = None;
    validation_options = None;
    stop_on_error = true;
    collect_metrics = true;
  }

  (* This will be implemented once we have the actual stage implementations *)
  let run_pipeline 
      (l0_lexer : (module L0_Lexer))
      (l1_expander : (module L1_Expander))  
      (l2_parser : (module L2_Parser))
      (validation : (module ValidationSystem))
      ?(options = create_default_options ())
      (latex_input : string) : (pipeline_result, pipeline_error) stage_result =
    
    let start_time = Sys.time () in
    let metrics = ref [] in
    
    let module L0 = (val l0_lexer) in
    let module L1 = (val l1_expander) in
    let module L2 = (val l2_parser) in
    let module V = (val validation) in
    
    (* This is a skeleton - actual implementation will follow *)
    Error (Configuration_Error "Pipeline implementation pending - architecture complete")

end

(* === TESTING FRAMEWORK INTERFACE === *)

module Testing = struct
  
  type test_case = {
    name: string;
    description: string;
    input: string;
    expected_issues: string list;
    performance_target_ms: float;
    category: string;
  }

  type test_result = {
    test_name: string;
    success: bool;
    execution_time_ms: float;
    issues_found: int;
    expected_issues: int;
    performance_pass: bool;
    error_message: string option;
    details: string list;
  }

  type test_suite_result = {
    total_tests: int;
    passed_tests: int;
    failed_tests: int;
    pass_rate: float;
    total_time_ms: float;
    performance_failures: int;
    results: test_result list;
  }

  (* Test framework implementation will follow *)

end

(* === ERROR HANDLING AND LOGGING === *)

module ErrorHandling = struct
  
  type log_level = Debug | Info | Warning | Error | Critical
  
  type error_context = {
    stage: string;
    location: Location.t option;
    input_preview: string;
    stack_trace: string list;
  }

  type pipeline_error_details = {
    error_type: string;
    message: string;
    context: error_context;
    recoverable: bool;
    suggestions: string list;
  }

  (* Error handling implementation will follow *)

end