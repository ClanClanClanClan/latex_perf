(* VALIDATOR CORE - PERFORMANCE FIXED VERSION *)
(* Array-based token stream for O(1) access instead of O(n) *)

open Printf

(* Token type from L0 lexer *)
type catcode = 
  | Escape | BeginGroup | EndGroup | MathShift | AlignTab 
  | EndLine | Param | Superscript | Subscript | Ignored 
  | Space | Letter | Other | Active | Comment | Invalid

type token =
  | TChar of Uchar.t * catcode
  | TMacro of string
  | TParam of int
  | TGroupOpen
  | TGroupClose
  | TEOF

type location = {
  line: int;
  column: int;
  offset: int;
}

type located_token = {
  token: token;
  location: location;
}

(* Document context for state tracking *)
type math_delimiter = 
  | Dollar 
  | DoubleDollar 
  | BeginMath 
  | BeginDisplayMath
  | BeginEquation

type environment = {
  name: string;
  location: location;
  args: string list;
}

type document_context = {
  (* Mode tracking *)
  mutable mode: [`Text | `Math | `DisplayMath | `Verbatim];
  mutable math_delim_stack: math_delimiter list;
  mutable env_stack: environment list;
  
  (* State flags *)
  mutable in_comment: bool;
  mutable in_preamble: bool;
  mutable after_backslash: bool;
  
  (* Document structure *)
  mutable section_level: int;
  mutable current_section: string option;
  
  (* Cross-references *)
  labels: (string, location) Hashtbl.t;
  refs: (string, location) Hashtbl.t;
  citations: (string, location) Hashtbl.t;
  
  (* Document metadata *)
  packages: string list ref;
  macros_defined: string list ref;
  bibliography_files: string list ref;
  
  (* Statistics *)
  mutable token_count: int;
  mutable line_count: int;
}

(* Create initial context *)
let create_context () = {
  mode = `Text;
  math_delim_stack = [];
  env_stack = [];
  in_comment = false;
  in_preamble = true;
  after_backslash = false;
  section_level = 0;
  current_section = None;
  labels = Hashtbl.create 100;
  refs = Hashtbl.create 100;
  citations = Hashtbl.create 100;
  packages = ref [];
  macros_defined = ref [];
  bibliography_files = ref [];
  token_count = 0;
  line_count = 1;
}

(* Confidence levels for issues *)
type confidence =
  | Certain    (* 0.9 - 1.0: Definite error *)
  | Likely     (* 0.7 - 0.9: Probable issue *)
  | Possible   (* 0.5 - 0.7: Potential issue *)
  | Unlikely   (* < 0.5: Probably false positive *)

let confidence_value = function
  | Certain -> 0.95
  | Likely -> 0.80
  | Possible -> 0.60
  | Unlikely -> 0.40

(* Validation issue with confidence *)
type validation_issue = {
  rule_id: string;
  severity: [`Error | `Warning | `Info];
  confidence: confidence;
  message: string;
  location: location;
  suggestion: string option;
  context_hint: string option;
}

(* FIXED: Array-based token stream for O(1) access *)
type token_stream = {
  tokens: located_token array;  (* ARRAY not list! *)
  mutable position: int;
  mutable saved_positions: int list;
}

let create_stream_from_list tokens = {
  tokens = Array.of_list tokens;
  position = 0;
  saved_positions = [];
}

let create_stream tokens_array = {
  tokens = tokens_array;
  position = 0;
  saved_positions = [];
}

(* O(1) access instead of O(n) *)
let current stream =
  if stream.position < Array.length stream.tokens then
    Some stream.tokens.(stream.position)
  else
    None

(* O(1) peek *)
let peek stream n =
  let pos = stream.position + n in
  if pos >= 0 && pos < Array.length stream.tokens then
    Some stream.tokens.(pos)
  else
    None

let advance stream =
  if stream.position < Array.length stream.tokens then
    stream.position <- stream.position + 1

(* Reset stream to beginning *)
let reset_stream stream =
  stream.position <- 0

(* Create independent copy of stream *)
let copy_stream stream = {
  tokens = stream.tokens;  (* Share the array, it's immutable *)
  position = 0;  (* Start from beginning *)
  saved_positions = [];
}

let save_position stream =
  stream.saved_positions <- stream.position :: stream.saved_positions

let restore_position stream =
  match stream.saved_positions with
  | [] -> failwith "No saved position"
  | pos :: rest ->
      stream.position <- pos;
      stream.saved_positions <- rest

let discard_saved_position stream =
  match stream.saved_positions with
  | [] -> ()
  | _ :: rest -> stream.saved_positions <- rest

(* Word boundary detection *)
let is_word_char = function
  | TChar (uc, Letter) -> true
  | TChar (uc, Other) ->
      let code = Uchar.to_int uc in
      (code >= 48 && code <= 57) ||    (* 0-9 *)
      (code >= 65 && code <= 90) ||    (* A-Z *)
      (code >= 97 && code <= 122)      (* a-z *)
  | _ -> false

let is_word_boundary_before stream =
  match peek stream (-1) with
  | None -> true
  | Some tok -> not (is_word_char tok.token)

let is_word_boundary_after stream =
  match peek stream 1 with
  | None -> true
  | Some tok -> not (is_word_char tok.token)

let is_at_word stream =
  is_word_boundary_before stream && 
  not (is_word_boundary_after stream)

(* Pattern matching helpers *)
let match_sequence stream patterns =
  save_position stream;
  let rec check_patterns = function
    | [] -> true
    | pattern :: rest ->
        match current stream with
        | None -> 
            restore_position stream;
            false
        | Some tok ->
            if pattern tok.token then begin
              advance stream;
              check_patterns rest
            end else begin
              restore_position stream;
              false
            end
  in
  if check_patterns patterns then begin
    discard_saved_position stream;
    true
  end else
    false

(* Extract text from token *)
let token_to_text = function
  | TChar (uc, _) -> 
      (try String.make 1 (Uchar.to_char uc)
       with _ -> "?")  (* Handle Unicode properly *)
  | TMacro name -> "\\" ^ name
  | TParam n -> "#" ^ string_of_int n
  | TGroupOpen -> "{"
  | TGroupClose -> "}"
  | TEOF -> ""

(* Check if in math mode *)
let in_math_mode context =
  context.mode = `Math || context.mode = `DisplayMath

(* Update context based on token *)
let update_context context tok =
  context.token_count <- context.token_count + 1;
  
  match tok.token with
  | TChar (_, MathShift) ->
      (* Toggle math mode *)
      if context.mode = `Text then begin
        context.mode <- `Math;
        context.math_delim_stack <- Dollar :: context.math_delim_stack
      end else if context.mode = `Math then begin
        match context.math_delim_stack with
        | Dollar :: rest ->
            context.mode <- `Text;
            context.math_delim_stack <- rest
        | _ -> ()
      end
      
  | TMacro "begin" -> context.after_backslash <- false
  | TMacro "end" -> context.after_backslash <- false
  | TMacro "documentclass" -> context.in_preamble <- true
  | TMacro "document" -> () (* Will be handled with begin/end *)
  | TMacro "usepackage" -> () (* Will extract package name *)
  | TMacro "label" -> () (* Will extract label *)
  | TMacro "ref" | TMacro "eqref" | TMacro "pageref" -> () (* Will extract ref *)
  | TMacro "cite" | TMacro "citep" | TMacro "citet" -> () (* Will extract citation *)
  
  | TChar (uc, EndLine) ->
      context.line_count <- context.line_count + 1;
      if context.in_comment then
        context.in_comment <- false
        
  | TChar (_, Comment) ->
      context.in_comment <- true
      
  | _ -> ()

(* Extract macro argument *)
let extract_braced_argument stream =
  match current stream with
  | Some { token = TGroupOpen; _ } ->
      advance stream;
      let rec collect acc depth =
        match current stream with
        | None -> None
        | Some { token = TGroupClose; _ } when depth = 1 ->
            advance stream;
            Some (List.rev acc)
        | Some { token = TGroupClose; _ } ->
            advance stream;
            collect (TGroupClose :: acc) (depth - 1)
        | Some { token = TGroupOpen; _ } ->
            advance stream;
            collect (TGroupOpen :: acc) (depth + 1)
        | Some { token; _ } ->
            advance stream;
            collect (token :: acc) depth
      in
      collect [] 1
  | _ -> None

(* Skip whitespace *)
let skip_whitespace stream =
  let rec skip () =
    match current stream with
    | Some { token = TChar (_, Space); _ }
    | Some { token = TChar (_, EndLine); _ } ->
        advance stream;
        skip ()
    | _ -> ()
  in
  skip ()

(* Base validator module type *)
module type VALIDATOR = sig
  val rule_id : string
  val name : string
  val description : string
  val default_severity : [`Error | `Warning | `Info]
  val validate : document_context -> token_stream -> validation_issue list
end

(* Helper to create issues *)
let make_issue ~rule_id ~severity ~confidence ~message ~location ?suggestion ?context_hint () =
  { rule_id; severity; confidence; message; location; suggestion; context_hint }

(* Convert confidence to numeric for filtering *)
let should_report confidence threshold =
  confidence_value confidence >= threshold

(* Backwards compatibility: create stream from list *)
(* Commented out to avoid name conflict - use create_stream_from_list explicitly *)
(* let create_stream tokens_list = create_stream_from_list tokens_list *)