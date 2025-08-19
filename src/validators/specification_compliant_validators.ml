(* SPECIFICATION-COMPLIANT VALIDATORS - Implementing Exact rules_v3.yaml Requirements *)
(* Simple, focused implementations that match specifications precisely *)

open Printf
open Validator_core

let max_tokens = 100000  (* Reasonable limit for safety *)
let max_time_ms = 1000.0  (* 1 second timeout *)

(* ===== TYPO VALIDATORS (L0_Lexer precondition) ===== *)

(* TYPO-001: ASCII straight quotes must be curly quotes [Error] *)
module SpecCompliantTYPO001 : VALIDATOR = struct
  let rule_id = "TYPO-001"
  let name = "ASCII straight quotes must be curly quotes"
  let description = "ASCII straight quotes (\" … \") must be curly quotes"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TChar (c, _); location } when Uchar.to_int c = 34 -> (* ASCII quote *)
          issues := (make_issue
            ~rule_id
            ~severity:`Error
            ~confidence:Certain
            ~message:"ASCII straight quotes must be curly quotes"
            ~location
            ~suggestion:"Use opening curly quotes or closing curly quotes instead of straight quotes"
            ()) :: !issues;
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    !issues
end

(* TYPO-002: Double hyphen -- should be en-dash [Warning] *)
module SpecCompliantTYPO002 : VALIDATOR = struct
  let rule_id = "TYPO-002"
  let name = "Double hyphen should be en-dash"
  let description = "Double hyphen -- should be en‑dash –"
  let default_severity = `Warning
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream, peek stream 1 with
      | Some { token = TChar (c1, _); location }, Some { token = TChar (c2, _); _ }
        when Uchar.to_int c1 = 45 && Uchar.to_int c2 = 45 -> (* -- *)
        
        (* Check it's not triple hyphen (handled by TYPO-003) *)
        let is_triple = match peek stream 2 with
          | Some { token = TChar (c3, _); _ } when Uchar.to_int c3 = 45 -> true
          | _ -> false
        in
        
        if not is_triple then
          issues := (make_issue
            ~rule_id
            ~severity:`Warning
            ~confidence:Certain
            ~message:"Double hyphen -- should be en-dash –"
            ~location
            ~suggestion:"Use en-dash – instead of --"
            ()) :: !issues;
        
        advance stream
        
      | _ -> advance stream
    done;
    !issues
end

(* TYPO-003: Triple hyphen --- should be em-dash [Warning] *)
module SpecCompliantTYPO003 : VALIDATOR = struct
  let rule_id = "TYPO-003"
  let name = "Triple hyphen should be em-dash"
  let description = "Triple hyphen --- should be em‑dash —"
  let default_severity = `Warning
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      (match current stream, peek stream 1, peek stream 2 with
      | Some { token = TChar (c1, _); location }, Some { token = TChar (c2, _); _ }, Some { token = TChar (c3, _); _ }
        when Uchar.to_int c1 = 45 && Uchar.to_int c2 = 45 && Uchar.to_int c3 = 45 -> (* --- *)
        
        issues := (make_issue
          ~rule_id
          ~severity:`Warning
          ~confidence:Certain
          ~message:"Triple hyphen --- should be em-dash —"
          ~location
          ~suggestion:"Use em-dash — instead of ---"
          ()) :: !issues;
        
        advance stream
        
      | _ -> advance stream)
    done;
    !issues
end

(* TYPO-005: Ellipsis typed as three periods [Warning] *)
module SpecCompliantTYPO005 : VALIDATOR = struct
  let rule_id = "TYPO-005"
  let name = "Ellipsis typed as periods"
  let description = "Ellipsis typed as three periods ...; use \\dots"
  let default_severity = `Warning
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      (match current stream, peek stream 1, peek stream 2 with
      | Some { token = TChar (c1, _); location }, Some { token = TChar (c2, _); _ }, Some { token = TChar (c3, _); _ }
        when Uchar.to_int c1 = 46 && Uchar.to_int c2 = 46 && Uchar.to_int c3 = 46 -> (* ... *)
        
        issues := (make_issue
          ~rule_id
          ~severity:`Warning
          ~confidence:Certain
          ~message:"Ellipsis typed as three periods; use \\dots"
          ~location
          ~suggestion:"Use \\dots or \\ldots for proper ellipsis"
          ()) :: !issues;
        
        advance stream
        
      | _ -> advance stream)
    done;
    !issues
end

(* TYPO-006: Tab character forbidden [Error] *)
module SpecCompliantTYPO006 : VALIDATOR = struct
  let rule_id = "TYPO-006"
  let name = "Tab character forbidden"
  let description = "Tab character U+0009 forbidden"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TChar (c, _); location } when Uchar.to_int c = 9 -> (* tab *)
          issues := (make_issue
            ~rule_id
            ~severity:`Error
            ~confidence:Certain
            ~message:"Tab character U+0009 forbidden"
            ~location
            ~suggestion:"Use spaces for indentation instead of tabs"
            ()) :: !issues;
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    !issues
end

(* TYPO-007: Trailing spaces [Info] *)
module SpecCompliantTYPO007 : VALIDATOR = struct
  let rule_id = "TYPO-007"
  let name = "Trailing spaces"
  let description = "Trailing spaces at end of line"
  let default_severity = `Info
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TChar (c, Space); location } when Uchar.to_int c = 32 -> (* space *)
          (* Check if this space is followed by end of line *)
          (match peek stream 1 with
          | Some { token = TChar (c2, EndLine); _ } when Uchar.to_int c2 = 10 -> (* newline *)
              issues := (make_issue
                ~rule_id
                ~severity:`Info
                ~confidence:Certain
                ~message:"Trailing spaces at end of line"
                ~location
                ~suggestion:"Remove trailing spaces"
                ()) :: !issues;
              advance stream
          | _ -> advance stream)
          
      | Some _ -> advance stream
      | None -> ()
    done;
    !issues
end

(* ===== DELIM VALIDATORS (L1_Expanded precondition) ===== *)

(* DELIM-001: Unmatched delimiters after expansion [Error] *)
module SpecCompliantDELIM001 : VALIDATOR = struct
  let rule_id = "DELIM-001"
  let name = "Unmatched delimiters after expansion"
  let description = "Unmatched delimiters { … } after macro expansion"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    let brace_stack = Stack.create () in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TChar (c, _); location } when Uchar.to_int c = 123 -> (* { *)
          Stack.push location brace_stack;
          advance stream
          
      | Some { token = TChar (c, _); location } when Uchar.to_int c = 125 -> (* } *)
          if Stack.is_empty brace_stack then
            issues := (make_issue
              ~rule_id:"DELIM-002"
              ~severity:`Error
              ~confidence:Certain
              ~message:"Extra closing } detected"
              ~location
              ~suggestion:"Remove extra closing brace or add matching opening brace"
              ()) :: !issues
          else
            ignore (Stack.pop brace_stack);
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    
    (* Check for unclosed braces *)
    Stack.iter (fun location ->
      issues := (make_issue
        ~rule_id
        ~severity:`Error
        ~confidence:Certain
        ~message:"Unmatched delimiters { … } after macro expansion"
        ~location
        ~suggestion:"Add matching closing brace"
        ()) :: !issues
    ) brace_stack;
    
    !issues
end

(* DELIM-002: Extra closing braces [Error] *)
module SpecCompliantDELIM002 : VALIDATOR = struct
  let rule_id = "DELIM-002"
  let name = "Extra closing braces"
  let description = "Extra closing } detected"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    let brace_stack = Stack.create () in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TChar (c, _); location } when Uchar.to_int c = 123 -> (* { *)
          Stack.push location brace_stack;
          advance stream
          
      | Some { token = TChar (c, _); location } when Uchar.to_int c = 125 -> (* } *)
          if Stack.is_empty brace_stack then
            issues := (make_issue
              ~rule_id
              ~severity:`Error
              ~confidence:Certain
              ~message:"Extra closing } detected"
              ~location
              ~suggestion:"Remove extra closing brace or add matching opening brace"
              ()) :: !issues
          else
            ignore (Stack.pop brace_stack);
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    
    !issues
end

(* DELIM-003: Unmatched \left without \right [Error] *)
module SpecCompliantDELIM003 : VALIDATOR = struct
  let rule_id = "DELIM-003"
  let name = "Unmatched \\left without \\right"
  let description = "Unmatched \\left without \\right"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    let left_stack = Stack.create () in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TMacro "left"; location } ->
          Stack.push location left_stack;
          advance stream
          
      | Some { token = TMacro "right"; location } ->
          if Stack.is_empty left_stack then
            issues := (make_issue
              ~rule_id:"DELIM-004"
              ~severity:`Error
              ~confidence:Certain
              ~message:"Unmatched \\right without \\left"
              ~location
              ~suggestion:"Add matching \\left before this \\right"
              ()) :: !issues
          else
            ignore (Stack.pop left_stack);
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    
    (* Check for unclosed \left *)
    Stack.iter (fun location ->
      issues := (make_issue
        ~rule_id
        ~severity:`Error
        ~confidence:Certain
        ~message:"Unmatched \\left without \\right"
        ~location
        ~suggestion:"Add matching \\right"
        ()) :: !issues
    ) left_stack;
    
    !issues
end

(* DELIM-004: Unmatched \right without \left [Error] *)
module SpecCompliantDELIM004 : VALIDATOR = struct
  let rule_id = "DELIM-004"
  let name = "Unmatched \\right without \\left"
  let description = "Unmatched \\right without \\left"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    let left_stack = Stack.create () in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TMacro "left"; location } ->
          Stack.push location left_stack;
          advance stream
          
      | Some { token = TMacro "right"; location } ->
          if Stack.is_empty left_stack then
            issues := (make_issue
              ~rule_id
              ~severity:`Error
              ~confidence:Certain
              ~message:"Unmatched \\right without \\left"
              ~location
              ~suggestion:"Add matching \\left before this \\right"
              ()) :: !issues
          else
            ignore (Stack.pop left_stack);
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    
    !issues
end

(* ===== SPC VALIDATORS (L0_Lexer precondition) ===== *)

(* SPC-001: Missing thin space before differential [Info] *)
module SpecCompliantSPC001 : VALIDATOR = struct
  let rule_id = "SPC-001"
  let name = "Missing thin space before differential"
  let description = "Missing thin space before differential dx, dy, etc."
  let default_severity = `Info
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      (match current stream, peek stream 1 with
      | Some { token = TChar (c1, Letter); location }, Some { token = TChar (c2, Letter); _ }
        when Uchar.to_int c1 = 100 && Uchar.to_int c2 >= 97 && Uchar.to_int c2 <= 122 -> (* d + letter *)
        
        (* Check if previous token is not a space *)
        (match peek stream (-1) with
        | Some { token = TChar (_, Space); _ } -> advance stream
        | Some _ ->
            issues := (make_issue
              ~rule_id
              ~severity:`Info
              ~confidence:Possible
              ~message:"Missing thin space before differential"
              ~location
              ~suggestion:"Use \\, before differential (e.g., f(x)\\,dx)"
              ()) :: !issues;
            advance stream
        | None -> advance stream)
        
      | _ -> advance stream)
    done;
    !issues
end

(* SPC-002: Space before punctuation [Info] *)
module SpecCompliantSPC002 : VALIDATOR = struct
  let rule_id = "SPC-002"
  let name = "Space before punctuation"
  let description = "Unwanted space before punctuation"
  let default_severity = `Info
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      (match current stream, peek stream 1 with
      | Some { token = TChar (c1, Space); location }, Some { token = TChar (c2, _); _ }
        when Uchar.to_int c1 = 32 && 
             (Uchar.to_int c2 = 44 || Uchar.to_int c2 = 46 || 
              Uchar.to_int c2 = 59 || Uchar.to_int c2 = 58) -> (* space + punctuation *)
        
        issues := (make_issue
          ~rule_id
          ~severity:`Info
          ~confidence:Likely
          ~message:"Unwanted space before punctuation"
          ~location
          ~suggestion:"Remove space before punctuation"
          ()) :: !issues;
        advance stream
        
      | _ -> advance stream)
    done;
    !issues
end

(* SPC-003: Non-breaking space usage [Warning] *)
module SpecCompliantSPC003 : VALIDATOR = struct
  let rule_id = "SPC-003"
  let name = "Non-breaking space usage"
  let description = "Missing non-breaking space in common contexts"
  let default_severity = `Warning
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      (* Check for common patterns that need non-breaking space *)
      match current stream with
      | Some { token = TChar (c, Letter); location } when Uchar.to_int c = 112 -> (* p *)
          (* Check for "p. " pattern (page reference) *)
          (match peek stream 1, peek stream 2 with
          | Some { token = TChar (c2, _); _ }, Some { token = TChar (c3, Space); _ }
            when Uchar.to_int c2 = 46 && Uchar.to_int c3 = 32 -> (* p. *)
            issues := (make_issue
              ~rule_id
              ~severity:`Warning
              ~confidence:Likely
              ~message:"Use non-breaking space after p."
              ~location
              ~suggestion:"Use p.~number instead of p. number"
              ()) :: !issues;
            advance stream
          | _ -> advance stream)
          
      | Some _ -> advance stream
      | None -> ()
    done;
    !issues
end

(* ===== CHAR VALIDATORS (L0_Lexer precondition) ===== *)

(* CHAR-001: Unicode validation [Error] *)
module SpecCompliantCHAR001 : VALIDATOR = struct
  let rule_id = "CHAR-001"
  let name = "Unicode validation"
  let description = "Invalid or problematic Unicode characters"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TChar (c, _); location } ->
          let code = Uchar.to_int c in
          (* Check for problematic Unicode ranges *)
          if code >= 0xFDD0 && code <= 0xFDEF then (* Non-characters *)
            issues := (make_issue
              ~rule_id
              ~severity:`Error
              ~confidence:Certain
              ~message:"Invalid Unicode non-character"
              ~location
              ~suggestion:"Remove or replace invalid Unicode character"
              ()) :: !issues;
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    !issues
end

(* CHAR-002: Character encoding [Error] *)
module SpecCompliantCHAR002 : VALIDATOR = struct
  let rule_id = "CHAR-002"
  let name = "Character encoding"
  let description = "Character encoding issues"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TChar (c, _); location } ->
          let code = Uchar.to_int c in
          (* Check for encoding issues like replacement character *)
          if code = 0xFFFD then (* Unicode replacement character *)
            issues := (make_issue
              ~rule_id
              ~severity:`Error
              ~confidence:Certain
              ~message:"Character encoding issue detected"
              ~location
              ~suggestion:"Check file encoding and fix corrupted characters"
              ()) :: !issues;
          advance stream
          
      | Some _ -> advance stream
      | None -> ()
    done;
    !issues
end

(* ===== REF VALIDATORS (L1_Expanded precondition) ===== *)

(* REF-001: Undefined \ref / \eqref label [Error] *)
module SpecCompliantREF001 : VALIDATOR = struct
  let rule_id = "REF-001"
  let name = "Undefined reference label"
  let description = "Undefined \\ref / \\eqref label after expansion"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    let labels = Hashtbl.create 100 in
    let references = ref [] in
    
    (* First pass: collect all labels *)
    save_position stream;
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TMacro "label"; _ } ->
          advance stream;
          skip_whitespace stream;
          (match extract_braced_argument stream with
          | Some tokens ->
              let label_name = String.concat "" (List.map token_to_text tokens) in
              Hashtbl.add labels label_name true
          | None -> ())
          
      | Some _ -> advance stream
      | None -> ()
    done;
    restore_position stream;
    
    (* Second pass: check all references *)
    tokens_processed := 0;
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TMacro cmd; location } when List.mem cmd ["ref"; "eqref"] ->
          advance stream;
          skip_whitespace stream;
          (match extract_braced_argument stream with
          | Some tokens ->
              let ref_name = String.concat "" (List.map token_to_text tokens) in
              if not (Hashtbl.mem labels ref_name) then
                issues := (make_issue
                  ~rule_id
                  ~severity:`Error
                  ~confidence:Certain
                  ~message:(sprintf "Undefined \\%s label: %s" cmd ref_name)
                  ~location
                  ~suggestion:"Define the label with \\label{...} or check spelling"
                  ()) :: !issues
          | None -> ())
          
      | Some _ -> advance stream
      | None -> ()
    done;
    
    !issues
end

(* REF-002: Duplicate label name [Error] *)
module SpecCompliantREF002 : VALIDATOR = struct
  let rule_id = "REF-002"
  let name = "Duplicate label name"
  let description = "Duplicate label name"
  let default_severity = `Error
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    let labels = Hashtbl.create 100 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TMacro "label"; _ } ->
          advance stream;
          skip_whitespace stream;
          (match extract_braced_argument stream with
          | Some tokens ->
              let label_name = String.concat "" (List.map token_to_text tokens) in
              if Hashtbl.mem labels label_name then
                issues := (make_issue
                  ~rule_id
                  ~severity:`Error
                  ~confidence:Certain
                  ~message:(sprintf "Duplicate label name: %s" label_name)
                  ~location:{ line = 0; column = 0; offset = 0 }
                  ~suggestion:"Use unique label names throughout document"
                  ()) :: !issues
              else
                Hashtbl.add labels label_name true
          | None -> ())
          
      | Some _ -> advance stream
      | None -> ()
    done;
    
    !issues
end

(* REF-003: Label contains spaces [Warning] *)
module SpecCompliantREF003 : VALIDATOR = struct
  let rule_id = "REF-003"
  let name = "Label contains spaces"
  let description = "Label contains spaces"
  let default_severity = `Warning
  
  let validate context stream =
    let issues = ref [] in
    let tokens_processed = ref 0 in
    
    while current stream <> None && !tokens_processed < max_tokens do
      incr tokens_processed;
      
      match current stream with
      | Some { token = TMacro "label"; location } ->
          advance stream;
          skip_whitespace stream;
          (match extract_braced_argument stream with
          | Some tokens ->
              let label_name = String.concat "" (List.map token_to_text tokens) in
              if String.contains label_name ' ' then
                issues := (make_issue
                  ~rule_id
                  ~severity:`Warning
                  ~confidence:Certain
                  ~message:"Label contains spaces"
                  ~location
                  ~suggestion:"Replace spaces with hyphens or underscores"
                  ()) :: !issues
          | None -> ())
          
      | Some _ -> advance stream
      | None -> ()
    done;
    
    !issues
end

(* Collection of specification-compliant validators *)
let specification_compliant_validators : (module VALIDATOR) list = [
  (* TYPO validators (L0_Lexer) *)
  (module SpecCompliantTYPO001);
  (module SpecCompliantTYPO002);
  (module SpecCompliantTYPO003);
  (module SpecCompliantTYPO005);
  (module SpecCompliantTYPO006);
  (module SpecCompliantTYPO007);
  
  (* SPC validators (L0_Lexer) *)
  (module SpecCompliantSPC001);
  (module SpecCompliantSPC002);
  (module SpecCompliantSPC003);
  
  (* CHAR validators (L0_Lexer) *)
  (module SpecCompliantCHAR001);
  (module SpecCompliantCHAR002);
  
  (* DELIM validators (L1_Expanded) *)
  (module SpecCompliantDELIM001);
  (module SpecCompliantDELIM002);
  (module SpecCompliantDELIM003);
  (module SpecCompliantDELIM004);
  
  (* REF validators (L1_Expanded) *)
  (module SpecCompliantREF001);
  (module SpecCompliantREF002);
  (module SpecCompliantREF003);
]

(* Week 1 Foundation validators (10 validators) *)
let week1_foundation_validators : (module VALIDATOR) list = [
  (module SpecCompliantTYPO001); (module SpecCompliantTYPO002); (module SpecCompliantTYPO003);
  (module SpecCompliantTYPO005); (module SpecCompliantTYPO006);
  (module SpecCompliantDELIM001); (module SpecCompliantDELIM003);
  (module SpecCompliantREF001); (module SpecCompliantREF002); (module SpecCompliantREF003);
]

(* Week 2 Expansion validators (8 additional validators) *)
let week2_expansion_validators : (module VALIDATOR) list = [
  (module SpecCompliantTYPO007);
  (module SpecCompliantSPC001); (module SpecCompliantSPC002); (module SpecCompliantSPC003);
  (module SpecCompliantCHAR001); (module SpecCompliantCHAR002);
  (module SpecCompliantDELIM002); (module SpecCompliantDELIM004);
]