(* SPECIFICATION-BASED VALIDATORS - v25_R1 Compliant Implementation *)
(* Implements validators according to exact specifications from rules_v3.yaml *)

open Printf

type validation_result = {
  rule_id: string;
  position: int;
  message: string;
  severity: [`Critical | `Warning | `Style | `Info];
}

type token_info = {
  kind: string;
  ascii_char: int option;
  position: int;
  text: string;
}

(* TYPO-001: ASCII straight quotes must be curly quotes *)
module TYPO_001 = struct
  let id = "TYPO-001"
  let description = "ASCII straight quotes (\" … \") must be curly quotes"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    Array.iteri (fun i token ->
      match token.ascii_char with
      | Some 34 -> (* ASCII quote character *)
          results := {
            rule_id = id;
            position = token.position;
            message = "ASCII straight quote should be curly quote";
            severity = `Critical;
          } :: !results
      | _ -> ()
    ) tokens;
    List.rev !results
end

(* TYPO-002: Double hyphen should be en-dash *)
module TYPO_002 = struct
  let id = "TYPO-002"
  let description = "Double hyphen -- should be en‑dash –"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    for i = 0 to Array.length tokens - 2 do
      let t1 = tokens.(i) in
      let t2 = tokens.(i + 1) in
      match (t1.ascii_char, t2.ascii_char) with
      | (Some 45, Some 45) -> (* Two consecutive hyphens *)
          results := {
            rule_id = id;
            position = t1.position;
            message = "Double hyphen should be en-dash (use \\textendash)";
            severity = `Warning;
          } :: !results
      | _ -> ()
    done;
    List.rev !results
end

(* TYPO-003: Triple hyphen should be em-dash *)
module TYPO_003 = struct
  let id = "TYPO-003"
  let description = "Triple hyphen --- should be em‑dash —"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    for i = 0 to Array.length tokens - 3 do
      let t1 = tokens.(i) in
      let t2 = tokens.(i + 1) in
      let t3 = tokens.(i + 2) in
      match (t1.ascii_char, t2.ascii_char, t3.ascii_char) with
      | (Some 45, Some 45, Some 45) -> (* Three consecutive hyphens *)
          results := {
            rule_id = id;
            position = t1.position;
            message = "Triple hyphen should be em-dash (use \\textemdash)";
            severity = `Warning;
          } :: !results
      | _ -> ()
    done;
    List.rev !results
end

(* TYPO-005: Ellipsis as three periods should use \dots *)
module TYPO_005 = struct
  let id = "TYPO-005"
  let description = "Ellipsis typed as three periods ...; use \\dots"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    for i = 0 to Array.length tokens - 3 do
      let t1 = tokens.(i) in
      let t2 = tokens.(i + 1) in
      let t3 = tokens.(i + 2) in
      match (t1.ascii_char, t2.ascii_char, t3.ascii_char) with
      | (Some 46, Some 46, Some 46) -> (* Three consecutive periods *)
          results := {
            rule_id = id;
            position = t1.position;
            message = "Three periods should be ellipsis (use \\dots or \\ldots)";
            severity = `Warning;
          } :: !results
      | _ -> ()
    done;
    List.rev !results
end

(* TYPO-006: Tab character forbidden *)
module TYPO_006 = struct
  let id = "TYPO-006"
  let description = "Tab character U+0009 forbidden"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    Array.iteri (fun i token ->
      match token.ascii_char with
      | Some 9 -> (* Tab character *)
          results := {
            rule_id = id;
            position = token.position;
            message = "Tab character (U+0009) is forbidden; use spaces";
            severity = `Critical;
          } :: !results
      | _ -> ()
    ) tokens;
    List.rev !results
end

(* TYPO-007: Trailing spaces at end of line *)
module TYPO_007 = struct
  let id = "TYPO-007"
  let description = "Trailing spaces at end of line"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    for i = 0 to Array.length tokens - 2 do
      let current = tokens.(i) in
      let next = tokens.(i + 1) in
      (* Space followed by newline *)
      if current.ascii_char = Some 32 && next.ascii_char = Some 10 then
        results := {
          rule_id = id;
          position = current.position;
          message = "Trailing space at end of line";
          severity = `Info;
        } :: !results
    done;
    List.rev !results
end

(* TYPO-010: Space before punctuation *)
module TYPO_010 = struct
  let id = "TYPO-010"
  let description = "Space before punctuation , . ; : ? !"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let is_punctuation = function
    | 44 | 46 | 59 | 58 | 63 | 33 -> true (* , . ; : ? ! *)
    | _ -> false
  
  let validate tokens =
    let results = ref [] in
    for i = 0 to Array.length tokens - 2 do
      let space = tokens.(i) in
      let punct = tokens.(i + 1) in
      match (space.ascii_char, punct.ascii_char) with
      | (Some 32, Some p) when is_punctuation p ->
          let punct_char = Char.chr p in
          results := {
            rule_id = id;
            position = space.position;
            message = sprintf "Unnecessary space before punctuation '%c'" punct_char;
            severity = `Info;
          } :: !results
      | _ -> ()
    done;
    List.rev !results
end

(* TYPO-018: Multiple consecutive spaces *)
module TYPO_018 = struct
  let id = "TYPO-018"
  let description = "Multiple consecutive spaces in text"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    let space_count = ref 0 in
    let space_start = ref (-1) in
    
    for i = 0 to Array.length tokens - 1 do
      let token = tokens.(i) in
      if token.ascii_char = Some 32 then begin
        if !space_count = 0 then space_start := token.position;
        incr space_count
      end else begin
        if !space_count > 1 then
          results := {
            rule_id = id;
            position = !space_start;
            message = sprintf "%d consecutive spaces found" !space_count;
            severity = `Info;
          } :: !results;
        space_count := 0
      end
    done;
    List.rev !results
end

(* DELIM-001: Unmatched closing brace *)
module DELIM_001 = struct
  let id = "DELIM-001"
  let description = "Unmatched closing brace }"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    let brace_stack = ref [] in
    
    Array.iter (fun token ->
      match token.ascii_char with
      | Some 123 -> (* { *)
          brace_stack := token.position :: !brace_stack
      | Some 125 -> (* } *)
          if !brace_stack = [] then
            results := {
              rule_id = id;
              position = token.position;
              message = "Unmatched closing brace }";
              severity = `Critical;
            } :: !results
          else
            brace_stack := List.tl !brace_stack
      | _ -> ()
    ) tokens;
    List.rev !results
end

(* DELIM-002: Unclosed opening brace *)
module DELIM_002 = struct
  let id = "DELIM-002"
  let description = "Unclosed opening brace {"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    let brace_stack = ref [] in
    
    Array.iter (fun token ->
      match token.ascii_char with
      | Some 123 -> (* { *)
          brace_stack := token.position :: !brace_stack
      | Some 125 -> (* } *)
          if !brace_stack <> [] then
            brace_stack := List.tl !brace_stack
      | _ -> ()
    ) tokens;
    
    (* Any remaining opening braces are unclosed *)
    List.iter (fun pos ->
      results := {
        rule_id = id;
        position = pos;
        message = "Unclosed opening brace {";
        severity = `Critical;
      } :: !results
    ) !brace_stack;
    List.rev !results
end

(* Registry of all implemented validators *)
module Registry = struct
  let all_validators = [
    ("TYPO-001", TYPO_001.validate);
    ("TYPO-002", TYPO_002.validate);
    ("TYPO-003", TYPO_003.validate);
    ("TYPO-005", TYPO_005.validate);
    ("TYPO-006", TYPO_006.validate);
    ("TYPO-007", TYPO_007.validate);
    ("TYPO-010", TYPO_010.validate);
    ("TYPO-018", TYPO_018.validate);
    ("DELIM-001", DELIM_001.validate);
    ("DELIM-002", DELIM_002.validate);
  ]
  
  let count = List.length all_validators
  
  let validate_all tokens =
    let all_results = ref [] in
    List.iter (fun (rule_id, validate_fn) ->
      let results = validate_fn tokens in
      all_results := results @ !all_results
    ) all_validators;
    List.rev !all_results
end

(* Test framework *)
module Test = struct
  let create_test_token ascii pos text =
    {
      kind = "char";
      ascii_char = Some ascii;
      position = pos;
      text = text;
    }
  
  let test_typo_001 () =
    let tokens = [|
      create_test_token 34 0 "\"";  (* ASCII quote *)
      create_test_token 97 1 "a";   (* letter a *)
      create_test_token 34 2 "\"";  (* ASCII quote *)
    |] in
    let results = TYPO_001.validate tokens in
    printf "TYPO-001 test: Found %d issues\n" (List.length results);
    List.iter (fun r -> printf "  %s at pos %d: %s\n" r.rule_id r.position r.message) results
  
  let test_typo_002 () =
    let tokens = [|
      create_test_token 45 0 "-";   (* hyphen *)
      create_test_token 45 1 "-";   (* hyphen *)
    |] in
    let results = TYPO_002.validate tokens in
    printf "TYPO-002 test: Found %d issues\n" (List.length results);
    List.iter (fun r -> printf "  %s at pos %d: %s\n" r.rule_id r.position r.message) results
  
  let test_typo_005 () =
    let tokens = [|
      create_test_token 46 0 ".";   (* period *)
      create_test_token 46 1 ".";   (* period *)
      create_test_token 46 2 ".";   (* period *)
    |] in
    let results = TYPO_005.validate tokens in
    printf "TYPO-005 test: Found %d issues\n" (List.length results);
    List.iter (fun r -> printf "  %s at pos %d: %s\n" r.rule_id r.position r.message) results
  
  let test_all () =
    printf "=== SPECIFICATION-BASED VALIDATOR TESTS ===\n";
    printf "Implementing %d validators according to rules_v3.yaml\n\n" Registry.count;
    
    test_typo_001 ();
    test_typo_002 ();
    test_typo_005 ();
    
    printf "\n=== COMPREHENSIVE TEST ===\n";
    let mixed_tokens = [|
      create_test_token 34 0 "\"";   (* ASCII quote - TYPO-001 *)
      create_test_token 45 1 "-";    (* hyphen *)
      create_test_token 45 2 "-";    (* hyphen - TYPO-002 *)
      create_test_token 32 3 " ";    (* space *)
      create_test_token 46 4 ".";    (* period - TYPO-010 *)
      create_test_token 9  5 "\t";   (* tab - TYPO-006 *)
    |] in
    
    let all_results = Registry.validate_all mixed_tokens in
    printf "Found %d total validation issues:\n" (List.length all_results);
    List.iter (fun r ->
      let severity_str = match r.severity with
        | `Critical -> "CRITICAL"
        | `Warning -> "WARNING"
        | `Info -> "INFO"
        | `Style -> "STYLE"
      in
      printf "  [%s] %s at pos %d: %s\n" severity_str r.rule_id r.position r.message
    ) all_results
end

(* Main execution *)
let () =
  Test.test_all ()