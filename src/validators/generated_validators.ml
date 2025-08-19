(* GENERATED VALIDATOR MODULE - DO NOT EDIT *)
(* Generated from specs/rules/rules_v3.yaml *)

open Printf

type validation_result = {
  rule_id: string;
  position: int;
  message: string;
  severity: [`Critical | `Warning | `Style | `Info];
}


(* TYPO-001: ASCII straight quotes (\" … \") must be curly quotes *)
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


(* TYPO-002: Double hyphen -- should be en‑dash – *)
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
            message = "Double hyphen should be en-dash (use \\\\textendash)";
            severity = `Warning;
          } :: !results
      | _ -> ()
    done;
    List.rev !results
end


(* TYPO-003: Triple hyphen --- should be em‑dash — *)
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
            message = "Triple hyphen should be em-dash (use \\\\textemdash)";
            severity = `Warning;
          } :: !results
      | _ -> ()
    done;
    List.rev !results
end


(* TYPO-004: TeX double back‑tick ``…'' not allowed; use opening curly quotes *)
module TYPO_004 = struct
  let id = "TYPO-004"
  let description = "TeX double back‑tick ``…'' not allowed; use opening curly quotes"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-004 validation *)
    (* Description: TeX double back‑tick ``…'' not allowed; use opening curly quotes *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: TeX double back‑tick ``…'' not allowed; use opening curly quotes";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-005: Ellipsis typed as three periods ...; use \\dots *)
module TYPO_005 = struct
  let id = "TYPO-005"
  let description = "Ellipsis typed as three periods ...; use \\dots"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-005 validation *)
    (* Description: Ellipsis typed as three periods ...; use \\dots *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Ellipsis typed as three periods ...; use \\dots";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-006: Tab character U+0009 forbidden *)
module TYPO_006 = struct
  let id = "TYPO-006"
  let description = "Tab character U+0009 forbidden"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-006 validation *)
    (* Description: Tab character U+0009 forbidden *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Tab character U+0009 forbidden";
        severity = `Info;
      } :: !results;
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
    (* TODO: Implement TYPO-007 validation *)
    (* Description: Trailing spaces at end of line *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Trailing spaces at end of line";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-008: Multiple consecutive blank lines (> 2) in source *)
module TYPO_008 = struct
  let id = "TYPO-008"
  let description = "Multiple consecutive blank lines (> 2) in source"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-008 validation *)
    (* Description: Multiple consecutive blank lines (> 2) in source *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Multiple consecutive blank lines (> 2) in source";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-009: Non‑breaking space ~ used incorrectly at line start *)
module TYPO_009 = struct
  let id = "TYPO-009"
  let description = "Non‑breaking space ~ used incorrectly at line start"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-009 validation *)
    (* Description: Non‑breaking space ~ used incorrectly at line start *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Non‑breaking space ~ used incorrectly at line start";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-010: Space before punctuation , . ; : ? ! *)
module TYPO_010 = struct
  let id = "TYPO-010"
  let description = "Space before punctuation , . ; : ? !"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-010 validation *)
    (* Description: Space before punctuation , . ; : ? ! *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Space before punctuation , . ; : ? !";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-011: Missing thin space (\\,) before differential d in integrals *)
module TYPO_011 = struct
  let id = "TYPO-011"
  let description = "Missing thin space (\\,) before differential d in integrals"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-011 validation *)
    (* Description: Missing thin space (\\,) before differential d in integrals *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Missing thin space (\\,) before differential d in integrals";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-012: Straight apostrophe ' used for minutes/feet; use ^\\prime or ′ *)
module TYPO_012 = struct
  let id = "TYPO-012"
  let description = "Straight apostrophe ' used for minutes/feet; use ^\\prime or ′"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-012 validation *)
    (* Description: Straight apostrophe ' used for minutes/feet; use ^\\prime or ′ *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Straight apostrophe ' used for minutes/feet; use ^\\prime or ′";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-013: ASCII back‑tick ` used as opening quote *)
module TYPO_013 = struct
  let id = "TYPO-013"
  let description = "ASCII back‑tick ` used as opening quote"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-013 validation *)
    (* Description: ASCII back‑tick ` used as opening quote *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: ASCII back‑tick ` used as opening quote";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-014: Space before percent sign \\% *)
module TYPO_014 = struct
  let id = "TYPO-014"
  let description = "Space before percent sign \\%"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-014 validation *)
    (* Description: Space before percent sign \\% *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Space before percent sign \\%";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-015: Double \\% in source; likely stray percent *)
module TYPO_015 = struct
  let id = "TYPO-015"
  let description = "Double \\% in source; likely stray percent"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-015 validation *)
    (* Description: Double \\% in source; likely stray percent *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Double \\% in source; likely stray percent";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-016: Non‑breaking space ~ missing before \\cite / \\ref *)
module TYPO_016 = struct
  let id = "TYPO-016"
  let description = "Non‑breaking space ~ missing before \\cite / \\ref"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-016 validation *)
    (* Description: Non‑breaking space ~ missing before \\cite / \\ref *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Non‑breaking space ~ missing before \\cite / \\ref";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-017: TeX accent commands (\\'{e}) in text; prefer UTF‑8 é *)
module TYPO_017 = struct
  let id = "TYPO-017"
  let description = "TeX accent commands (\\'{e}) in text; prefer UTF‑8 é"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-017 validation *)
    (* Description: TeX accent commands (\\'{e}) in text; prefer UTF‑8 é *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: TeX accent commands (\\'{e}) in text; prefer UTF‑8 é";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-018: Multiple consecutive spaces in text *)
module TYPO_018 = struct
  let id = "TYPO-018"
  let description = "Multiple consecutive spaces in text"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-018 validation *)
    (* Description: Multiple consecutive spaces in text *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Multiple consecutive spaces in text";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-019: Comma splice detected: missing conjunction after comma *)
module TYPO_019 = struct
  let id = "TYPO-019"
  let description = "Comma splice detected: missing conjunction after comma"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-019 validation *)
    (* Description: Comma splice detected: missing conjunction after comma *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Comma splice detected: missing conjunction after comma";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-020: Sentence without ending punctuation *)
module TYPO_020 = struct
  let id = "TYPO-020"
  let description = "Sentence without ending punctuation"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-020 validation *)
    (* Description: Sentence without ending punctuation *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Sentence without ending punctuation";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-021: Capital letter after ellipsis without space *)
module TYPO_021 = struct
  let id = "TYPO-021"
  let description = "Capital letter after ellipsis without space"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-021 validation *)
    (* Description: Capital letter after ellipsis without space *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Capital letter after ellipsis without space";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-022: Space before closing punctuation ) ] } *)
module TYPO_022 = struct
  let id = "TYPO-022"
  let description = "Space before closing punctuation ) ] }"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-022 validation *)
    (* Description: Space before closing punctuation ) ] } *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Space before closing punctuation ) ] }";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-023: ASCII ampersand & outside tabular env; use \\& *)
module TYPO_023 = struct
  let id = "TYPO-023"
  let description = "ASCII ampersand & outside tabular env; use \\&"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-023 validation *)
    (* Description: ASCII ampersand & outside tabular env; use \\& *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: ASCII ampersand & outside tabular env; use \\&";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-024: Dangling dash at line end *)
module TYPO_024 = struct
  let id = "TYPO-024"
  let description = "Dangling dash at line end"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-024 validation *)
    (* Description: Dangling dash at line end *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Dangling dash at line end";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-025: Space before en‑dash in number range *)
module TYPO_025 = struct
  let id = "TYPO-025"
  let description = "Space before en‑dash in number range"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-025 validation *)
    (* Description: Space before en‑dash in number range *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Space before en‑dash in number range";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-026: Wrong dash in page range – should use -- *)
module TYPO_026 = struct
  let id = "TYPO-026"
  let description = "Wrong dash in page range – should use --"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-026 validation *)
    (* Description: Wrong dash in page range – should use -- *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Wrong dash in page range – should use --";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-027: Multiple exclamation marks ‼ *)
module TYPO_027 = struct
  let id = "TYPO-027"
  let description = "Multiple exclamation marks ‼"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-027 validation *)
    (* Description: Multiple exclamation marks ‼ *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Multiple exclamation marks ‼";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-028: Use of ``$$'' display math delimiter *)
module TYPO_028 = struct
  let id = "TYPO-028"
  let description = "Use of ``$$'' display math delimiter"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-028 validation *)
    (* Description: Use of ``$$'' display math delimiter *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Use of ``$$'' display math delimiter";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-029: Non‑breaking space after \\ref missing *)
module TYPO_029 = struct
  let id = "TYPO-029"
  let description = "Non‑breaking space after \\ref missing"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-029 validation *)
    (* Description: Non‑breaking space after \\ref missing *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Non‑breaking space after \\ref missing";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-030: UK spelling inconsistency detected *)
module TYPO_030 = struct
  let id = "TYPO-030"
  let description = "UK spelling inconsistency detected"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-030 validation *)
    (* Description: UK spelling inconsistency detected *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: UK spelling inconsistency detected";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-031: American punctuation placement inside quotes *)
module TYPO_031 = struct
  let id = "TYPO-031"
  let description = "American punctuation placement inside quotes"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-031 validation *)
    (* Description: American punctuation placement inside quotes *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: American punctuation placement inside quotes";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-032: Comma before \\cite *)
module TYPO_032 = struct
  let id = "TYPO-032"
  let description = "Comma before \\cite"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-032 validation *)
    (* Description: Comma before \\cite *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Comma before \\cite";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-033: Abbreviation et.al without space *)
module TYPO_033 = struct
  let id = "TYPO-033"
  let description = "Abbreviation et.al without space"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-033 validation *)
    (* Description: Abbreviation et.al without space *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Abbreviation et.al without space";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-034: Spurious space before footnote command \\footnote *)
module TYPO_034 = struct
  let id = "TYPO-034"
  let description = "Spurious space before footnote command \\footnote"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-034 validation *)
    (* Description: Spurious space before footnote command \\footnote *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Spurious space before footnote command \\footnote";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-035: French punctuation requires NBSP before ; : ! ? *)
module TYPO_035 = struct
  let id = "TYPO-035"
  let description = "French punctuation requires NBSP before ; : ! ?"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-035 validation *)
    (* Description: French punctuation requires NBSP before ; : ! ? *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: French punctuation requires NBSP before ; : ! ?";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-036: Suspicious consecutive capitalised words (shouting) *)
module TYPO_036 = struct
  let id = "TYPO-036"
  let description = "Suspicious consecutive capitalised words (shouting)"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-036 validation *)
    (* Description: Suspicious consecutive capitalised words (shouting) *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Suspicious consecutive capitalised words (shouting)";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-037: Space before comma *)
module TYPO_037 = struct
  let id = "TYPO-037"
  let description = "Space before comma"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-037 validation *)
    (* Description: Space before comma *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Space before comma";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-038: E‑mail address not in \\href *)
module TYPO_038 = struct
  let id = "TYPO-038"
  let description = "E‑mail address not in \\href"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-038 validation *)
    (* Description: E‑mail address not in \\href *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: E‑mail address not in \\href";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-039: URL split across lines without \\url{} *)
module TYPO_039 = struct
  let id = "TYPO-039"
  let description = "URL split across lines without \\url{}"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-039 validation *)
    (* Description: URL split across lines without \\url{} *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: URL split across lines without \\url{}";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-040: Math in text mode $…$ exceeds 80 characters *)
module TYPO_040 = struct
  let id = "TYPO-040"
  let description = "Math in text mode $…$ exceeds 80 characters"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-040 validation *)
    (* Description: Math in text mode $…$ exceeds 80 characters *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Math in text mode $…$ exceeds 80 characters";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-041: Incorrect spacing around \\ldots *)
module TYPO_041 = struct
  let id = "TYPO-041"
  let description = "Incorrect spacing around \\ldots"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-041 validation *)
    (* Description: Incorrect spacing around \\ldots *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Incorrect spacing around \\ldots";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-042: Multiple consecutive question marks ?? *)
module TYPO_042 = struct
  let id = "TYPO-042"
  let description = "Multiple consecutive question marks ??"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-042 validation *)
    (* Description: Multiple consecutive question marks ?? *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Multiple consecutive question marks ??";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-043: Smart quotes inside verbatim detected *)
module TYPO_043 = struct
  let id = "TYPO-043"
  let description = "Smart quotes inside verbatim detected"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-043 validation *)
    (* Description: Smart quotes inside verbatim detected *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Smart quotes inside verbatim detected";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-044: Acronym not defined on first use *)
module TYPO_044 = struct
  let id = "TYPO-044"
  let description = "Acronym not defined on first use"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-044 validation *)
    (* Description: Acronym not defined on first use *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Acronym not defined on first use";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-045: Non‑ASCII punctuation in math mode (‘ ’ “ ”) *)
module TYPO_045 = struct
  let id = "TYPO-045"
  let description = "Non‑ASCII punctuation in math mode (‘ ’ “ ”)"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-045 validation *)
    (* Description: Non‑ASCII punctuation in math mode (‘ ’ “ ”) *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Non‑ASCII punctuation in math mode (‘ ’ “ ”)";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-046: Use of $begin:math:text$ … $end:math:text$ instead of $…$ *)
module TYPO_046 = struct
  let id = "TYPO-046"
  let description = "Use of $begin:math:text$ … $end:math:text$ instead of $…$"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-046 validation *)
    (* Description: Use of $begin:math:text$ … $end:math:text$ instead of $…$ *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Use of $begin:math:text$ … $end:math:text$ instead of $…$";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-047: Starred \\section* used where numbered section expected *)
module TYPO_047 = struct
  let id = "TYPO-047"
  let description = "Starred \\section* used where numbered section expected"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-047 validation *)
    (* Description: Starred \\section* used where numbered section expected *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Starred \\section* used where numbered section expected";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-048: En‑dash used as minus sign in text *)
module TYPO_048 = struct
  let id = "TYPO-048"
  let description = "En‑dash used as minus sign in text"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-048 validation *)
    (* Description: En‑dash used as minus sign in text *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: En‑dash used as minus sign in text";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-049: Space after opening quote *)
module TYPO_049 = struct
  let id = "TYPO-049"
  let description = "Space after opening quote"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-049 validation *)
    (* Description: Space after opening quote *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Space after opening quote";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-051: Figure space U+2009 used instead of \\thinspace macro *)
module TYPO_051 = struct
  let id = "TYPO-051"
  let description = "Figure space U+2009 used instead of \\thinspace macro"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-051 validation *)
    (* Description: Figure space U+2009 used instead of \\thinspace macro *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Figure space U+2009 used instead of \\thinspace macro";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-052: Unescaped < or > in text; use \\textless / \\textgreater *)
module TYPO_052 = struct
  let id = "TYPO-052"
  let description = "Unescaped < or > in text; use \\textless / \\textgreater"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-052 validation *)
    (* Description: Unescaped < or > in text; use \\textless / \\textgreater *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Unescaped < or > in text; use \\textless / \\textgreater";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-053: Unicode ⋯ (U+22EF) leader forbidden; use \\dots instead *)
module TYPO_053 = struct
  let id = "TYPO-053"
  let description = "Unicode ⋯ (U+22EF) leader forbidden; use \\dots instead"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-053 validation *)
    (* Description: Unicode ⋯ (U+22EF) leader forbidden; use \\dots instead *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Unicode ⋯ (U+22EF) leader forbidden; use \\dots instead";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-054: Hair‑space required after en‑dash in word–word ranges *)
module TYPO_054 = struct
  let id = "TYPO-054"
  let description = "Hair‑space required after en‑dash in word–word ranges"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-054 validation *)
    (* Description: Hair‑space required after en‑dash in word–word ranges *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Hair‑space required after en‑dash in word–word ranges";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-055: Consecutive thin‑spaces (\\,\\,) prohibited; collapse *)
module TYPO_055 = struct
  let id = "TYPO-055"
  let description = "Consecutive thin‑spaces (\\,\\,) prohibited; collapse"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-055 validation *)
    (* Description: Consecutive thin‑spaces (\\,\\,) prohibited; collapse *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Consecutive thin‑spaces (\\,\\,) prohibited; collapse";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-056: Legacy TeX accents present despite UTF‑8 input *)
module TYPO_056 = struct
  let id = "TYPO-056"
  let description = "Legacy TeX accents present despite UTF‑8 input"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-056 validation *)
    (* Description: Legacy TeX accents present despite UTF‑8 input *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Legacy TeX accents present despite UTF‑8 input";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-057: Missing thin‑space before °C/°F or \\si{\\celsius} *)
module TYPO_057 = struct
  let id = "TYPO-057"
  let description = "Missing thin‑space before °C/°F or \\si{\\celsius}"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-057 validation *)
    (* Description: Missing thin‑space before °C/°F or \\si{\\celsius} *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Missing thin‑space before °C/°F or \\si{\\celsius}";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-058: Greek homograph letters used in Latin words (ϲ,ɑ,ᴦ…) *)
module TYPO_058 = struct
  let id = "TYPO-058"
  let description = "Greek homograph letters used in Latin words (ϲ,ɑ,ᴦ…)"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-058 validation *)
    (* Description: Greek homograph letters used in Latin words (ϲ,ɑ,ᴦ…) *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Greek homograph letters used in Latin words (ϲ,ɑ,ᴦ…)";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-060: Smart quotes present inside \\lstlisting / verbatim environments *)
module TYPO_060 = struct
  let id = "TYPO-060"
  let description = "Smart quotes present inside \\lstlisting / verbatim environments"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-060 validation *)
    (* Description: Smart quotes present inside \\lstlisting / verbatim environments *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Smart quotes present inside \\lstlisting / verbatim environments";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-061: Unicode × (U+00D7) in text; prefer \\times via math mode *)
module TYPO_061 = struct
  let id = "TYPO-061"
  let description = "Unicode × (U+00D7) in text; prefer \\times via math mode"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-061 validation *)
    (* Description: Unicode × (U+00D7) in text; prefer \\times via math mode *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Unicode × (U+00D7) in text; prefer \\times via math mode";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-062: Literal backslash in text; use \\textbackslash *)
module TYPO_062 = struct
  let id = "TYPO-062"
  let description = "Literal backslash in text; use \\textbackslash"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-062 validation *)
    (* Description: Literal backslash in text; use \\textbackslash *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Literal backslash in text; use \\textbackslash";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* TYPO-063: Non‑breaking hyphen U+2011 found inside URL *)
module TYPO_063 = struct
  let id = "TYPO-063"
  let description = "Non‑breaking hyphen U+2011 found inside URL"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement TYPO-063 validation *)
    (* Description: Non‑breaking hyphen U+2011 found inside URL *)
    (* This is a placeholder implementation *)
    if Array.length tokens > 0 then
      results := {
        rule_id = id;
        position = 0;
        message = "Rule not yet implemented: Non‑breaking hyphen U+2011 found inside URL";
        severity = `Info;
      } :: !results;
    List.rev !results
end


(* SPC-001: Line longer than 120 characters *)
module SPC_001 = struct
  let id = "SPC-001"
  let description = "Line longer than 120 characters"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-001 validation *)
    (* Description: Line longer than 120 characters *)
    List.rev !results
end


(* SPC-002: Line containing only whitespace *)
module SPC_002 = struct
  let id = "SPC-002"
  let description = "Line containing only whitespace"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-002 validation *)
    (* Description: Line containing only whitespace *)
    List.rev !results
end


(* SPC-003: Hard tab precedes non‑tab text (mixed indent) *)
module SPC_003 = struct
  let id = "SPC-003"
  let description = "Hard tab precedes non‑tab text (mixed indent)"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-003 validation *)
    (* Description: Hard tab precedes non‑tab text (mixed indent) *)
    List.rev !results
end


(* SPC-004: Carriage return U+000D without LF *)
module SPC_004 = struct
  let id = "SPC-004"
  let description = "Carriage return U+000D without LF"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-004 validation *)
    (* Description: Carriage return U+000D without LF *)
    List.rev !results
end


(* SPC-005: Trailing tab at end of line *)
module SPC_005 = struct
  let id = "SPC-005"
  let description = "Trailing tab at end of line"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-005 validation *)
    (* Description: Trailing tab at end of line *)
    List.rev !results
end


(* SPC-006: Indentation mixes spaces and tabs *)
module SPC_006 = struct
  let id = "SPC-006"
  let description = "Indentation mixes spaces and tabs"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-006 validation *)
    (* Description: Indentation mixes spaces and tabs *)
    List.rev !results
end


(* SPC-007: Three or more consecutive blank lines *)
module SPC_007 = struct
  let id = "SPC-007"
  let description = "Three or more consecutive blank lines"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-007 validation *)
    (* Description: Three or more consecutive blank lines *)
    List.rev !results
end


(* SPC-008: Paragraph starts with whitespace *)
module SPC_008 = struct
  let id = "SPC-008"
  let description = "Paragraph starts with whitespace"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-008 validation *)
    (* Description: Paragraph starts with whitespace *)
    List.rev !results
end


(* SPC-009: Non‑breaking space ~ at line start *)
module SPC_009 = struct
  let id = "SPC-009"
  let description = "Non‑breaking space ~ at line start"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-009 validation *)
    (* Description: Non‑breaking space ~ at line start *)
    List.rev !results
end


(* SPC-010: Sentence spacing uses two spaces after period *)
module SPC_010 = struct
  let id = "SPC-010"
  let description = "Sentence spacing uses two spaces after period"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-010 validation *)
    (* Description: Sentence spacing uses two spaces after period *)
    List.rev !results
end


(* SPC-011: Space before newline inside $$…$$ display *)
module SPC_011 = struct
  let id = "SPC-011"
  let description = "Space before newline inside $$…$$ display"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-011 validation *)
    (* Description: Space before newline inside $$…$$ display *)
    List.rev !results
end


(* SPC-012: BOM not at file start *)
module SPC_012 = struct
  let id = "SPC-012"
  let description = "BOM not at file start"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-012 validation *)
    (* Description: BOM not at file start *)
    List.rev !results
end


(* SPC-013: Whitespace‑only paragraph *)
module SPC_013 = struct
  let id = "SPC-013"
  let description = "Whitespace‑only paragraph"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-013 validation *)
    (* Description: Whitespace‑only paragraph *)
    List.rev !results
end


(* SPC-014: Mixed LF and CRLF within paragraph *)
module SPC_014 = struct
  let id = "SPC-014"
  let description = "Mixed LF and CRLF within paragraph"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-014 validation *)
    (* Description: Mixed LF and CRLF within paragraph *)
    List.rev !results
end


(* SPC-015: Indentation exceeds 8 spaces *)
module SPC_015 = struct
  let id = "SPC-015"
  let description = "Indentation exceeds 8 spaces"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-015 validation *)
    (* Description: Indentation exceeds 8 spaces *)
    List.rev !results
end


(* SPC-016: Space before semicolon *)
module SPC_016 = struct
  let id = "SPC-016"
  let description = "Space before semicolon"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-016 validation *)
    (* Description: Space before semicolon *)
    List.rev !results
end


(* SPC-017: Missing thin space before units (e.g. 5 cm) *)
module SPC_017 = struct
  let id = "SPC-017"
  let description = "Missing thin space before units (e.g. 5 cm)"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-017 validation *)
    (* Description: Missing thin space before units (e.g. 5 cm) *)
    List.rev !results
end


(* SPC-018: No space after sentence‑ending period *)
module SPC_018 = struct
  let id = "SPC-018"
  let description = "No space after sentence‑ending period"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-018 validation *)
    (* Description: No space after sentence‑ending period *)
    List.rev !results
end


(* SPC-019: Trailing full‑width space U+3000 at line end *)
module SPC_019 = struct
  let id = "SPC-019"
  let description = "Trailing full‑width space U+3000 at line end"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-019 validation *)
    (* Description: Trailing full‑width space U+3000 at line end *)
    List.rev !results
end


(* SPC-020: Tab character inside math mode *)
module SPC_020 = struct
  let id = "SPC-020"
  let description = "Tab character inside math mode"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-020 validation *)
    (* Description: Tab character inside math mode *)
    List.rev !results
end


(* SPC-021: Space before colon *)
module SPC_021 = struct
  let id = "SPC-021"
  let description = "Space before colon"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-021 validation *)
    (* Description: Space before colon *)
    List.rev !results
end


(* SPC-022: Tab after bullet in \\itemize *)
module SPC_022 = struct
  let id = "SPC-022"
  let description = "Tab after bullet in \\itemize"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-022 validation *)
    (* Description: Tab after bullet in \\itemize *)
    List.rev !results
end


(* SPC-023: Hard space U+00A0 outside French punctuation context *)
module SPC_023 = struct
  let id = "SPC-023"
  let description = "Hard space U+00A0 outside French punctuation context"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-023 validation *)
    (* Description: Hard space U+00A0 outside French punctuation context *)
    List.rev !results
end


(* SPC-024: Leading spaces on blank line *)
module SPC_024 = struct
  let id = "SPC-024"
  let description = "Leading spaces on blank line"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-024 validation *)
    (* Description: Leading spaces on blank line *)
    List.rev !results
end


(* SPC-025: Space before ellipsis \\dots *)
module SPC_025 = struct
  let id = "SPC-025"
  let description = "Space before ellipsis \\dots"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-025 validation *)
    (* Description: Space before ellipsis \\dots *)
    List.rev !results
end


(* SPC-026: Mixed indentation width at same list depth *)
module SPC_026 = struct
  let id = "SPC-026"
  let description = "Mixed indentation width at same list depth"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-026 validation *)
    (* Description: Mixed indentation width at same list depth *)
    List.rev !results
end


(* SPC-027: Trailing whitespace inside \\url{} *)
module SPC_027 = struct
  let id = "SPC-027"
  let description = "Trailing whitespace inside \\url{}"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-027 validation *)
    (* Description: Trailing whitespace inside \\url{} *)
    List.rev !results
end


(* SPC-028: Multiple consecutive ~ NBSPs *)
module SPC_028 = struct
  let id = "SPC-028"
  let description = "Multiple consecutive ~ NBSPs"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-028 validation *)
    (* Description: Multiple consecutive ~ NBSPs *)
    List.rev !results
end


(* SPC-029: Indentation uses NBSP characters *)
module SPC_029 = struct
  let id = "SPC-029"
  let description = "Indentation uses NBSP characters"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-029 validation *)
    (* Description: Indentation uses NBSP characters *)
    List.rev !results
end


(* SPC-030: Line starts with full‑width space U+3000 *)
module SPC_030 = struct
  let id = "SPC-030"
  let description = "Line starts with full‑width space U+3000"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-030 validation *)
    (* Description: Line starts with full‑width space U+3000 *)
    List.rev !results
end


(* SPC-031: Three spaces after period *)
module SPC_031 = struct
  let id = "SPC-031"
  let description = "Three spaces after period"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-031 validation *)
    (* Description: Three spaces after period *)
    List.rev !results
end


(* SPC-032: Paragraph indented with mix of NBSP and space *)
module SPC_032 = struct
  let id = "SPC-032"
  let description = "Paragraph indented with mix of NBSP and space"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-032 validation *)
    (* Description: Paragraph indented with mix of NBSP and space *)
    List.rev !results
end


(* SPC-033: No‑break space before em‑dash in English text forbidden *)
module SPC_033 = struct
  let id = "SPC-033"
  let description = "No‑break space before em‑dash in English text forbidden"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-033 validation *)
    (* Description: No‑break space before em‑dash in English text forbidden *)
    List.rev !results
end


(* SPC-034: Thin‑space before en‑dash in command‑line flags removed *)
module SPC_034 = struct
  let id = "SPC-034"
  let description = "Thin‑space before en‑dash in command‑line flags removed"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-034 validation *)
    (* Description: Thin‑space before en‑dash in command‑line flags removed *)
    List.rev !results
end


(* SPC-035: Leading thin‑space U+2009 at start of line *)
module SPC_035 = struct
  let id = "SPC-035"
  let description = "Leading thin‑space U+2009 at start of line"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement SPC-035 validation *)
    (* Description: Leading thin‑space U+2009 at start of line *)
    List.rev !results
end


(* ENC-001: Non‑UTF‑8 byte sequence detected *)
module ENC_001 = struct
  let id = "ENC-001"
  let description = "Non‑UTF‑8 byte sequence detected"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-001 validation *)
    (* Description: Non‑UTF‑8 byte sequence detected *)
    List.rev !results
end


(* ENC-002: Byte‑order mark U+FEFF present in middle of file *)
module ENC_002 = struct
  let id = "ENC-002"
  let description = "Byte‑order mark U+FEFF present in middle of file"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-002 validation *)
    (* Description: Byte‑order mark U+FEFF present in middle of file *)
    List.rev !results
end


(* ENC-003: LATIN‑1 smart quotes detected *)
module ENC_003 = struct
  let id = "ENC-003"
  let description = "LATIN‑1 smart quotes detected"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-003 validation *)
    (* Description: LATIN‑1 smart quotes detected *)
    List.rev !results
end


(* ENC-004: Windows‑1252 characters (– — …) outside UTF‑8 *)
module ENC_004 = struct
  let id = "ENC-004"
  let description = "Windows‑1252 characters (– — …) outside UTF‑8"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-004 validation *)
    (* Description: Windows‑1252 characters (– — …) outside UTF‑8 *)
    List.rev !results
end


(* ENC-005: Invalid UTF‑8 continuation byte *)
module ENC_005 = struct
  let id = "ENC-005"
  let description = "Invalid UTF‑8 continuation byte"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-005 validation *)
    (* Description: Invalid UTF‑8 continuation byte *)
    List.rev !results
end


(* ENC-006: Overlong UTF‑8 encoding sequence *)
module ENC_006 = struct
  let id = "ENC-006"
  let description = "Overlong UTF‑8 encoding sequence"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-006 validation *)
    (* Description: Overlong UTF‑8 encoding sequence *)
    List.rev !results
end


(* ENC-007: Zero‑width space U+200B present *)
module ENC_007 = struct
  let id = "ENC-007"
  let description = "Zero‑width space U+200B present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-007 validation *)
    (* Description: Zero‑width space U+200B present *)
    List.rev !results
end


(* ENC-008: Private‑use codepoint detected *)
module ENC_008 = struct
  let id = "ENC-008"
  let description = "Private‑use codepoint detected"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-008 validation *)
    (* Description: Private‑use codepoint detected *)
    List.rev !results
end


(* ENC-009: Unpaired surrogate code unit *)
module ENC_009 = struct
  let id = "ENC-009"
  let description = "Unpaired surrogate code unit"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-009 validation *)
    (* Description: Unpaired surrogate code unit *)
    List.rev !results
end


(* ENC-010: Non‑canonical NFC form *)
module ENC_010 = struct
  let id = "ENC-010"
  let description = "Non‑canonical NFC form"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-010 validation *)
    (* Description: Non‑canonical NFC form *)
    List.rev !results
end


(* ENC-011: Byte sequence resembles MacRoman encoding *)
module ENC_011 = struct
  let id = "ENC-011"
  let description = "Byte sequence resembles MacRoman encoding"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-011 validation *)
    (* Description: Byte sequence resembles MacRoman encoding *)
    List.rev !results
end


(* ENC-012: C1 control characters U+0080–009F present *)
module ENC_012 = struct
  let id = "ENC-012"
  let description = "C1 control characters U+0080–009F present"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-012 validation *)
    (* Description: C1 control characters U+0080–009F present *)
    List.rev !results
end


(* ENC-013: Mixed CRLF and LF line endings *)
module ENC_013 = struct
  let id = "ENC-013"
  let description = "Mixed CRLF and LF line endings"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-013 validation *)
    (* Description: Mixed CRLF and LF line endings *)
    List.rev !results
end


(* ENC-014: UTF‑16 byte‑order mark present *)
module ENC_014 = struct
  let id = "ENC-014"
  let description = "UTF‑16 byte‑order mark present"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-014 validation *)
    (* Description: UTF‑16 byte‑order mark present *)
    List.rev !results
end


(* ENC-015: Non‑NFKC homoglyph character (Greek μ vs µ) *)
module ENC_015 = struct
  let id = "ENC-015"
  let description = "Non‑NFKC homoglyph character (Greek μ vs µ)"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-015 validation *)
    (* Description: Non‑NFKC homoglyph character (Greek μ vs µ) *)
    List.rev !results
end


(* ENC-016: Arabic numerals replaced by Unicode look‑alikes *)
module ENC_016 = struct
  let id = "ENC-016"
  let description = "Arabic numerals replaced by Unicode look‑alikes"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-016 validation *)
    (* Description: Arabic numerals replaced by Unicode look‑alikes *)
    List.rev !results
end


(* ENC-017: Soft hyphen U+00AD found in source *)
module ENC_017 = struct
  let id = "ENC-017"
  let description = "Soft hyphen U+00AD found in source"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-017 validation *)
    (* Description: Soft hyphen U+00AD found in source *)
    List.rev !results
end


(* ENC-018: Non‑breaking hyphen U+2011 present outside URLs *)
module ENC_018 = struct
  let id = "ENC-018"
  let description = "Non‑breaking hyphen U+2011 present outside URLs"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-018 validation *)
    (* Description: Non‑breaking hyphen U+2011 present outside URLs *)
    List.rev !results
end


(* ENC-019: Duplicate combining accents on same base glyph *)
module ENC_019 = struct
  let id = "ENC-019"
  let description = "Duplicate combining accents on same base glyph"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-019 validation *)
    (* Description: Duplicate combining accents on same base glyph *)
    List.rev !results
end


(* ENC-020: Invisible formatting mark U+200E/U+200F present *)
module ENC_020 = struct
  let id = "ENC-020"
  let description = "Invisible formatting mark U+200E/U+200F present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-020 validation *)
    (* Description: Invisible formatting mark U+200E/U+200F present *)
    List.rev !results
end


(* ENC-021: WORD JOINER U+2060 present *)
module ENC_021 = struct
  let id = "ENC-021"
  let description = "WORD JOINER U+2060 present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-021 validation *)
    (* Description: WORD JOINER U+2060 present *)
    List.rev !results
end


(* ENC-022: Interlinear annotation chars U+FFF9–FFFB detected *)
module ENC_022 = struct
  let id = "ENC-022"
  let description = "Interlinear annotation chars U+FFF9–FFFB detected"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-022 validation *)
    (* Description: Interlinear annotation chars U+FFF9–FFFB detected *)
    List.rev !results
end


(* ENC-023: NARROW NB‑SPACE U+202F outside French context *)
module ENC_023 = struct
  let id = "ENC-023"
  let description = "NARROW NB‑SPACE U+202F outside French context"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-023 validation *)
    (* Description: NARROW NB‑SPACE U+202F outside French context *)
    List.rev !results
end


(* ENC-024: Bidirectional embeddings U+202A–U+202E present *)
module ENC_024 = struct
  let id = "ENC-024"
  let description = "Bidirectional embeddings U+202A–U+202E present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ENC-024 validation *)
    (* Description: Bidirectional embeddings U+202A–U+202E present *)
    List.rev !results
end


(* CHAR-005: Control characters U+0000–001F present *)
module CHAR_005 = struct
  let id = "CHAR-005"
  let description = "Control characters U+0000–001F present"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-005 validation *)
    (* Description: Control characters U+0000–001F present *)
    List.rev !results
end


(* CHAR-006: Backspace U+0008 present *)
module CHAR_006 = struct
  let id = "CHAR-006"
  let description = "Backspace U+0008 present"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-006 validation *)
    (* Description: Backspace U+0008 present *)
    List.rev !results
end


(* CHAR-007: Bell/alert U+0007 present *)
module CHAR_007 = struct
  let id = "CHAR-007"
  let description = "Bell/alert U+0007 present"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-007 validation *)
    (* Description: Bell/alert U+0007 present *)
    List.rev !results
end


(* CHAR-008: Form feed U+000C present *)
module CHAR_008 = struct
  let id = "CHAR-008"
  let description = "Form feed U+000C present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-008 validation *)
    (* Description: Form feed U+000C present *)
    List.rev !results
end


(* CHAR-009: Delete U+007F present *)
module CHAR_009 = struct
  let id = "CHAR-009"
  let description = "Delete U+007F present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-009 validation *)
    (* Description: Delete U+007F present *)
    List.rev !results
end


(* CHAR-010: Right‑to‑left mark U+200F outside RTL context *)
module CHAR_010 = struct
  let id = "CHAR-010"
  let description = "Right‑to‑left mark U+200F outside RTL context"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-010 validation *)
    (* Description: Right‑to‑left mark U+200F outside RTL context *)
    List.rev !results
end


(* CHAR-011: Left‑to‑right mark U+200E unnecessary *)
module CHAR_011 = struct
  let id = "CHAR-011"
  let description = "Left‑to‑right mark U+200E unnecessary"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-011 validation *)
    (* Description: Left‑to‑right mark U+200E unnecessary *)
    List.rev !results
end


(* CHAR-012: Zero‑width joiner U+200D outside ligature context *)
module CHAR_012 = struct
  let id = "CHAR-012"
  let description = "Zero‑width joiner U+200D outside ligature context"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-012 validation *)
    (* Description: Zero‑width joiner U+200D outside ligature context *)
    List.rev !results
end


(* CHAR-013: Bidirectional isolate chars U+2066–U+2069 present *)
module CHAR_013 = struct
  let id = "CHAR-013"
  let description = "Bidirectional isolate chars U+2066–U+2069 present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-013 validation *)
    (* Description: Bidirectional isolate chars U+2066–U+2069 present *)
    List.rev !results
end


(* CHAR-014: Unicode replacement � found – decoding error *)
module CHAR_014 = struct
  let id = "CHAR-014"
  let description = "Unicode replacement � found – decoding error"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-014 validation *)
    (* Description: Unicode replacement � found – decoding error *)
    List.rev !results
end


(* CHAR-015: Emoji detected in source *)
module CHAR_015 = struct
  let id = "CHAR-015"
  let description = "Emoji detected in source"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-015 validation *)
    (* Description: Emoji detected in source *)
    List.rev !results
end


(* CHAR-016: Double‑width CJK punctuation in ASCII context *)
module CHAR_016 = struct
  let id = "CHAR-016"
  let description = "Double‑width CJK punctuation in ASCII context"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-016 validation *)
    (* Description: Double‑width CJK punctuation in ASCII context *)
    List.rev !results
end


(* CHAR-017: Full‑width Latin letters detected *)
module CHAR_017 = struct
  let id = "CHAR-017"
  let description = "Full‑width Latin letters detected"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-017 validation *)
    (* Description: Full‑width Latin letters detected *)
    List.rev !results
end


(* CHAR-018: Deprecated ligature ﬀ/ﬁ/ﬂ characters present *)
module CHAR_018 = struct
  let id = "CHAR-018"
  let description = "Deprecated ligature ﬀ/ﬁ/ﬂ characters present"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-018 validation *)
    (* Description: Deprecated ligature ﬀ/ﬁ/ﬂ characters present *)
    List.rev !results
end


(* CHAR-019: Unicode minus U+2212 in text mode *)
module CHAR_019 = struct
  let id = "CHAR-019"
  let description = "Unicode minus U+2212 in text mode"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-019 validation *)
    (* Description: Unicode minus U+2212 in text mode *)
    List.rev !results
end


(* CHAR-020: Sharp S ß in uppercase context – suggest SS *)
module CHAR_020 = struct
  let id = "CHAR-020"
  let description = "Sharp S ß in uppercase context – suggest SS"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-020 validation *)
    (* Description: Sharp S ß in uppercase context – suggest SS *)
    List.rev !results
end


(* CHAR-021: Zero‑width no‑break space U+FEFF inside paragraph *)
module CHAR_021 = struct
  let id = "CHAR-021"
  let description = "Zero‑width no‑break space U+FEFF inside paragraph"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-021 validation *)
    (* Description: Zero‑width no‑break space U+FEFF inside paragraph *)
    List.rev !results
end


(* CHAR-022: Deprecated tag characters U+E0000–E007F present *)
module CHAR_022 = struct
  let id = "CHAR-022"
  let description = "Deprecated tag characters U+E0000–E007F present"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CHAR-022 validation *)
    (* Description: Deprecated tag characters U+E0000–E007F present *)
    List.rev !results
end


(* VERB-001: \\verb delimiter reused inside same \\verb block *)
module VERB_001 = struct
  let id = "VERB-001"
  let description = "\\verb delimiter reused inside same \\verb block"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-001 validation *)
    (* Description: \\verb delimiter reused inside same \\verb block *)
    List.rev !results
end


(* VERB-002: Tab inside verbatim – discouraged *)
module VERB_002 = struct
  let id = "VERB-002"
  let description = "Tab inside verbatim – discouraged"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-002 validation *)
    (* Description: Tab inside verbatim – discouraged *)
    List.rev !results
end


(* VERB-003: Trailing spaces inside verbatim *)
module VERB_003 = struct
  let id = "VERB-003"
  let description = "Trailing spaces inside verbatim"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-003 validation *)
    (* Description: Trailing spaces inside verbatim *)
    List.rev !results
end


(* VERB-004: Non‑ASCII quotes inside verbatim *)
module VERB_004 = struct
  let id = "VERB-004"
  let description = "Non‑ASCII quotes inside verbatim"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-004 validation *)
    (* Description: Non‑ASCII quotes inside verbatim *)
    List.rev !results
end


(* VERB-005: Verbatim line > 120 characters *)
module VERB_005 = struct
  let id = "VERB-005"
  let description = "Verbatim line > 120 characters"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-005 validation *)
    (* Description: Verbatim line > 120 characters *)
    List.rev !results
end


(* VERB-006: Inline \\verb used for multiline content *)
module VERB_006 = struct
  let id = "VERB-006"
  let description = "Inline \\verb used for multiline content"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-006 validation *)
    (* Description: Inline \\verb used for multiline content *)
    List.rev !results
end


(* VERB-007: Nested verbatim environment *)
module VERB_007 = struct
  let id = "VERB-007"
  let description = "Nested verbatim environment"
  let severity = `Critical
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-007 validation *)
    (* Description: Nested verbatim environment *)
    List.rev !results
end


(* VERB-008: `lstlisting` uses language=none *)
module VERB_008 = struct
  let id = "VERB-008"
  let description = "`lstlisting` uses language=none"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-008 validation *)
    (* Description: `lstlisting` uses language=none *)
    List.rev !results
end


(* VERB-009: Missing caption in `minted` code block *)
module VERB_009 = struct
  let id = "VERB-009"
  let description = "Missing caption in `minted` code block"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-009 validation *)
    (* Description: Missing caption in `minted` code block *)
    List.rev !results
end


(* VERB-010: Inline code uses back‑ticks instead of \\verb *)
module VERB_010 = struct
  let id = "VERB-010"
  let description = "Inline code uses back‑ticks instead of \\verb"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-010 validation *)
    (* Description: Inline code uses back‑ticks instead of \\verb *)
    List.rev !results
end


(* VERB-011: Unknown `lstlisting` language *)
module VERB_011 = struct
  let id = "VERB-011"
  let description = "Unknown `lstlisting` language"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-011 validation *)
    (* Description: Unknown `lstlisting` language *)
    List.rev !results
end


(* VERB-012: `minted` block missing autogobble *)
module VERB_012 = struct
  let id = "VERB-012"
  let description = "`minted` block missing autogobble"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-012 validation *)
    (* Description: `minted` block missing autogobble *)
    List.rev !results
end


(* VERB-013: Code line > 120 glyphs *)
module VERB_013 = struct
  let id = "VERB-013"
  let description = "Code line > 120 glyphs"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-013 validation *)
    (* Description: Code line > 120 glyphs *)
    List.rev !results
end


(* VERB-015: Verbatim uses catcode changes instead of \\verb *)
module VERB_015 = struct
  let id = "VERB-015"
  let description = "Verbatim uses catcode changes instead of \\verb"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-015 validation *)
    (* Description: Verbatim uses catcode changes instead of \\verb *)
    List.rev !results
end


(* VERB-016: `minted` without `escapeinside` while containing back‑ticks *)
module VERB_016 = struct
  let id = "VERB-016"
  let description = "`minted` without `escapeinside` while containing back‑ticks"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-016 validation *)
    (* Description: `minted` without `escapeinside` while containing back‑ticks *)
    List.rev !results
end


(* VERB-017: `minted` lacks `linenos` in code block > 20 lines *)
module VERB_017 = struct
  let id = "VERB-017"
  let description = "`minted` lacks `linenos` in code block > 20 lines"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement VERB-017 validation *)
    (* Description: `minted` lacks `linenos` in code block > 20 lines *)
    List.rev !results
end


(* CMD-002: Command redefined with \\def instead of \\renewcommand *)
module CMD_002 = struct
  let id = "CMD-002"
  let description = "Command redefined with \\def instead of \\renewcommand"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-002 validation *)
    (* Description: Command redefined with \\def instead of \\renewcommand *)
    List.rev !results
end


(* CMD-004: CamelCase command names discouraged *)
module CMD_004 = struct
  let id = "CMD-004"
  let description = "CamelCase command names discouraged"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-004 validation *)
    (* Description: CamelCase command names discouraged *)
    List.rev !results
end


(* CMD-005: Single‑letter macro created (\\x) *)
module CMD_005 = struct
  let id = "CMD-005"
  let description = "Single‑letter macro created (\\x)"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-005 validation *)
    (* Description: Single‑letter macro created (\\x) *)
    List.rev !results
end


(* CMD-006: Macro defined inside document body *)
module CMD_006 = struct
  let id = "CMD-006"
  let description = "Macro defined inside document body"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-006 validation *)
    (* Description: Macro defined inside document body *)
    List.rev !results
end


(* CMD-008: Macro uses \\@ in name outside maketitle context *)
module CMD_008 = struct
  let id = "CMD-008"
  let description = "Macro uses \\@ in name outside maketitle context"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-008 validation *)
    (* Description: Macro uses \\@ in name outside maketitle context *)
    List.rev !results
end


(* CMD-009: Macro name contains digits *)
module CMD_009 = struct
  let id = "CMD-009"
  let description = "Macro name contains digits"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-009 validation *)
    (* Description: Macro name contains digits *)
    List.rev !results
end


(* CMD-011: Macro defined with \\def/\\edef in preamble without \\makeatletter guard *)
module CMD_011 = struct
  let id = "CMD-011"
  let description = "Macro defined with \\def/\\edef in preamble without \\makeatletter guard"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-011 validation *)
    (* Description: Macro defined with \\def/\\edef in preamble without \\makeatletter guard *)
    List.rev !results
end


(* CMD-013: \\def\\arraystretch declared inside document body *)
module CMD_013 = struct
  let id = "CMD-013"
  let description = "\\def\\arraystretch declared inside document body"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CMD-013 validation *)
    (* Description: \\def\\arraystretch declared inside document body *)
    List.rev !results
end


(* MATH-083: Unicode minus inside text mode *)
module MATH_083 = struct
  let id = "MATH-083"
  let description = "Unicode minus inside text mode"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement MATH-083 validation *)
    (* Description: Unicode minus inside text mode *)
    List.rev !results
end


(* CJK-001: Full‑width comma U+FF0C in ASCII context *)
module CJK_001 = struct
  let id = "CJK-001"
  let description = "Full‑width comma U+FF0C in ASCII context"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CJK-001 validation *)
    (* Description: Full‑width comma U+FF0C in ASCII context *)
    List.rev !results
end


(* CJK-002: Full‑width period U+FF0E in ASCII context *)
module CJK_002 = struct
  let id = "CJK-002"
  let description = "Full‑width period U+FF0E in ASCII context"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CJK-002 validation *)
    (* Description: Full‑width period U+FF0E in ASCII context *)
    List.rev !results
end


(* CJK-010: Half‑width CJK punctuation in full‑width context *)
module CJK_010 = struct
  let id = "CJK-010"
  let description = "Half‑width CJK punctuation in full‑width context"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CJK-010 validation *)
    (* Description: Half‑width CJK punctuation in full‑width context *)
    List.rev !results
end


(* CJK-014: Inter‑punct U+30FB outside CJK run *)
module CJK_014 = struct
  let id = "CJK-014"
  let description = "Inter‑punct U+30FB outside CJK run"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CJK-014 validation *)
    (* Description: Inter‑punct U+30FB outside CJK run *)
    List.rev !results
end


(* FR-007: FR‑BE: thin NB‑space before/after € sign required *)
module FR_007 = struct
  let id = "FR-007"
  let description = "FR‑BE: thin NB‑space before/after € sign required"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement FR-007 validation *)
    (* Description: FR‑BE: thin NB‑space before/after € sign required *)
    List.rev !results
end


(* FR-008: French: ligature œ/Œ mandatory in “cœur”, “œuvre”… *)
module FR_008 = struct
  let id = "FR-008"
  let description = "French: ligature œ/Œ mandatory in “cœur”, “œuvre”…"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement FR-008 validation *)
    (* Description: French: ligature œ/Œ mandatory in “cœur”, “œuvre”… *)
    List.rev !results
end


(* PT-003: pt‑PT: ordinal 1.º/1.ª must use º/ª, not superscript *)
module PT_003 = struct
  let id = "PT-003"
  let description = "pt‑PT: ordinal 1.º/1.ª must use º/ª, not superscript"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement PT-003 validation *)
    (* Description: pt‑PT: ordinal 1.º/1.ª must use º/ª, not superscript *)
    List.rev !results
end


(* RU-001: RU: NB‑space required before em‑dash *)
module RU_001 = struct
  let id = "RU-001"
  let description = "RU: NB‑space required before em‑dash"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement RU-001 validation *)
    (* Description: RU: NB‑space required before em‑dash *)
    List.rev !results
end


(* PL-001: PL: NB‑space before abbreviations “r.”, “nr”, “s.” *)
module PL_001 = struct
  let id = "PL-001"
  let description = "PL: NB‑space before abbreviations “r.”, “nr”, “s.”"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement PL-001 validation *)
    (* Description: PL: NB‑space before abbreviations “r.”, “nr”, “s.” *)
    List.rev !results
end


(* CS-001: CS/SK: thin NB‑space before °C forbidden *)
module CS_001 = struct
  let id = "CS-001"
  let description = "CS/SK: thin NB‑space before °C forbidden"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CS-001 validation *)
    (* Description: CS/SK: thin NB‑space before °C forbidden *)
    List.rev !results
end


(* CS-002: CS/SK: date format must be 30.\,1.\,2026 *)
module CS_002 = struct
  let id = "CS-002"
  let description = "CS/SK: date format must be 30.\,1.\,2026"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement CS-002 validation *)
    (* Description: CS/SK: date format must be 30.\,1.\,2026 *)
    List.rev !results
end


(* EL-001: Greek: oxia vs tonos normalisation *)
module EL_001 = struct
  let id = "EL-001"
  let description = "Greek: oxia vs tonos normalisation"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement EL-001 validation *)
    (* Description: Greek: oxia vs tonos normalisation *)
    List.rev !results
end


(* RO-001: RO: use Ș/ș (S‑comma) not Ş/ş (S‑cedilla) *)
module RO_001 = struct
  let id = "RO-001"
  let description = "RO: use Ș/ș (S‑comma) not Ş/ş (S‑cedilla)"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement RO-001 validation *)
    (* Description: RO: use Ș/ș (S‑comma) not Ş/ş (S‑cedilla) *)
    List.rev !results
end


(* AR-002: AR: ASCII hyphen in phone numbers—use \\arabicdash *)
module AR_002 = struct
  let id = "AR-002"
  let description = "AR: ASCII hyphen in phone numbers—use \\arabicdash"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement AR-002 validation *)
    (* Description: AR: ASCII hyphen in phone numbers—use \\arabicdash *)
    List.rev !results
end


(* HE-001: HE: apostrophe used instead of geresh U+05F3 *)
module HE_001 = struct
  let id = "HE-001"
  let description = "HE: apostrophe used instead of geresh U+05F3"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement HE-001 validation *)
    (* Description: HE: apostrophe used instead of geresh U+05F3 *)
    List.rev !results
end


(* ZH-001: ZH‑Hans: western '.' – use Chinese ‘。’ *)
module ZH_001 = struct
  let id = "ZH-001"
  let description = "ZH‑Hans: western '.' – use Chinese ‘。’"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement ZH-001 validation *)
    (* Description: ZH‑Hans: western '.' – use Chinese ‘。’ *)
    List.rev !results
end


(* JA-001: JA: half‑width katakana present—use full‑width *)
module JA_001 = struct
  let id = "JA-001"
  let description = "JA: half‑width katakana present—use full‑width"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement JA-001 validation *)
    (* Description: JA: half‑width katakana present—use full‑width *)
    List.rev !results
end


(* JA-002: JA: U+FF5E tilde normalise to wave‑dash U+301C *)
module JA_002 = struct
  let id = "JA-002"
  let description = "JA: U+FF5E tilde normalise to wave‑dash U+301C"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement JA-002 validation *)
    (* Description: JA: U+FF5E tilde normalise to wave‑dash U+301C *)
    List.rev !results
end


(* KO-001: KO: Old‑Hangul jamo outside scholarly context *)
module KO_001 = struct
  let id = "KO-001"
  let description = "KO: Old‑Hangul jamo outside scholarly context"
  let severity = `Warning
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement KO-001 validation *)
    (* Description: KO: Old‑Hangul jamo outside scholarly context *)
    List.rev !results
end


(* HI-001: HI: ZWJ/ZWNJ misuse next to ख् *)
module HI_001 = struct
  let id = "HI-001"
  let description = "HI: ZWJ/ZWNJ misuse next to ख्"
  let severity = `Info
  let precondition = "L0_Lexer"
  
  let validate tokens =
    let results = ref [] in
    (* TODO: Implement HI-001 validation *)
    (* Description: HI: ZWJ/ZWNJ misuse next to ख् *)
    List.rev !results
end


(* Validator Registry *)
module Registry = struct
  let all_validators = [
    (module TYPO_001);
    (module TYPO_002);
    (module TYPO_003);
    (module TYPO_004);
    (module TYPO_005);
    (module TYPO_006);
    (module TYPO_007);
    (module TYPO_008);
    (module TYPO_009);
    (module TYPO_010);
    (module TYPO_011);
    (module TYPO_012);
    (module TYPO_013);
    (module TYPO_014);
    (module TYPO_015);
    (module TYPO_016);
    (module TYPO_017);
    (module TYPO_018);
    (module TYPO_019);
    (module TYPO_020);
    (module TYPO_021);
    (module TYPO_022);
    (module TYPO_023);
    (module TYPO_024);
    (module TYPO_025);
    (module TYPO_026);
    (module TYPO_027);
    (module TYPO_028);
    (module TYPO_029);
    (module TYPO_030);
    (module TYPO_031);
    (module TYPO_032);
    (module TYPO_033);
    (module TYPO_034);
    (module TYPO_035);
    (module TYPO_036);
    (module TYPO_037);
    (module TYPO_038);
    (module TYPO_039);
    (module TYPO_040);
    (module TYPO_041);
    (module TYPO_042);
    (module TYPO_043);
    (module TYPO_044);
    (module TYPO_045);
    (module TYPO_046);
    (module TYPO_047);
    (module TYPO_048);
    (module TYPO_049);
    (module TYPO_051);
    (module TYPO_052);
    (module TYPO_053);
    (module TYPO_054);
    (module TYPO_055);
    (module TYPO_056);
    (module TYPO_057);
    (module TYPO_058);
    (module TYPO_060);
    (module TYPO_061);
    (module TYPO_062);
    (module TYPO_063);
    (module SPC_001);
    (module SPC_002);
    (module SPC_003);
    (module SPC_004);
    (module SPC_005);
    (module SPC_006);
    (module SPC_007);
    (module SPC_008);
    (module SPC_009);
    (module SPC_010);
    (module SPC_011);
    (module SPC_012);
    (module SPC_013);
    (module SPC_014);
    (module SPC_015);
    (module SPC_016);
    (module SPC_017);
    (module SPC_018);
    (module SPC_019);
    (module SPC_020);
    (module SPC_021);
    (module SPC_022);
    (module SPC_023);
    (module SPC_024);
    (module SPC_025);
    (module SPC_026);
    (module SPC_027);
    (module SPC_028);
    (module SPC_029);
    (module SPC_030);
    (module SPC_031);
    (module SPC_032);
    (module SPC_033);
    (module SPC_034);
    (module SPC_035);
    (module ENC_001);
    (module ENC_002);
    (module ENC_003);
    (module ENC_004);
    (module ENC_005);
    (module ENC_006);
    (module ENC_007);
    (module ENC_008);
    (module ENC_009);
    (module ENC_010);
    (module ENC_011);
    (module ENC_012);
    (module ENC_013);
    (module ENC_014);
    (module ENC_015);
    (module ENC_016);
    (module ENC_017);
    (module ENC_018);
    (module ENC_019);
    (module ENC_020);
    (module ENC_021);
    (module ENC_022);
    (module ENC_023);
    (module ENC_024);
    (module CHAR_005);
    (module CHAR_006);
    (module CHAR_007);
    (module CHAR_008);
    (module CHAR_009);
    (module CHAR_010);
    (module CHAR_011);
    (module CHAR_012);
    (module CHAR_013);
    (module CHAR_014);
    (module CHAR_015);
    (module CHAR_016);
    (module CHAR_017);
    (module CHAR_018);
    (module CHAR_019);
    (module CHAR_020);
    (module CHAR_021);
    (module CHAR_022);
    (module VERB_001);
    (module VERB_002);
    (module VERB_003);
    (module VERB_004);
    (module VERB_005);
    (module VERB_006);
    (module VERB_007);
    (module VERB_008);
    (module VERB_009);
    (module VERB_010);
    (module VERB_011);
    (module VERB_012);
    (module VERB_013);
    (module VERB_015);
    (module VERB_016);
    (module VERB_017);
    (module CMD_002);
    (module CMD_004);
    (module CMD_005);
    (module CMD_006);
    (module CMD_008);
    (module CMD_009);
    (module CMD_011);
    (module CMD_013);
    (module MATH_083);
    (module CJK_001);
    (module CJK_002);
    (module CJK_010);
    (module CJK_014);
    (module FR_007);
    (module FR_008);
    (module PT_003);
    (module RU_001);
    (module PL_001);
    (module CS_001);
    (module CS_002);
    (module EL_001);
    (module RO_001);
    (module AR_002);
    (module HE_001);
    (module ZH_001);
    (module JA_001);
    (module JA_002);
    (module KO_001);
    (module HI_001);
  ]
end
