(* Mathematical Notation Validation Rules - LaTeX Perfectionist v25 *)
(* Rules for proper mathematical typesetting and notation *)

open Data.Location
open Data.Catcode
open Data.Chunk
open Data.Dlist
open Lexer_v25

type validation_issue = {
  rule_id: string;
  message: string;
  location: Location.t;
  suggestion: string option;
  confidence: float;
}

type rule_severity = Info | Warning | Error

type validation_rule = {
  id: string;
  name: string;
  description: string;
  severity: rule_severity;
  category: string;
  check: token array -> validation_issue list;
}

(* Helper functions *)
let is_math_delimiter = function
  | TChar (uc, _) -> Uchar.to_int uc = 0x24 (* $ *)
  | _ -> false

let is_macro name = function
  | TMacro m -> m = name
  | _ -> false

(** Math mode detection and tracking *)
module MathMode = struct
  type math_state = {
    in_math: bool;
    math_level: int;
    display_math: bool;
  }
  
  let initial_state = { in_math = false; math_level = 0; display_math = false }
  
  let update_state state = function
    | TChar (uc, _) when Uchar.to_int uc = 0x24 ->
        if state.in_math then
          { state with in_math = false; math_level = 0; display_math = false }
        else
          { state with in_math = true; math_level = 1; display_math = false }
    | TMacro "begin" -> 
        (* Handle math environments like equation, align, etc. *)
        { state with in_math = true; math_level = 1; display_math = true }
    | TMacro "end" -> state
    | _ -> state
  
  let scan_with_math_state tokens f =
    let state = ref initial_state in
    let results = ref [] in
    Array.iteri (fun i tok ->
      state := update_state !state tok;
      match f i tok !state with
      | Some result -> results := result :: !results
      | None -> ()
    ) tokens;
    List.rev !results
end

(** Function and operator rules *)
module FunctionRules = struct
  
  (* Rule: Use proper function commands *)
  let proper_functions = {
    id = "MATH-001";
    name = "proper_functions";
    description = "Use \\sin, \\cos, etc. instead of italicized text";
    severity = Warning;
    category = "math";
    check = fun tokens ->
      let math_functions = [
        "sin"; "cos"; "tan"; "sec"; "csc"; "cot";
        "sinh"; "cosh"; "tanh"; "sech"; "csch"; "coth";
        "arcsin"; "arccos"; "arctan"; "arcsec"; "arccsc"; "arccot";
        "log"; "ln"; "lg"; "exp";
        "min"; "max"; "sup"; "inf"; "lim"; "limsup"; "liminf";
        "det"; "dim"; "deg"; "gcd"; "ker"; "hom";
      ] in
      
      MathMode.scan_with_math_state tokens (fun i tok state ->
        if state.MathMode.in_math then
          match tok with
          | TMacro name when List.mem name math_functions ->
              (* This is correct - function is properly declared *)
              None
          | _ -> 
              (* Check for letter sequences that might be functions *)
              let check_sequence start_i =
                let rec collect_chars acc j =
                  if j >= Array.length tokens then (acc, j)
                  else match tokens.(j) with
                  | TChar (uc, _) -> 
                      let c = Uchar.to_int uc in
                      if (c >= 97 && c <= 122) then (* a-z *)
                        let char_str = String.make 1 (Char.chr c) in
                        collect_chars (acc ^ char_str) (j + 1)
                      else (acc, j)
                  | _ -> (acc, j)
                in
                collect_chars "" start_i
              in
              
              let (word, _) = check_sequence i in
              if List.mem word math_functions && String.length word > 2 then
                Some {
                  rule_id = "MATH-001";
                  message = Printf.sprintf "Use \\%s instead of %s in math mode" word word;
                  location = Location.make 0 0;
                  suggestion = Some (Printf.sprintf "Replace with \\%s" word);
                  confidence = 0.9;
                }
              else None
        else None
      )
  }
  
  (* Rule: Proper differential notation *)
  let differential_notation = {
    id = "MATH-002";
    name = "differential_notation";
    description = "Use \\mathrm{d} or \\,\\mathrm{d} for differentials";
    severity = Info;
    category = "math";
    check = fun tokens ->
      MathMode.scan_with_math_state tokens (fun i tok state ->
        if state.MathMode.in_math then
          match tok with
          | TChar (uc, _) when Uchar.to_int uc = 100 -> (* 'd' *)
              (* Check if this might be a differential *)
              let context_suggests_differential = 
                i > 0 && (match tokens.(i-1) with
                | TMacro "int" -> true
                | TChar (uc, _) when Uchar.to_int uc = 0x2F -> true (* / *)
                | _ -> false)
              in
              if context_suggests_differential then
                Some {
                  rule_id = "MATH-002";
                  message = "Use \\mathrm{d} for differential operator";
                  location = Location.make 0 0;
                  suggestion = Some "Replace d with \\mathrm{d}";
                  confidence = 0.7;
                }
              else None
          | _ -> None
        else None
      )
  }
  
  (* Rule: Proper vector notation *)
  let vector_notation = {
    id = "MATH-003";
    name = "vector_notation";
    description = "Use consistent vector notation (\\vec or \\mathbf)";
    severity = Info;
    category = "math";
    check = fun tokens ->
      let vec_commands = ref [] in
      let issues = ref [] in
      
      Array.iter (function
        | TMacro cmd when List.mem cmd ["vec"; "mathbf"; "boldsymbol"] ->
            vec_commands := cmd :: !vec_commands
        | _ -> ()
      ) tokens;
      
      let unique_commands = List.sort_uniq String.compare !vec_commands in
      if List.length unique_commands > 1 then
        issues := {
          rule_id = "MATH-003";
          message = "Inconsistent vector notation commands";
          location = Location.make 0 0;
          suggestion = Some "Use one vector notation style consistently";
          confidence = 0.8;
        } :: !issues;
      
      !issues
  }
end

(** Equation and alignment rules *)
module EquationRules = struct
  
  (* Rule: Equation numbering consistency *)
  let equation_numbering = {
    id = "MATH-004";
    name = "equation_numbering";
    description = "Use consistent equation numbering";
    severity = Info;
    category = "math";
    check = fun tokens ->
      let numbered_envs = ref [] in
      let unnumbered_envs = ref [] in
      let issues = ref [] in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest ->
            if List.mem env ["equation"; "align"; "gather"] then
              numbered_envs := env :: !numbered_envs
            else if List.mem env ["equation*"; "align*"; "gather*"] then
              unnumbered_envs := env :: !unnumbered_envs;
            scan rest
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      
      if List.length !numbered_envs > 0 && List.length !unnumbered_envs > 0 then
        issues := {
          rule_id = "MATH-004";
          message = "Mixed numbered and unnumbered equations";
          location = Location.make 0 0;
          suggestion = Some "Use consistent equation numbering style";
          confidence = 0.7;
        } :: !issues;
      
      !issues
  }
  
  (* Rule: Alignment character usage *)
  let alignment_characters = {
    id = "MATH-005";
    name = "alignment_characters";
    description = "Proper use of alignment characters in align environment";
    severity = Warning;
    category = "math";
    check = fun tokens ->
      let issues = ref [] in
      let in_align = ref false in
      let ampersand_count = ref 0 in
      
      let rec scan = function
        | [] -> ()
        | TMacro "begin" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["align"; "align*"; "eqnarray"; "eqnarray*"] ->
            in_align := true;
            ampersand_count := 0;
            scan rest
        | TMacro "end" :: TGroupOpen :: TMacro env :: TGroupClose :: rest
          when List.mem env ["align"; "align*"; "eqnarray"; "eqnarray*"] ->
            in_align := false;
            scan rest
        | TChar (uc, _) :: rest when !in_align && Uchar.to_int uc = 38 -> (* & *)
            incr ampersand_count;
            scan rest
        | TChar (uc, _) :: rest when !in_align && Uchar.to_int uc = 92 -> (* \ *)
            (* Check for \\ (line break) *)
            (match rest with
            | TChar (uc2, _) :: rest2 when Uchar.to_int uc2 = 92 ->
                if !ampersand_count = 0 then
                  issues := {
                    rule_id = "MATH-005";
                    message = "No alignment character (&) before line break";
                    location = Location.make 0 0;
                    suggestion = Some "Add & before = or other relation";
                    confidence = 0.8;
                  } :: !issues;
                ampersand_count := 0;
                scan rest2
            | _ -> scan rest)
        | _ :: rest -> scan rest
      in
      
      scan (Array.to_list tokens);
      List.rev !issues
  }
end

(** Symbol and notation rules *)
module SymbolRules = struct
  
  (* Rule: Consistent Greek letter variants *)
  let greek_variants = {
    id = "MATH-006";
    name = "greek_variants";
    description = "Use consistent Greek letter variants";
    severity = Info;
    category = "math";
    check = fun tokens ->
      let variants = [
        ("epsilon", "varepsilon");
        ("phi", "varphi");
        ("theta", "vartheta");
        ("rho", "varrho");
        ("pi", "varpi");
      ] in
      let used_variants = Hashtbl.create 10 in
      let issues = ref [] in
      
      Array.iter (function
        | TMacro name ->
            List.iter (fun (base, var) ->
              if name = base || name = var then
                Hashtbl.replace used_variants (base, var) name
            ) variants
        | _ -> ()
      ) tokens;
      
      Hashtbl.iter (fun (base, var) used ->
        (* Check if both variants are used *)
        Array.iter (function
          | TMacro name when (name = base || name = var) && name <> used ->
              issues := {
                rule_id = "MATH-006";
                message = Printf.sprintf "Inconsistent Greek letter: \\%s and \\%s both used" base var;
                location = Location.make 0 0;
                suggestion = Some "Use one variant consistently";
                confidence = 0.8;
              } :: !issues
          | _ -> ()
        ) tokens
      ) used_variants;
      
      List.rev !issues
  }
  
  (* Rule: Proper spacing around operators *)
  let operator_spacing = {
    id = "MATH-007";
    name = "operator_spacing";
    description = "Proper spacing around binary operators";
    severity = Info;
    category = "math";
    check = fun tokens ->
      let binary_ops = ["+"; "-"; "="; "<"; ">"; "\\leq"; "\\geq"; "\\neq"] in
      let issues = ref [] in
      
      MathMode.scan_with_math_state tokens (fun i tok state ->
        if state.MathMode.in_math then
          match tok with
          | TMacro op when List.mem ("\\" ^ op) binary_ops ->
              (* Check spacing around operators *)
              let has_space_before = i > 0 && (match tokens.(i-1) with
                | TChar (uc, _) when Uchar.to_int uc = 0x20 -> true
                | _ -> false) in
              let has_space_after = i < Array.length tokens - 1 && (match tokens.(i+1) with
                | TChar (uc, _) when Uchar.to_int uc = 0x20 -> true
                | _ -> false) in
              if not has_space_before && not has_space_after then
                Some {
                  rule_id = "MATH-007";
                  message = Printf.sprintf "Consider adding space around \\%s" op;
                  location = Location.make 0 0;
                  suggestion = Some "Add thin space \\, around binary operators";
                  confidence = 0.6;
                }
              else None
          | _ -> None
        else None
      )
  }
end

(** Collect all math notation rules *)
let all_rules = [
  (* Functions *)
  FunctionRules.proper_functions;
  FunctionRules.differential_notation;
  FunctionRules.vector_notation;
  
  (* Equations *)
  EquationRules.equation_numbering;
  EquationRules.alignment_characters;
  
  (* Symbols *)
  SymbolRules.greek_variants;
  SymbolRules.operator_spacing;
]

(** Validation functions *)
let validate tokens =
  List.fold_left (fun acc rule ->
    let issues = rule.check tokens in
    acc @ List.map (fun issue -> (rule, issue)) issues
  ) [] all_rules

let rule_count () = List.length all_rules

let rules_by_category category =
  List.filter (fun r -> r.category = category) all_rules