(* Validator DSL v1 Foundation - LaTeX Perfectionist v25 *)
(* Domain-Specific Language for defining and generating validation rules *)

open Printf

(* Rule severity levels *)
type severity = 
  | Error      (* Must fix - blocks compilation *)
  | Warning    (* Should fix - potential issue *)
  | Info       (* Could fix - style suggestion *)
  | Hint       (* May consider - enhancement *)

(* Rule phase - when to apply *)
type phase =
  | Phase1_Syntax     (* Basic syntax checks *)
  | Phase2_Semantic   (* Semantic validation *)
  | Phase3_Style      (* Style and consistency *)
  | Phase4_Quality    (* Quality and best practices *)

(* Pattern matching types *)
type pattern =
  | Literal of string
  | Regex of string
  | Token of string
  | Sequence of pattern list
  | Choice of pattern list
  | Optional of pattern
  | Repeat of pattern * int option * int option  (* min, max *)
  | Not of pattern
  | Lookahead of pattern
  | Lookbehind of pattern
  | Capture of string * pattern  (* name, pattern *)

(* Context where pattern applies *)
type context =
  | Document
  | Preamble
  | Environment of string
  | MathMode
  | TextMode
  | Command of string
  | Section of int  (* section level *)
  | Custom of string

(* Fix action *)
type fix_action =
  | Replace of string
  | Delete
  | Insert of string
  | Wrap of string * string  (* before, after *)
  | ApplyFunction of string  (* function name *)
  | Manual of string  (* description for manual fix *)

(* Rule definition *)
type rule = {
  id: string;
  name: string;
  description: string;
  severity: severity;
  phase: phase;
  pattern: pattern;
  contexts: context list;
  fix: fix_action option;
  provides: string list;
  requires: string list;
  conflicts: string list;
  enabled: bool;
}

(* Rule manifest *)
type manifest = {
  version: string;
  rules: rule list;
  total_rules: int;
  phases: (phase * int) list;  (* phase, count *)
  dependencies: (string * string list) list;  (* rule_id, dependencies *)
}

(* DSL Builder interface *)
module Builder = struct
  type t = {
    mutable rules: rule list;
    mutable current_rule: rule option;
  }
  
  let create () = {
    rules = [];
    current_rule = None;
  }
  
  let rule builder id name =
    let new_rule = {
      id;
      name;
      description = "";
      severity = Warning;
      phase = Phase1_Syntax;
      pattern = Literal "";
      contexts = [Document];
      fix = None;
      provides = [];
      requires = [];
      conflicts = [];
      enabled = true;
    } in
    builder.current_rule <- Some new_rule;
    builder
  
  let description builder desc =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with description = desc }
     | None -> failwith "No current rule");
    builder
  
  let severity builder sev =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with severity = sev }
     | None -> failwith "No current rule");
    builder
  
  let phase builder ph =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with phase = ph }
     | None -> failwith "No current rule");
    builder
  
  let pattern builder pat =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with pattern = pat }
     | None -> failwith "No current rule");
    builder
  
  let contexts builder ctx_list =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with contexts = ctx_list }
     | None -> failwith "No current rule");
    builder
  
  let fix builder fix_action =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with fix = Some fix_action }
     | None -> failwith "No current rule");
    builder
  
  let provides builder items =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with provides = items }
     | None -> failwith "No current rule");
    builder
  
  let requires builder items =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with requires = items }
     | None -> failwith "No current rule");
    builder
  
  let conflicts builder items =
    (match builder.current_rule with
     | Some r -> builder.current_rule <- Some { r with conflicts = items }
     | None -> failwith "No current rule");
    builder
  
  let build builder =
    (match builder.current_rule with
     | Some r -> 
         builder.rules <- r :: builder.rules;
         builder.current_rule <- None
     | None -> ());
    builder
  
  let get_rules builder = List.rev builder.rules
end

(* Pattern constructors *)
let lit s = Literal s
let regex s = Regex s
let token t = Token t
let seq patterns = Sequence patterns
let choice patterns = Choice patterns
let opt pattern = Optional pattern
let star pattern = Repeat (pattern, Some 0, None)
let plus pattern = Repeat (pattern, Some 1, None)
let repeat ?(min=0) ?(max=(-1)) pattern = 
  Repeat (pattern, Some min, if max < 0 then None else Some max)
let not_ pattern = Not pattern
let ahead pattern = Lookahead pattern
let behind pattern = Lookbehind pattern
let capture name pattern = Capture (name, pattern)

(* Common patterns *)
let whitespace = regex "\\s+"
let newline = regex "\\n"
let identifier = regex "[a-zA-Z_][a-zA-Z0-9_]*"
let number = regex "-?[0-9]+(\\.[0-9]+)?"
let quoted_string = regex "\"[^\"]*\""

(* Generate manifest from rules *)
let generate_manifest rules =
  let count_phase phase =
    List.length (List.filter (fun r -> r.phase = phase) rules)
  in
  
  let extract_deps rule =
    (rule.id, rule.requires)
  in
  
  {
    version = "1.0.0";
    rules;
    total_rules = List.length rules;
    phases = [
      (Phase1_Syntax, count_phase Phase1_Syntax);
      (Phase2_Semantic, count_phase Phase2_Semantic);
      (Phase3_Style, count_phase Phase3_Style);
      (Phase4_Quality, count_phase Phase4_Quality);
    ];
    dependencies = List.map extract_deps rules;
  }

(* Pattern to string for debugging *)
let rec pattern_to_string = function
  | Literal s -> sprintf "Literal(%s)" s
  | Regex s -> sprintf "Regex(%s)" s
  | Token t -> sprintf "Token(%s)" t
  | Sequence ps -> sprintf "Seq[%s]" (String.concat ", " (List.map pattern_to_string ps))
  | Choice ps -> sprintf "Choice[%s]" (String.concat " | " (List.map pattern_to_string ps))
  | Optional p -> sprintf "Opt(%s)" (pattern_to_string p)
  | Repeat (p, min, max) -> 
      let min_str = match min with Some n -> string_of_int n | None -> "0" in
      let max_str = match max with Some n -> string_of_int n | None -> "*" in
      sprintf "Repeat(%s, %s, %s)" (pattern_to_string p) min_str max_str
  | Not p -> sprintf "Not(%s)" (pattern_to_string p)
  | Lookahead p -> sprintf "Ahead(%s)" (pattern_to_string p)
  | Lookbehind p -> sprintf "Behind(%s)" (pattern_to_string p)
  | Capture (name, p) -> sprintf "Capture(%s, %s)" name (pattern_to_string p)

(* Example rules using the DSL *)
let create_example_rules () =
  let open Builder in
  let builder = create () in
  
  (* Rule 1: Double dollar signs (common LaTeX error) *)
  let builder = builder
    |> rule "typo_001" "Double dollar signs"
    |> description "Use \\[ ... \\] instead of $$ ... $$ for display math"
    |> severity Warning
    |> phase Phase1_Syntax
    |> pattern (seq [lit "$$"; capture "content" (star (not_ (lit "$$"))); lit "$$"])
    |> contexts [Document; TextMode]
    |> fix (Replace "\\[content\\]")
    |> build
  in
  let builder = builder |> provides ["display_math_modern"] |> build in
  
  (* Rule 2: Inconsistent spacing around equals *)
  let builder = builder
    |> rule "typo_002" "Inconsistent spacing around ="
    |> description "Ensure consistent spacing around = in math mode"
    |> severity Info
    |> phase Phase3_Style
    |> pattern (choice [
        seq [regex "[^ ]"; lit "="; regex " "];
        seq [regex " "; lit "="; regex "[^ ]"]
      ])
    |> contexts [MathMode]
    |> fix (Replace " = ")
    |> build
  in
  
  (* Rule 3: Missing tilde before citations *)
  let builder = builder
    |> rule "typo_003" "Missing tilde before cite"
    |> description "Use ~ before \\cite to prevent line breaks"
    |> severity Warning
    |> phase Phase2_Semantic
    |> pattern (seq [regex "[a-z]"; whitespace; token "\\cite"])
    |> contexts [Document; TextMode]
    |> fix (Replace "~\\cite")
    |> build
  in
  
  get_rules builder

(* Validate rule dependencies *)
let validate_dependencies rules =
  let rule_ids = List.map (fun r -> r.id) rules in
  let errors = ref [] in
  
  List.iter (fun rule ->
    (* Check requires *)
    List.iter (fun req ->
      if not (List.mem req rule_ids) then
        errors := sprintf "Rule %s requires unknown rule %s" rule.id req :: !errors
    ) rule.requires;
    
    (* Check conflicts *)
    List.iter (fun conf ->
      if not (List.mem conf rule_ids) then
        errors := sprintf "Rule %s conflicts with unknown rule %s" rule.id conf :: !errors
    ) rule.conflicts;
  ) rules;
  
  if !errors = [] then
    Ok ()
  else
    Error !errors

(* Pretty print manifest *)
let pp_manifest manifest =
  printf "=== Validator Manifest v%s ===\n" manifest.version;
  printf "Total rules: %d\n" manifest.total_rules;
  printf "\nPhases:\n";
  List.iter (fun (phase, count) ->
    let phase_str = match phase with
      | Phase1_Syntax -> "Syntax"
      | Phase2_Semantic -> "Semantic"
      | Phase3_Style -> "Style"
      | Phase4_Quality -> "Quality"
    in
    printf "  %s: %d rules\n" phase_str count
  ) manifest.phases;
  printf "\nRules:\n";
  List.iter (fun rule ->
    printf "  [%s] %s (%s)\n" rule.id rule.name 
      (match rule.severity with
       | Error -> "ERROR"
       | Warning -> "WARN"
       | Info -> "INFO"
       | Hint -> "HINT")
  ) manifest.rules