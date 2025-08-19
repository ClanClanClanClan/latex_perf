(* Validator DSL v1 Foundation - LaTeX Perfectionist v25 - FIXED VERSION *)

open Printf

type severity = Error | Warning | Info | Hint
type phase = Phase1_Syntax | Phase2_Semantic | Phase3_Style | Phase4_Quality
type pattern = 
  | Literal of string
  | Regex of string  
  | Token of string
  | Sequence of pattern list
  | Choice of pattern list

type context = Document | TextMode | MathMode | Environment of string
type fix_action = Replace of string | Delete | Insert of string

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

(* Simple rule creation *)
let create_rule id name desc sev ph pat ctx fix_opt =
  {
    id; name; description = desc; severity = sev; phase = ph;
    pattern = pat; contexts = ctx; fix = fix_opt;
    provides = []; requires = []; conflicts = []; enabled = true;
  }

(* Pattern constructors *)
let lit s = Literal s
let regex s = Regex s
let seq patterns = Sequence patterns
let choice patterns = Choice patterns

(* Example rules *)
let example_rules = [
  create_rule "typo_001" "Double dollar signs"
    "Use \\[ ... \\] instead of $$ ... $$ for display math"
    Warning Phase1_Syntax
    (seq [lit "$$"; regex ".*"; lit "$$"])
    [Document; TextMode]
    (Some (Replace "\\[...\\]"));
    
  create_rule "typo_002" "Inconsistent spacing"
    "Ensure consistent spacing around = in math"
    Info Phase3_Style
    (choice [seq [regex "[^ ]"; lit "="; regex " "]])
    [MathMode]
    (Some (Replace " = "));
]

let get_example_rules () = example_rules

(* Pattern to string *)
let rec pattern_to_string = function
  | Literal s -> sprintf "Literal(%s)" s
  | Regex s -> sprintf "Regex(%s)" s
  | Token t -> sprintf "Token(%s)" t
  | Sequence ps -> sprintf "Seq[%s]" (String.concat ", " (List.map pattern_to_string ps))
  | Choice ps -> sprintf "Choice[%s]" (String.concat " | " (List.map pattern_to_string ps))