# Validator Implementation Guide

**Purpose**: Guide for implementing and extending the LaTeX Perfectionist validator framework  
**Current Status**: 141/623 rules implemented (23% complete)  
**Priority**: Critical for v25_R1 compliance

## 📋 OVERVIEW

### **Validator Framework Architecture**
- **Rule catalog**: 623 rules in `specs/rules/rules_v3.yaml`
- **Implementation**: Single-pass engine with interest masks
- **Performance**: 1.261ms P99 for 276K tokens (target: ≤2ms)
- **Dependencies**: DAG-based rule scheduling (not yet implemented)

### **Current Implementation Status**
```yaml
# Working validators (141 implemented):
- TYPO rules: 10/50 (typography)
- DELIM rules: 2/25 (delimiters) 
- SPC rules: 3/35 (spacing)
- Other categories: Mostly unimplemented

# Critical gap: 482 missing rules require generator system
```

## 🏗️ VALIDATOR ARCHITECTURE

### **Core Types**
```ocaml
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
```

### **Validator Module Pattern**
```ocaml
module RULE_XXX = struct
  let id = "RULE-XXX"
  let description = "Brief description matching rules_v3.yaml"
  let severity = `Critical  (* or `Warning, `Style, `Info *)
  let precondition = "L0_Lexer"  (* or "L1_Expander", "L2_Parser" *)
  
  let validate tokens =
    let results = ref [] in
    (* Implementation logic *)
    List.rev !results
end
```

## 📖 RULE CATEGORIES (623 Total)

### **Phase 0: Reserved Rules** (25 rules)
```yaml
PDF-001 to PDF-010:   # Document-level validation
  severity: Critical
  scope: PDF metadata, structure
  
CHAR-001 to CHAR-015: # Character encoding
  severity: Critical  
  scope: UTF-8 compliance, forbidden characters
```

### **Phase 1: L0/L1 Processing** (110 rules)
```yaml
TYPO-001 to TYPO-050: # Typography
  examples:
    - TYPO-001: ASCII quotes → curly quotes (implemented)
    - TYPO-002: Double hyphen → en-dash (implemented)
    - TYPO-005: Three periods → ellipsis (implemented)
  severity: Warning
  
DELIM-001 to DELIM-025: # Delimiter matching  
  examples:
    - DELIM-001: Unmatched closing brace (implemented)
    - DELIM-002: Unclosed opening brace (implemented)
  severity: Critical
  
SPC-001 to SPC-035: # Spacing rules
  examples:
    - SPC-006: Tab characters forbidden (implemented as TYPO-006)
    - SPC-010: Space before punctuation (implemented as TYPO-010)
  severity: Info
```

### **Phase 1.5: L2 Post-expansion** (80 rules)
```yaml
ENV-001 to ENV-030: # Environment validation
  scope: \begin{} \end{} matching, nesting
  severity: Critical
  status: Not implemented
  
CMD-001 to CMD-050: # Command validation  
  scope: Command syntax, argument validation
  severity: Warning
  status: Not implemented
```

### **Phase 2: L3 Semantic** (80 rules)
```yaml
REF-001 to REF-040: # Reference validation
  scope: \label, \ref, \cite consistency
  severity: Warning
  status: Not implemented
  
STRUCT-001 to STRUCT-040: # Document structure
  scope: Section hierarchy, numbering
  severity: Style
  status: Not implemented
```

### **Phase 3: L4 Style** (200 rules)
```yaml
STYLE-001 to STYLE-100: # Style enforcement
  scope: Typography, formatting consistency
  severity: Style
  status: Not implemented
  
LAYOUT-001 to LAYOUT-100: # Layout validation
  scope: Page layout, spacing, alignment
  severity: Style  
  status: Not implemented
```

## 🔧 IMPLEMENTATION PATTERNS

### **Character-based Rules** (ASCII validation)
```ocaml
module TYPO_001 = struct
  let id = "TYPO-001"
  let description = "ASCII straight quotes must be curly quotes"
  let severity = `Critical
  
  let validate tokens =
    let results = ref [] in
    Array.iteri (fun i token ->
      match token.ascii_char with
      | Some 34 -> (* ASCII quote *)
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
```

### **Sequence-based Rules** (Pattern matching)
```ocaml
module TYPO_002 = struct
  let id = "TYPO-002"
  let description = "Double hyphen should be en-dash"
  let severity = `Warning
  
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
```

### **State-based Rules** (Bracket matching)
```ocaml
module DELIM_001 = struct
  let id = "DELIM-001"
  let description = "Unmatched closing brace"
  let severity = `Critical
  
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
```

## 🧪 TESTING FRAMEWORK

### **Unit Test Pattern**
```ocaml
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
    assert (List.length results = 2);  (* Two ASCII quotes found *)
    List.iter (fun r -> 
      assert (r.rule_id = "TYPO-001");
      assert (r.severity = `Critical)
    ) results
end
```

### **Integration Testing**
```bash
# Run comprehensive validator tests
./test/validators/comprehensive_rule_validation_test

# Expected output:
# - Tests 10 validator rules on realistic LaTeX examples
# - Performance: ~14,000 chars/ms processing rate
# - All rules follow rules_v3.yaml specifications
```

### **Performance Testing**
```ocaml
(* Performance validation for large documents *)
let test_performance () =
  let doc = create_large_document 100000 in  (* 100K chars *)
  let tokens = parse_text doc in
  let start_time = Unix.gettimeofday () in
  let results = Registry.validate_all tokens in
  let end_time = Unix.gettimeofday () in
  let duration = (end_time -. start_time) *. 1000.0 in
  assert (duration < 2.0);  (* Target: <2ms for any document size *)
  printf "Validated %d tokens in %.3f ms\n" (Array.length tokens) duration
```

## 🔄 GENERATOR SYSTEM (Critical Gap)

### **Required Implementation**
```ocaml
(* src/generator/rule_parser.ml - NOT YET IMPLEMENTED *)
type rule_spec = {
  id: string;
  phase: int;
  provides: string list;
  requires: string list;
  conflicts: string list;
  severity: [`Critical | `Warning | `Style | `Info];
  description: string;
  implementation_hint: string option;
}

let parse_rules_yaml filename =
  (* Parse specs/rules/rules_v3.yaml *)
  (* Extract rule specifications *)
  (* Build dependency graph *)
  []

let generate_validator_code rule_spec =
  (* Template-based code generation *)
  (* Create validator module *)
  (* Generate test cases *)
  ""

let build_dependency_dag rules =
  (* Analyze rule dependencies *)
  (* Create execution order *)
  (* Detect conflicts *)
  []
```

### **Template System** (Proposed)
```ocaml
(* Generator templates for common patterns *)
let ascii_char_template = {|
module {RULE_ID} = struct
  let id = "{RULE_ID}"
  let description = "{DESCRIPTION}"
  let severity = `{SEVERITY}
  
  let validate tokens =
    let results = ref [] in
    Array.iteri (fun i token ->
      match token.ascii_char with
      | Some {ASCII_CODE} ->
          results := {{
            rule_id = id;
            position = token.position;
            message = "{MESSAGE}";
            severity = `{SEVERITY};
          }} :: !results
      | _ -> ()
    ) tokens;
    List.rev !results
end
|}
```

## 📊 PERFORMANCE OPTIMIZATION

### **Interest Masks** (93% efficiency)
```ocaml
(* Optimize validators with interest masks *)
let has_interest tokens rule_interest_chars =
  (* Quick scan: does document contain characters this rule cares about? *)
  Array.exists (fun token ->
    match token.ascii_char with
    | Some c -> List.mem c rule_interest_chars
    | None -> false
  ) tokens

let validate_with_interest_mask tokens =
  let results = ref [] in
  
  (* TYPO-001: Only run if document contains ASCII quotes *)
  if has_interest tokens [34] then
    results := TYPO_001.validate tokens @ !results;
    
  (* TYPO-002: Only run if document contains hyphens *)
  if has_interest tokens [45] then
    results := TYPO_002.validate tokens @ !results;
    
  !results
```

### **Single-pass Architecture**
- **O(n) complexity**: Each validator scans tokens once
- **Early termination**: Interest masks skip irrelevant rules
- **Memory efficiency**: Process tokens in-place when possible
- **Cache-friendly**: Linear memory access patterns

## 🎯 IMPLEMENTATION PRIORITIES

### **Phase 1: Generator System** (Week 3-4)
1. **Parse rules_v3.yaml**: Extract 623 rule specifications
2. **Template engine**: Generate validator modules automatically
3. **DAG builder**: Resolve dependencies and conflicts
4. **Integration**: Generate missing 482 validators

### **Phase 2: L2 Integration** (Week 5-6)
1. **ENV validators**: Environment matching and nesting
2. **CMD validators**: Command syntax validation
3. **Streaming interface**: Process L2 AST efficiently

### **Phase 3: L3/L4 Validators** (Week 7-12)
1. **REF validators**: Reference consistency checking
2. **STRUCT validators**: Document structure validation
3. **STYLE/LAYOUT validators**: Typography and layout rules

## 📚 REFERENCE MATERIALS

### **Essential Files**
- `specs/rules/rules_v3.yaml`: Complete 623-rule catalog
- `src/validators/specification_based_validators.ml`: Current implementation (10 rules)
- `test/validators/comprehensive_rule_validation_test.ml`: Test framework

### **Implementation Examples**
- Typography: `TYPO_001` (ASCII quotes)
- Sequence detection: `TYPO_002` (double hyphens)
- State tracking: `DELIM_001` (bracket matching)
- Performance: Interest masks for 93% efficiency

---

**Next Action**: Implement validator generator system to scale from 141 to 623 rules automatically. This is the critical path to v25_R1 compliance.