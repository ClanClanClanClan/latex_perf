# ULTRATHINK: Proper Validator Design & Implementation

## 🧠 Deep Analysis of Requirements

### Core Problems with Previous Implementation:
1. **No Context Awareness**: Validators didn't track math/text mode
2. **Naive Pattern Matching**: Triggered on partial matches
3. **No Token Stream Understanding**: Didn't handle macro expansion
4. **No Boundary Detection**: Couldn't distinguish words from substrings
5. **No State Management**: Each validator was stateless

## 📐 Proper Architecture Design

### 1. Token Stream Processing

The L0 lexer produces a stream of tokens. We need to:
- Track position in document
- Maintain context (math mode, environments, etc.)
- Handle lookahead/lookbehind
- Preserve token locations for error reporting

### 2. Context-Aware State Machine

```ocaml
type document_context = {
  mutable mode: [`Text | `Math | `DisplayMath];
  mutable math_delim_stack: math_delimiter list;
  mutable env_stack: environment list;
  mutable in_verbatim: bool;
  mutable in_comment: bool;
  mutable section_level: int;
  labels: (string, location) Hashtbl.t;
  citations: string list ref;
  macros_defined: string list ref;
  packages: string list ref;
}
```

### 3. False Positive Minimization Strategies

#### A. Word Boundary Detection
```ocaml
let is_word_boundary before after =
  let is_word_char = function
    | TChar (uc, Letter) -> true
    | TChar (uc, Other) when is_alphanumeric uc -> true
    | _ -> false
  in
  not (is_word_char before && is_word_char after)
```

#### B. Context-Specific Rules
- Only check math operators IN math mode
- Only check references AFTER \ref, \cite, etc.
- Only suggest em-dash for actual interruptions (not hyphenated words)

#### C. Confidence Scoring
```ocaml
type confidence = 
  | Certain of float      (* 0.9 - 1.0 *)
  | Likely of float       (* 0.7 - 0.9 *)
  | Possible of float     (* 0.5 - 0.7 *)
  | Unlikely of float     (* < 0.5 - probably suppress *)
```

### 4. Validator Categories

#### Level 1: Lexical (High Confidence)
- **Balanced delimiters**: {}, [], $$ 
- **Escaped characters**: \%, \$, \&
- **Encoding issues**: Invalid UTF-8

#### Level 2: Syntactic (Medium Confidence)
- **Macro arguments**: Correct arity
- **Environment matching**: \begin{X} ... \end{X}
- **Math mode consistency**: $ boundaries

#### Level 3: Semantic (Lower Confidence)
- **Typography suggestions**: quotes, dashes
- **Style preferences**: \sin vs sin
- **Best practices**: Non-breaking spaces

### 5. Implementation Strategy

#### Phase 1: Core Infrastructure
1. Proper token stream with lookahead
2. Context tracking state machine
3. Word boundary detection
4. Confidence scoring system

#### Phase 2: High-Value Validators
1. Delimiter balance (certain errors)
2. Environment matching (certain errors)
3. Undefined references (likely errors)
4. Math mode consistency (certain errors)

#### Phase 3: Style Validators
1. Typography (suggestions only)
2. Spacing (low confidence)
3. Citation style (informational)

## 🎯 Specific Validator Improvements

### TYPO-005: Em Dash (Previous False Positive Rate: ~80%)

**OLD (Bad)**:
```ocaml
| TChar (hyphen), TChar (letter) -> "Use em dash"
```

**NEW (Correct)**:
```ocaml
let validate_em_dash context tokens =
  match tokens with
  | ... :: space1 :: hyphen :: space2 :: ... 
    when is_space space1 && is_hyphen hyphen && is_space space2 
    && not (in_math_mode context) ->
      Some (Likely 0.8, "Consider em dash for interruption")
  | _ -> None
```

### MATH-006: Math Operators (Previous False Positive Rate: ~90%)

**OLD (Bad)**:
```ocaml
if contains "sin" -> "Use \\sin"  (* Matches "using", "cousin"! *)
```

**NEW (Correct)**:
```ocaml
let validate_math_operator context tokens =
  if not context.mode = `Math then None
  else match tokens with
  | prev :: TChar('s') :: TChar('i') :: TChar('n') :: next :: ...
    when is_word_boundary prev (TChar('s')) 
    && is_word_boundary (TChar('n')) next ->
      Some (Certain 0.95, "Use \\sin for sine function")
  | _ -> None
```

### REF-002: Undefined References (Previous False Positive Rate: ~70%)

**OLD (Bad)**:
```ocaml
if not (exists label) -> "Undefined"  (* Ignores .bib files! *)
```

**NEW (Correct)**:
```ocaml
let validate_reference context ref_name =
  (* Check multiple sources *)
  if Hashtbl.mem context.labels ref_name then
    None  (* Defined in document *)
  else if List.mem "biblatex" context.packages then
    None  (* Assume .bib file handles it *)
  else if String.starts_with "eq:" ref_name && in_amsmath context then
    None  (* AMS environments auto-label *)
  else
    Some (Likely 0.7, Printf.sprintf "Reference '%s' not found in document" ref_name)
```

## 🧪 Testing Strategy

### 1. Unit Tests per Validator
```ocaml
let test_ellipsis () =
  let test_cases = [
    ("...", true, "Three dots should trigger");
    (". . .", false, "Spaced dots should not trigger");
    ("3.14...", true, "Dots after number should trigger");
    ("etc...", true, "Common ellipsis case");
  ] in
  run_tests "TYPO-001" test_cases
```

### 2. False Positive Tests
```ocaml
let test_no_false_positives () =
  let legitimate_uses = [
    "co-author";     (* Should NOT trigger em-dash *)
    "using";         (* Should NOT trigger \sin *)
    "ref.~\\cite{x}"; (* Should NOT trigger undefined ref *)
  ] in
  assert_no_issues legitimate_uses
```

### 3. Corpus Testing
- Run on real LaTeX documents
- Measure false positive rate
- Tune confidence thresholds

## 🚀 Implementation Plan

### Day 1: Infrastructure
- [x] Proper module structure
- [ ] Context tracking system
- [ ] Token stream with lookahead
- [ ] Word boundary detection

### Day 2: Core Validators
- [ ] Delimiter balance
- [ ] Environment matching
- [ ] Math mode consistency
- [ ] Reference checking (smart)

### Day 3: Testing & Tuning
- [ ] Unit tests
- [ ] False positive tests
- [ ] Corpus validation
- [ ] Performance measurement

## 📊 Success Metrics

1. **Compilation**: 100% of validators compile
2. **Tests**: 100% of tests pass
3. **False Positives**: < 5% on real documents
4. **Performance**: < 0.5ms per validator
5. **Coverage**: All high-value errors caught

## 🔑 Key Insights

1. **Context is Everything**: Math vs text mode changes everything
2. **Boundaries Matter**: Word boundaries prevent 90% of false positives
3. **Confidence Levels**: Not all issues are equal
4. **External Context**: Consider .bib files, packages, etc.
5. **User Trust**: One false positive destroys trust in 10 real issues

This is the correct approach. Now let's implement it properly.