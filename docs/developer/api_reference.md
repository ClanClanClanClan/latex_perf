# API Reference

## Core Modules

### L0 Lexer (`LatexLexer.v`)

**Main Types:**
```coq
Inductive latex_token : Type :=
  | TCommand : string -> latex_token       (* \frac, \begin, \end *)
  | TBeginGroup : latex_token              (* { *)
  | TEndGroup : latex_token                (* } *)
  | TMathShift : latex_token               (* $ *)
  | TAlignment : latex_token               (* & *)
  | TParameter : latex_token               (* # *)
  | TSuperscript : latex_token             (* ^ *)
  | TSubscript : latex_token               (* _ *)
  | TText : string -> latex_token          (* regular text *)
  | TSpace : latex_token                   (* whitespace *)
  | TComment : string -> latex_token       (* % comment *)
  | TNewline : latex_token                 (* end of line *)
  | TEOF : latex_token.                    (* end of file *)
```

**Main Functions:**
- `latex_lexer : string -> list latex_token` - Tokenize LaTeX string

### L1 Expander (`ExpanderTypes.v`, `ExpanderAlgorithm.v`)

**Main Types:**
```coq
Record exp_state : Type := {
  macro_definitions : list macro_def;
  expansion_depth : nat;
  call_stack : list string;
  max_expansions : nat;
  macro_calls : nat;
  token_growth : nat
}.

Inductive expand_result : Type :=
  | ExpandSuccess : list latex_token -> expand_result
  | ExpandError : expand_error -> expand_result.
```

**Main Functions:**
```coq
expand : exp_state -> list latex_token -> expand_result
```

**Formal Guarantees:**
- `expand_fuel_insensitive` - Result independent of fuel when sufficient
- `expand_terminates_acyclic` - Always terminates for acyclic macros  
- `expand_no_teof` - Preserves absence of TEOF tokens

### V1½ Rules (`PostExpansionRules.v`)

**Main Types:**
```coq
Record validation_issue : Type := {
  rule_id : string;
  issue_severity : severity;
  message : string;
  loc : option location;
  suggested_fix : option string;
  rule_owner : string
}.

Record validation_rule : Type := {
  rule_id : string;
  description : string;
  validator : document_state -> list validation_issue;
  (* ... other fields ... *)
}.
```

**Available Rules:** POST-001 through POST-050

## Performance Constraints

### L1 Expander Limits
- **Token Growth**: 8,192 tokens maximum per document
- **Macro Calls**: 512 calls maximum per document  
- **Expansion Depth**: 32 levels maximum
- **Runtime SLA**: 42ms target (currently achieving 4.43ms)

### Built-in Macros
- **Typography**: 12 macros (`\LaTeX`, `\textbf`, etc.)
- **Mathematics**: 32 macros (Greek letters, symbols)
- **Structural**: 20 macros (sections, references)  
- **Formatting**: 12 macros (font sizes, alignment)

## Error Handling

### Expand Errors
```coq
Inductive expand_error : Type :=
  | MacroNotFound : string -> expand_error
  | RecursionLimit : expand_error
  | MalformedMacro : string -> expand_error
  | TokenLimitExceeded : expand_error
  | CallLimitExceeded : expand_error.
```

### Validation Severities
```coq
Inductive severity : Type :=
  | Error          (* Blocks processing *)
  | Warning        (* Should be fixed *)
  | Info.          (* Informational *)
```

## Integration Points

### L0 → L1 Integration
```coq
(* L0 output directly compatible with L1 input *)
let tokens := latex_lexer input_string in
let result := expand initial_state tokens in
```

### L1 → V1½ Integration  
```coq
(* V1½ rules operate on expanded token stream *)
let expanded_tokens := extract_tokens expand_result in
let issues := validate_with_post_expansion original_tokens expanded_tokens filename in
```

## Build Integration

### _CoqProject Structure
- `-R src/core ""` - Core modules accessible directly
- All active modules listed in dependency order
- Warnings configured for clean compilation

### Compilation Order
1. `LatexCatcodes.v` - Category code system
2. `LatexLexer.v` - L0 tokenizer  
3. `ExpanderTypes.v` - L1 type definitions
4. `MacroCatalog.v` - Built-in macro definitions
5. `ExpanderAlgorithm.v` - L1 expansion logic
6. `ExpanderProofsFinal.v` - Formal verification
7. `PostExpansionRules.v` - V1½ validation rules