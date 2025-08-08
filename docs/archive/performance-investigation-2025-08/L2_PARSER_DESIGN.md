# L2 Parser Design - LaTeX Perfectionist v25

## Overview
The L2 Incremental Parser transforms expanded token streams from L1 into a structured AST representation, enabling structural validation and semantic analysis.

## Performance Budget
- **Target**: ≤10ms P95 on 60k tokens
- **Incremental**: O(Δ) complexity for edits
- **Memory**: ≤50MB for large documents

## Architecture

### Core Components
1. **Parser Engine**: LL(2) predictive parser with error recovery
2. **AST Builder**: Efficient tree construction with parent pointers
3. **State Manager**: Tracks parsing context (math mode, environments, etc.)
4. **Error Recovery**: Synchronization points for graceful degradation

### AST Node Types
```ocaml
type ast_node =
  | Document of section list
  | Section of { level: int; title: inline list; content: block list }
  | Environment of { name: string; args: arg list; body: block list }
  | Command of { name: string; args: arg list }
  | MathInline of inline list
  | MathDisplay of block list
  | Text of string
  | Group of inline list
  | Paragraph of inline list
  | List of { kind: list_kind; items: block list list }
  | Table of { spec: string; rows: block list list list }
  | Include of { kind: include_kind; path: string }
  | Comment of string
  | Error of { msg: string; tokens: token list }
```

### Parsing Strategy
1. **Two-token lookahead**: Handles LaTeX ambiguities
2. **Context-sensitive**: Math mode affects token interpretation
3. **Error recovery**: Skip to next structural boundary
4. **Incremental**: Reparse only affected subtrees

## Implementation Plan
1. Core parser engine with basic node types
2. Environment and command parsing
3. Math mode handling
4. Error recovery mechanisms
5. Incremental update support
6. Integration with L1 pipeline
7. Comprehensive test suite