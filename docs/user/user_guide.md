# User Guide

## Overview

LaTeX Perfectionist v24 is a formally verified system for processing and validating LaTeX documents with mathematical guarantees of correctness.

## Key Features

### ✅ **Completed Components**

#### L0 Verified Lexer
- **Purpose**: Tokenize LaTeX documents into structured tokens
- **Status**: Complete with formal verification (0 axioms, 0 admits)
- **Performance**: Sub-second tokenization for typical documents

#### L1 Verified Macro Expander  
- **Purpose**: Expand LaTeX macros while maintaining correctness
- **Built-in Macros**: 76 standard LaTeX macros supported
- **Performance**: 4.43ms average (9.5x under 42ms SLA target)
- **Safety**: Prevents infinite recursion, enforces token limits

#### V1½ Post-Expansion Rules
- **Purpose**: Validate macro expansion results  
- **Rules**: 50 validation rules implemented
- **Coverage**: Detects expansion artifacts, deprecated usage, nesting issues

### 🎯 **Planned Components**

- **L2 PEG Parser**: AST construction (Months 7-9)
- **L3 Reference Interpreter**: Semantic analysis (Month 10)  
- **L4 Style Processor**: Document formatting (Months 11-12)
- **V1-V4 Rules**: 542 total validation rules across all layers

## Usage Scenarios

### Academic Document Processing
- Research papers with complex mathematics
- Thesis and dissertation validation
- Conference paper compliance checking

### Publishing Workflows  
- Journal submission preparation
- Style guide enforcement
- Quality assurance automation

### Development Integration
- CI/CD pipeline integration
- Pre-commit validation hooks
- Automated document quality checks

## Performance Characteristics

### Current Benchmarks
- **Small documents** (1-10 pages): 4.43ms average
- **Medium documents** (10-50 pages): ~20ms average  
- **Large documents** (50+ pages): <42ms (SLA target)

### Scaling Behavior
- **Linear scaling** with document size
- **Constant time** per macro expansion
- **Memory efficient** token processing

### Resource Requirements
- **CPU**: Single-core sufficient for typical usage
- **Memory**: <100MB for large documents
- **Disk**: Minimal temporary storage needed

## Input Formats

### Supported LaTeX
- **Standard LaTeX**: Full compatibility with LaTeX 2e
- **Common Packages**: AMS-Math, Graphics, Bibliography
- **Custom Macros**: User-defined macros with restrictions

### Document Structure
```latex
\documentclass{article}
\usepackage{amsmath}

\newcommand{\mycommand}[1]{\textbf{#1}}

\begin{document}
\title{My Document}
\author{Author Name}
\maketitle

Content with \mycommand{macro usage}.

\begin{equation}
E = mc^2
\end{equation}

\end{document}
```

### Constraints and Limitations
- **Macro Recursion**: Maximum 32 levels deep
- **Token Growth**: 8,192 token limit per document
- **Macro Calls**: 512 calls maximum per document
- **Acyclic Requirement**: No circular macro dependencies

## Validation Rules

### Rule Categories

#### POST-001 to POST-050: Post-Expansion Rules
- **POST-001**: Macro expansion artifacts detection
- **POST-005**: Deprecated macro usage warnings
- **POST-009**: Command nesting validation
- **POST-012**: Brace balance verification
- **POST-020**: Math mode consistency
- **POST-025**: Citation format validation
- **POST-030**: Figure/table reference checks
- **POST-040**: Unicode normalization
- **POST-050**: Performance optimization hints

### Severity Levels
- **Error**: Blocks processing, must be fixed
- **Warning**: Should be addressed, processing continues
- **Info**: Informational, no action required

### Rule Output Format
```
Rule ID: POST-009
Severity: Error
Message: Improperly nested commands detected after expansion
Location: Line 45, Column 12
Suggested Fix: fix_command_nesting
Owner: @expansion-team
```

## Error Handling

### Common Errors

#### Macro Not Found
```
Error: MacroNotFound(\command)
Cause: Custom macro used without definition
Fix: Add \newcommand definition or remove usage
```

#### Recursion Limit
```
Error: RecursionLimit
Cause: Macro expansion depth exceeds 32 levels
Fix: Simplify macro definitions or remove recursion
```

#### Token Limit Exceeded
```
Error: TokenLimitExceeded  
Cause: Document expansion produces >8,192 tokens
Fix: Reduce macro usage or simplify content
```

### Debugging Tips
1. **Check macro definitions** for circular dependencies
2. **Validate syntax** of custom commands
3. **Test incrementally** with smaller document sections
4. **Review warnings** for optimization opportunities

## Integration Examples

### Command Line Usage
```bash
# Basic validation
latex-perfectionist document.tex

# With specific rule sets
latex-perfectionist --rules=post-expansion document.tex

# Performance profiling
latex-perfectionist --profile document.tex
```

### Build System Integration
```makefile
# Makefile integration
validate-docs:
	latex-perfectionist *.tex
	
# Pre-commit hook
pre-commit:
	latex-perfectionist --fast $(CHANGED_TEX_FILES)
```

### CI/CD Pipeline
```yaml
# GitHub Actions example
- name: Validate LaTeX
  run: |
    latex-perfectionist --strict docs/*.tex
    latex-perfectionist --performance-check large-document.tex
```

## Troubleshooting

### Performance Issues
- **Slow compilation**: Check for deeply nested macros
- **Memory usage**: Verify document size within limits
- **Timeout errors**: Simplify complex macro definitions

### Validation Failures  
- **False positives**: Review rule configuration
- **Missing issues**: Verify rule coverage for use case
- **Inconsistent results**: Check LaTeX package versions

### Build Problems
- **Coq compilation**: Verify Coq 8.17+ installation
- **Missing dependencies**: Check opam package status
- **Import errors**: Regenerate build files with coq_makefile

## Support and Resources

### Documentation
- **Quick Start**: Basic usage and examples
- **API Reference**: Developer integration details  
- **Implementation Guide**: Internal architecture
- **Project Status**: Current development progress

### Community
- **Issues**: Report bugs and feature requests
- **Discussions**: Ask questions and share experiences
- **Contributing**: Guidelines for code contributions

### Performance Monitoring
- **SLA Tracking**: 42ms processing target
- **Benchmark Suite**: Standardized performance tests
- **Resource Usage**: Memory and CPU profiling tools