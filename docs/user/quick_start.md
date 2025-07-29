# Quick Start Guide

## Overview

LaTeX Perfectionist v24 is a formally verified LaTeX processing and validation system with 542 validation rules across 4 layers.

## Current Status (July 2025)

✅ **L0 Lexer**: Complete - tokenizes LaTeX documents  
✅ **L1 Expander**: Complete - handles macro expansion  
🎯 **V1½ Rules**: Ready - post-expansion validation rules

## Basic Usage

### 1. Build the System
```bash
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
```

### 2. Verify Components
```bash
# Test L0 lexer
make -f CoqMakefile src/core/lexer/LatexLexer.vo

# Test L1 expander  
make -f CoqMakefile src/core/expander/ExpanderAlgorithm.vo

# Test V1½ rules
make -f CoqMakefile src/rules/phase1_5/PostExpansionRules.vo
```

### 3. Check System Status
```bash
make validation
```

## Architecture Overview

```
Input File → L0 Lexer → L1 Expander → [L2 Parser] → [L3 Interpreter] → [L4 Style] → PDF
              ↓           ↓              ↓              ↓               ↓
           V1 Rules   V1½ Rules     V2 Rules       V3 Rules        V4 Rules
```

- **VSNA Layers (L0-L4)**: Core processing pipeline
- **Validation Layers (V1-V4)**: Rule-based validation at each stage

## Current Capabilities

- **L0**: Complete LaTeX tokenization with formal verification
- **L1**: Macro expansion with 76 built-in macros
- **V1½**: 50 post-expansion validation rules
- **Performance**: 4.43ms processing (9.5x under 42ms SLA)

## Next Steps

- **For Developers**: See [Implementation Guide](../developer/IMPLEMENTATION_GUIDE.md)
- **For Architecture**: See [Master Architecture](../developer/MASTER_ARCHITECTURE.md)
- **For Status**: See [Project Status](../internal/PROJECT_STATUS.md)