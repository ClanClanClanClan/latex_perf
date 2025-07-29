# ROOT FOLDER CLEANUP PLAN

## 🚨 **PROBLEM ANALYSIS**

**Current Root Folder Issues:**
- Mixed working code with archive materials
- Multiple competing documentation systems
- Build artifacts scattered everywhere  
- Historical reports mixed with current status
- Experimental code not clearly separated
- No clear distinction between what's active vs. deprecated

**Result**: Constant confusion about project state and scope

---

## ✅ **PROPOSED CLEAN STRUCTURE**

```
latex-perfectionist-v25/
├── README.md                 # Project overview and quick start
├── CLAUDE.md                 # AI session instructions (current)
├── _CoqProject              # Coq build configuration
├── dune-project             # OCaml build configuration  
├── Makefile                 # Main build targets
├── latex-perfectionist.opam # Package dependencies
│
├── src/                     # *** CURRENT WORKING CODE ***
│   ├── core/               # v25 Week 1 foundation (what we worked on)
│   ├── rules/              # Validation rule implementations
│   ├── extraction/         # OCaml extraction code
│   └── integration/        # Python-OCaml bridge
│
├── specs/                   # *** V25 SPECIFICATIONS ***
│   ├── requirements/       # High-level requirements
│   ├── architecture/       # System design documents  
│   ├── rules/              # Rule specifications (rules_v3.yaml)
│   └── implementation/     # Technical implementation plans
│
├── archive/                 # *** HISTORICAL MATERIALS ***
│   ├── v24/                # Previous version artifacts
│   ├── experiments/        # Failed experiments and prototypes
│   ├── reports/            # Historical audit reports
│   └── development-history/ # Old development artifacts
│
├── tools/                   # *** DEVELOPMENT UTILITIES ***
│   ├── scripts/            # Build and maintenance scripts
│   ├── benchmarks/         # Performance testing
│   ├── corpus/             # Test document corpus
│   └── analysis/           # Code analysis tools
│
├── build/                   # *** BUILD ARTIFACTS *** (gitignored)
│   ├── _build/             # Dune build directory
│   ├── extracted/          # Generated OCaml code
│   └── compiled/           # Compiled objects
│
└── docs/                    # *** PROJECT DOCUMENTATION ***
    ├── user/               # User-facing documentation
    ├── developer/          # Developer guides
    └── api/                # API documentation
```

---

## 🎯 **CLEANUP ACTIONS**

### **Phase 1: Preserve Current Work**
1. **PROTECT** files we worked on in `src/core/`
2. **PRESERVE** current session documentation
3. **BACKUP** working build configuration

### **Phase 2: Reorganize Specifications**  
1. **MOVE** `docs/specifications/` → `specs/`
2. **ORGANIZE** v25 planning documents by category
3. **SEPARATE** requirements from implementation details

### **Phase 3: Archive Historical Materials**
1. **MOVE** old reports to `archive/reports/`
2. **CONSOLIDATE** experimental code in `archive/experiments/`
3. **PRESERVE** v24 materials in `archive/v24/`

### **Phase 4: Organize Tools**
1. **CONSOLIDATE** all scripts in `tools/scripts/`
2. **MOVE** corpus management to `tools/corpus/`
3. **ORGANIZE** benchmarks and analysis tools

### **Phase 5: Clean Root**
1. **REMOVE** scattered documentation files from root
2. **GITIGNORE** build artifacts properly
3. **CREATE** clear README with navigation

---

## 🚫 **WHAT NOT TO TOUCH**

- `src/core/` - Our current working implementation
- `_CoqProject` - Working build configuration
- `CLAUDE.md` - Current session instructions  
- Any `.vo` compiled Coq files that are working

---

## 📋 **EXECUTION PLAN**

1. **Backup current state** (git commit)
2. **Create new directory structure**
3. **Move files systematically** (preserve git history)
4. **Update build paths** as needed
5. **Test compilation** after moves
6. **Update documentation** to reflect new structure

This will eliminate confusion by creating clear separation between:
- **What we're working on NOW** (`src/`)
- **What we're supposed to build** (`specs/`)  
- **What we've done before** (`archive/`)
- **How we build and test** (`tools/`)