# Project Organization Guidelines

**Purpose**: Maintain pristine organization throughout 156-week development  
**Status**: MANDATORY reading for all contributors  
**Last Updated**: August 12, 2025

---

## 🎯 GOLDEN RULES

### **Rule 1: NO FILES IN ROOT**
The root directory must contain ONLY:
- `README.md` - Project overview
- `CLAUDE.md` - Session instructions
- `DOCUMENTATION_INDEX.md` - Master doc index
- `LICENSE` - Legal requirement
- `Makefile*` - Build system
- `dune*` - Build configuration
- `_CoqProject` - Coq project file
- `.gitignore` - Git configuration
- `.github/` - GitHub workflows and configuration
- `.ocamlformat` - OCaml formatter configuration
- `.gitmessage` - Git commit template
- `latex-perfectionist.opam` - Package definition

**EVERYTHING ELSE** goes in subdirectories.

### **Rule 2: SOURCE CODE DISCIPLINE**
```
src/
├── core/          # 5-layer architecture ONLY
│   ├── l0_lexer/  # L0 layer files only
│   ├── l1_expander/ # L1 layer files only
│   ├── l2_parser/ # L2 layer files only
│   ├── l3_semantics/ # L3 layer files only
│   └── l4_style/  # L4 layer files only
├── data/          # Type definitions ONLY
├── validation/    # Validation framework ONLY
├── validator/     # Validation engine ONLY
└── validators/    # Individual rules ONLY
```

### **Rule 3: TEST ORGANIZATION**
```
test/
├── unit/          # Unit tests
├── integration/   # Integration tests
├── performance/   # Performance tests
├── scripts/       # Test scripts
└── debug/         # Debug utilities
```

### **Rule 4: DOCUMENTATION HIERARCHY**
```
docs/
├── developer/     # Development guides
├── archive/       # Historical documents
│   └── [date]/    # Archived by date
├── analysis/      # Analysis reports
├── current/       # Current working docs
└── handoffs/      # Transition documents
```

---

## 🚫 FORBIDDEN PRACTICES

### **NEVER DO THIS:**
1. ❌ Create files in root (except those listed above)
2. ❌ Leave `.cmo`, `.cmx`, `.o` files in source tree
3. ❌ Commit backup files (`*.bak`, `*.backup`, `*.old`)
4. ❌ Mix layers (L0 code in L1 directory, etc.)
5. ❌ Create "temporary" files without cleanup
6. ❌ Use inconsistent naming conventions
7. ❌ Create new top-level directories without documentation

### **ALWAYS DO THIS:**
1. ✅ Run `make clean` before committing
2. ✅ Use `.gitignore` patterns for new file types
3. ✅ Archive old documents to `docs/archive/`
4. ✅ Follow layer separation strictly
5. ✅ Update `DOCUMENTATION_INDEX.md` when adding docs
6. ✅ Use descriptive, consistent file names

---

## 📋 NAMING CONVENTIONS

### **Source Files**
- **Modules**: `lower_snake_case.ml` (e.g., `l0_lexer.ml`)
- **Interfaces**: Same as module with `.mli`
- **Tests**: `test_[feature].ml` (e.g., `test_arena_performance.ml`)

### **Documentation**
- **Guides**: `UPPERCASE_TITLE.md` for major docs
- **Reports**: `lowercase-with-dashes.md` for reports
- **Archives**: Include date: `2025-08-12-cleanup-report.md`

### **Validation Rules**
- **Pattern**: `[category]_rules.ml` (e.g., `typography_rules.ml`)
- **Tests**: `test_[category]_validation.ml`

---

## 🔄 MAINTENANCE PROCEDURES

### **Weekly Cleanup Checklist**
```bash
# 1. Remove build artifacts
make clean

# 2. Check for orphaned files
find . -name "*.bak" -o -name "*.tmp" -o -name "*.old"

# 3. Verify no compiled files in source
find src/ -name "*.cmo" -o -name "*.cmx" -o -name "*.o"

# 4. Check root directory
ls -la | grep -v "^\(README\|CLAUDE\|LICENSE\|Makefile\|dune\|_CoqProject\)"

# 5. Archive old documents
# Move docs > 30 days old to docs/archive/
```

### **Before Each Commit**
```bash
# Run the organization check
./scripts/check_organization.sh

# Clean build artifacts
make clean

# Verify gitignore is working
git status --ignored
```

---

## 🤖 AUTOMATED CHECKS

### **Pre-commit Hook**
Install the pre-commit hook to prevent clutter:
```bash
cp scripts/pre-commit-hook-template .git/hooks/pre-commit
chmod +x .git/hooks/pre-commit
```

### **CI/CD Checks**
The CI pipeline will FAIL if:
- Files exist in root (except allowed list)
- Compiled artifacts in source tree
- Backup files committed
- Documentation index not updated

---

## 📊 ORGANIZATION METRICS

### **Health Indicators**
- **Root files**: ≤ 12 files (only essentials)
- **Source directories**: Exactly 5 layers + support
- **Test coverage**: Each source file has test
- **Documentation**: All features documented

### **Red Flags** 🚩
- Root directory has > 15 files
- `src/` has directories not in architecture
- Finding `*.bak` or `*.tmp` files
- Circular dependencies between layers

---

## 🎯 LONG-TERM STRATEGY

### **Week 1-52: Foundation Phase**
- Strict enforcement of all rules
- Weekly cleanup reviews
- Immediate correction of violations

### **Week 53-104: Expansion Phase**
- Maintain discipline during growth
- Regular architecture reviews
- Refactor if organization degrades

### **Week 105-156: Maturity Phase**
- Organization should be automatic
- Focus on optimization not cleanup
- Prepare for long-term maintenance

---

## 📝 ENFORCEMENT

### **Code Review Checklist**
- [ ] No new files in root?
- [ ] Correct layer placement?
- [ ] Tests included?
- [ ] Documentation updated?
- [ ] No backup files?
- [ ] Clean build artifacts?

### **Merge Requirements**
PRs will be **BLOCKED** if:
1. Files added to root (except allowed)
2. Cross-layer dependencies introduced
3. Build artifacts committed
4. Documentation not updated

---

## 🚀 QUICK REFERENCE

### **Where Does This Go?**
| File Type | Location |
|-----------|----------|
| New L0 lexer feature | `src/core/l0_lexer/` |
| New validation rule | `src/validators/` |
| Performance test | `test/performance/` |
| Architecture doc | `docs/developer/` |
| Old analysis report | `docs/archive/[date]/` |
| Build output | `build/` (git ignored) |
| Temporary file | `/tmp/` (NOT in project) |

### **Emergency Cleanup**
```bash
# Nuclear option - clean everything
make distclean
git clean -fdx --dry-run  # Preview
git clean -fdx             # Execute (CAREFUL!)
```

---

## ✅ COMPLIANCE

**By following these guidelines, the project will remain organized for 156 weeks and beyond.**

Remember: **A clean codebase is a fast codebase.**

---

*Guidelines Version: 1.0*  
*Next Review: Week 5 checkpoint*  
*Owner: Project Lead*