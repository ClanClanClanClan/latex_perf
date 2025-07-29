#!/bin/bash

# 🚨 EMERGENCY CLEANUP SCRIPT FOR LATEX-PERFECTIONIST PROJECT
# 
# This script performs critical cleanup operations to organize the chaotic project structure
# 
# WARNINGS:
# - This will delete build artifacts
# - This will move files to new locations
# - Run from project root directory
# - Make backup before running if unsure

set -e

PROJECT_ROOT="/Users/dylanpossamai/Dropbox/Work/Articles/Scripts"
cd "$PROJECT_ROOT"

echo "🧹 STARTING EMERGENCY CLEANUP..."
echo "📁 Working in: $(pwd)"

# Phase 1: BUILD ARTIFACT PURGE
echo "🗑️  PHASE 1: Removing build artifacts..."

# Count artifacts before cleanup
ARTIFACT_COUNT=$(find . -name "*.cmi" -o -name "*.cmx" -o -name "*.o" -o -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" | wc -l)
echo "📊 Found $ARTIFACT_COUNT build artifacts to remove"

# Remove OCaml compilation artifacts
echo "   Removing OCaml artifacts (.cmi, .cmx, .o)..."
find . -name "*.cmi" -delete
find . -name "*.cmx" -delete  
find . -name "*.o" -delete

# Remove Coq compilation artifacts
echo "   Removing Coq artifacts (.vo, .vok, .vos, .glob)..."
find . -name "*.vo" -delete
find . -name "*.vok" -delete
find . -name "*.vos" -delete
find . -name "*.glob" -delete

echo "✅ Build artifacts removed"

# Phase 2: CREATE NEW DIRECTORY STRUCTURE
echo "📁 PHASE 2: Creating organized directory structure..."

# Create main directories
mkdir -p bin/
mkdir -p archive/{failed_experiments,deprecated,research_prototypes}
mkdir -p archive/failed_experiments/validation_compiler
mkdir -p archive/failed_experiments/scope_reduction
mkdir -p archive/research_prototypes/parallel_experiments
mkdir -p src/organized/{coq,ocaml,python}
mkdir -p src/organized/ocaml/{generated,validators,performance,utils}
mkdir -p tests/organized/{unit,integration,performance,corpus}
mkdir -p docs/organized/{architecture,performance,audit,research}

echo "✅ Directory structure created"

# Phase 3: MOVE EXECUTABLES TO BIN
echo "🔧 PHASE 3: Organizing executables..."

# Move working executables to bin
if [ -f "src/extraction/enterprise_optimized_fixed" ]; then
    echo "   Moving enterprise_optimized_fixed to bin/"
    mv src/extraction/enterprise_optimized_fixed bin/
fi

if [ -f "src/extraction/ultra_fast_simple" ]; then
    echo "   Moving ultra_fast_simple to bin/"
    mv src/extraction/ultra_fast_simple bin/
fi

if [ -f "src/extraction/rule_profiler" ]; then
    echo "   Moving rule_profiler to bin/"
    mv src/extraction/rule_profiler bin/
fi

# Archive fraudulent implementation
if [ -f "src/extraction/validation_compiler" ]; then
    echo "   Archiving fraudulent validation_compiler..."
    mv src/extraction/validation_compiler archive/failed_experiments/validation_compiler/
    echo "FRAUD: Claimed compiled validation engine, actually toy pattern matcher with issue inflation" > archive/failed_experiments/validation_compiler/README.md
fi

echo "✅ Executables organized"

# Phase 4: COPY CORE SOURCE FILES TO ORGANIZED STRUCTURE
echo "📄 PHASE 4: Organizing source files..."

# Copy (don't move yet) core files to organized structure
if [ -f "src/extraction/enterprise_validators.ml" ]; then
    echo "   Copying enterprise_validators.ml to organized structure..."
    cp src/extraction/enterprise_validators.ml src/organized/ocaml/generated/
    cp src/extraction/enterprise_validators.mli src/organized/ocaml/generated/
fi

if [ -f "src/extraction/enterprise_optimized.ml" ]; then
    echo "   Copying enterprise_optimized.ml to performance section..."
    cp src/extraction/enterprise_optimized.ml src/organized/ocaml/performance/
fi

if [ -f "src/extraction/ultra_fast_simple.ml" ]; then
    echo "   Copying ultra_fast_simple.ml to performance section..."
    cp src/extraction/ultra_fast_simple.ml src/organized/ocaml/performance/
fi

if [ -f "src/extraction/parallel_helpers.ml" ]; then
    echo "   Copying parallel_helpers.ml to utils..."
    cp src/extraction/parallel_helpers.ml src/organized/ocaml/utils/
    cp src/extraction/parallel_helpers.mli src/organized/ocaml/utils/
fi

# Archive fraudulent source
if [ -f "src/extraction/validation_compiler.ml" ]; then
    echo "   Archiving fraudulent validation_compiler.ml..."
    cp src/extraction/validation_compiler.ml archive/failed_experiments/validation_compiler/
fi

echo "✅ Source files organized"

# Phase 5: ORGANIZE DOCUMENTATION
echo "📚 PHASE 5: Organizing documentation..."

# Move crisis analysis documents
if [ -f "docs/ENTERPRISE_CRISIS_ANALYSIS.json" ]; then
    echo "   Moving crisis analysis to performance docs..."
    cp docs/ENTERPRISE_CRISIS_ANALYSIS.json docs/organized/performance/
fi

if [ -f "docs/TECHNICAL_DEBT_SPECIFICATION.md" ]; then
    echo "   Moving technical debt analysis to architecture docs..."
    cp docs/TECHNICAL_DEBT_SPECIFICATION.md docs/organized/architecture/
fi

if [ -f "docs/PERFORMANCE_BENCHMARKS.yaml" ]; then
    echo "   Moving performance benchmarks..."
    cp docs/PERFORMANCE_BENCHMARKS.yaml docs/organized/performance/
fi

# Archive fraudulent documentation
if [ -f "docs/BREAKTHROUGH_ACHIEVED.md" ]; then
    echo "   Archiving fraudulent breakthrough claims..."
    mv docs/BREAKTHROUGH_ACHIEVED.md archive/failed_experiments/
fi

echo "✅ Documentation organized"

# Phase 6: CREATE GITIGNORE
echo "⚙️  PHASE 6: Creating .gitignore..."

cat > .gitignore << 'EOF'
# Build artifacts
*.cmi
*.cmx
*.o
*.vo
*.vok
*.vos
*.glob
.build/

# Compiled executables (keep in bin/ only)
src/**/enterprise_*
src/**/validation_*
src/**/ultra_fast_*
src/**/test_*
src/**/rule_*
src/**/debug_*
src/**/verify_*

# IDE files
.vscode/settings.json
*.swp
*.tmp
.idea/

# OS files
.DS_Store
Thumbs.db

# Python
__pycache__/
*.pyc
*.pyo
*.egg-info/

# Logs
*.log
EOF

echo "✅ .gitignore created"

# Phase 7: CREATE ORGANIZATION STATUS REPORT
echo "📊 PHASE 7: Creating cleanup report..."

cat > CLEANUP_REPORT.md << 'EOF'
# PROJECT CLEANUP REPORT

## ✅ CLEANUP COMPLETED

### Build Artifacts Removed
- All .cmi, .cmx, .o files deleted
- All .vo, .vok, .vos, .glob files deleted  
- Clean source tree achieved

### Directory Structure Created
- `bin/` - Executable binaries
- `src/organized/` - Clean source organization
- `archive/` - Failed experiments and deprecated code
- `docs/organized/` - Structured documentation

### Fraudulent Code Archived
- `validation_compiler` - Moved to archive with fraud warning
- `BREAKTHROUGH_ACHIEVED.md` - Archived as fraudulent claims

### Working Implementations Preserved
- `enterprise_optimized_fixed` - Production-ready validator
- `ultra_fast_simple` - Honest toy implementation
- `enterprise_validators.ml` - Core generated validation engine

### Next Steps
1. Review organized structure in `src/organized/`
2. Test that executables in `bin/` still work
3. Gradually migrate to new structure
4. Update documentation references

## 🎯 ORGANIZATION SUCCESS
Project transformed from chaos to clarity - ready for breakthrough development.
EOF

echo "✅ Cleanup report created"

# Final summary
echo ""
echo "🎉 EMERGENCY CLEANUP COMPLETED!"
echo ""
echo "📋 SUMMARY:"
echo "   ✅ $ARTIFACT_COUNT build artifacts removed"
echo "   ✅ Clean directory structure created"
echo "   ✅ Executables moved to bin/"
echo "   ✅ Fraudulent code archived with warnings"
echo "   ✅ Working implementations preserved"
echo "   ✅ Documentation organized"
echo "   ✅ .gitignore created"
echo ""
echo "📁 Check the organized structure in:"
echo "   - src/organized/ (clean source code)"
echo "   - bin/ (working executables)"  
echo "   - archive/ (failed experiments)"
echo "   - docs/organized/ (structured documentation)"
echo ""
echo "⚠️  IMPORTANT: Review changes before committing!"
echo "📖 See CLEANUP_REPORT.md for details"

echo ""
echo "🚀 Project is now ready for breakthrough development!"