# ULTRATHINK CLEANUP EXECUTION PLAN

**Phase 3: Systematic Cleanup**  
**Date**: August 14, 2025

---

## **CLEANUP CATEGORIES**

### **1. BUILD ARTIFACTS (Safe to Remove)**
```bash
# OCaml compiled files
*.cmi *.cmx *.o *.cmo 

# Coq compiled files  
*.vo *.vos *.vok *.glob

# C object files
*.so *.a
```

### **2. BACKUP FILES (Archive Further)**
```bash
# Timestamped backups
*.backup.20250813_000642

# Legacy versions
*.old *.broken

# Temporary files
*~ *.tmp *.temp
```

### **3. DUPLICATE DIRECTORIES (Consolidate)**
```
CURRENT ISSUES:
src/validation/     vs    src/validators/    vs    src/validator/
src/l0_lexer/      vs    src/core/layer0/   vs    src/core/lexer/
src/l1_expander/   vs    src/core/layer1/

SOLUTION: Consolidate into src/core/ hierarchy
```

### **4. EMPTY DIRECTORIES (Remove)**
```
src/arena/         ❌ Empty
src/elder/         ❌ Empty  
src/event_bus/     ❌ Empty
src/lexer_simd/    ❌ Empty
src/lib/           ❌ Empty
src/memory/        ❌ Empty
src/sem/           ❌ Empty
src/style/         ❌ Empty
```

---

## **EXECUTION PLAN**

### **Step 1: Build Artifact Cleanup**
Target: Remove all .cmi, .cmx, .o, .cmo, .vo, .vos, .vok, .glob files from main directories (preserve archives)

### **Step 2: Backup File Archival**  
Target: Move *.backup.*, *.old, *.broken to archive/cleanup-2025-08-14/

### **Step 3: Empty Directory Removal**
Target: Remove empty src/ subdirectories  

### **Step 4: Duplicate Resolution**
Target: Identify primary implementations and archive alternatives

---

## **SAFETY CHECKS**

### **PRESERVE THESE FILES** ✅
- `latex_perfectionist_cli_phase3_ultra` (working binary)
- `benchmark_phase3_p99_robust` (working binary)  
- All .ml/.mli source files
- All .v proof files
- All .md documentation
- All .json/.yaml configuration files

### **ARCHIVE NOT DELETE** ✅  
- Move problematic files to archive/ instead of deletion
- Preserve project history
- Allow rollback if needed

### **TEST AFTER CLEANUP** ✅
- Verify production CLI still works
- Run benchmark validation  
- Check build system functionality

---

**Ready for Execution** - Proceeding with Step 1 ✅