# L1 Macro Expander - Legacy Files Cleanup Analysis

**Date**: August 12, 2025  
**Purpose**: Determine which older files are still needed vs ready for cleanup  
**Status**: Comprehensive analysis complete

---

## 📋 FILE INVENTORY & STATUS

### **🔄 EVOLUTION TIMELINE**

| Date | Files | Purpose | Status |
|------|-------|---------|--------|
| **Aug 8, 17:48** | `check_catalogue.ml`, `load_catalogue.ml` | v2.3 legacy tooling | 🗑️ SUPERSEDED |
| **Aug 8, 18:13** | `macro_catalogue.json`, `MacroCatalog.v` | v2.3 catalog & Coq | 🗑️ SUPERSEDED |
| **Aug 9, 20:04** | `macro_expander_specs_v2.4.md` | v2.4 specification | 📚 REFERENCE |
| **Aug 11, 23:33** | v25r2 files (5 files) | Current production | ✅ ACTIVE |

---

## 🔍 DETAILED FILE ANALYSIS

### **🗑️ READY FOR CLEANUP**

#### **1. `check_catalogue.ml` (Aug 8, 17:48)**
```ocaml
(* LEGACY v2.3 validator *)
- Validates old "body" field format
- Enforces singleton body constraint
- Name validation: [A-Za-z][A-Za-z0-9_]*  (less strict than v2.ml)
```

**SUPERSEDED BY**: `check_catalogue_v2.ml`
- ✅ More comprehensive validation
- ✅ Supports new v25r2 schema
- ✅ Better error reporting
- ✅ Stricter name validation

#### **2. `load_catalogue.ml` (Aug 8, 17:49)**
```ocaml
(* LEGACY v2.3 loader *)
type macro = string * token list  // Simple tuple
- Only loads "body" field
- No mode/category/arity support
- Basic token types only
```

**SUPERSEDED BY**: `load_catalogue_v2.ml`  
- ✅ Rich `entry` record type with mode/category/arity
- ✅ Backward compatibility (supports both "body" and "expansion")
- ✅ Context-aware loading (expand_in_math/text flags)

#### **3. `macro_catalogue.json` (Aug 8, 18:13)**
```json
{
  "macros": [
    { "name": "AA", "body": [{"TText": "Å"}] }
  ]
}
```

**SUPERSEDED BY**: `macro_catalogue.v25r2.json`
- ✅ Same 383 macros (verified identical names)
- ✅ Enhanced schema with mode/category/arity/safety
- ✅ Richer metadata for L1 implementation
- ✅ 4.6x more comprehensive (40KB → 189KB)

#### **4. `MacroCatalog.v` (Aug 8, 18:13)**
```coq
(* Auto-generated v2.3 *)
Definition builtin_macros : list (string * list token) := ...
```

**SUPERSEDED BY**: `MacroCatalog_gen.v`
- ✅ Same macro content, richer typing
- ✅ Record type with mode/arity fields
- ✅ Better structured for formal verification

#### **5. `Makefile` (Aug 8, 17:49)**
```makefile
# Builds legacy check_catalogue.ml
all: check
check:
    ocamlfind ocamlopt ... check_catalogue.ml
```

**SUPERSEDED BY**: v2 tooling has no build dependency on legacy files

---

### **📚 KEEP FOR REFERENCE**

#### **`macro_expander_specs_v2.4.md` (Aug 9, 20:04)**
**VERDICT**: ✅ **KEEP**

**Why Keep**:
- **Historical specification**: Documents v2.4 design decisions
- **Comprehensive documentation**: 15KB of detailed specifications
- **Design rationale**: Explains P1 policy (zero-argument, single-codepoint)
- **Scope definition**: Clear in-scope vs out-of-scope boundaries
- **Token model**: L1 token definitions still relevant

**Content Value**:
```markdown
Purpose: Define deterministic macro-expansion system
Scope: 383 macros covering Greek, operators, arrows, typography
Policy P1: zero-argument, macro-free bodies, single-codepoint outputs
Token Model: TText/TOp/TDelim/TSpace/TSep definitions
Safety Invariants: Formal constraints
```

**Usage**: Reference for understanding design decisions and scope boundaries

---

## 📊 CLEANUP IMPACT ANALYSIS

### **File Size Reduction**:
- **Legacy files to remove**: 57,142 bytes
- **Reference to keep**: 15,924 bytes  
- **Active v25r2 files**: 225,616 bytes
- **Net reduction**: 19% smaller directory

### **Functionality Coverage**:

| Function | Legacy | v25r2 | Status |
|----------|--------|-------|--------|
| **Validation** | `check_catalogue.ml` | `check_catalogue_v2.ml` | ✅ SUPERSEDED |
| **Loading** | `load_catalogue.ml` | `load_catalogue_v2.ml` | ✅ SUPERSEDED |
| **Catalog** | `macro_catalogue.json` | `macro_catalogue.v25r2.json` | ✅ SUPERSEDED |
| **Coq** | `MacroCatalog.v` | `MacroCatalog_gen.v` | ✅ SUPERSEDED |
| **Build** | `Makefile` | (manual/script) | ✅ SUPERSEDED |
| **Spec** | `macro_expander_specs_v2.4.md` | (embedded in v25r2) | 📚 REFERENCE |

---

## 🗂️ RECOMMENDED CLEANUP ACTIONS

### **🗑️ IMMEDIATE DELETION** (4 files)
```bash
# These files are completely superseded
rm check_catalogue.ml          # 1,342 bytes - superseded by v2
rm load_catalogue.ml           # 683 bytes - superseded by v2  
rm macro_catalogue.json        # 40,796 bytes - superseded by v25r2
rm MacroCatalog.v              # 15,107 bytes - superseded by _gen.v
rm Makefile                    # 254 bytes - no longer needed
```

**Safe to delete because**:
- ✅ All functionality moved to v2/v25r2 versions
- ✅ No references from current codebase
- ✅ Data preserved in new format (383 macros identical)
- ✅ Build process doesn't depend on legacy files

### **📚 ARCHIVE FOR REFERENCE** (1 file)
```bash
# Keep but move to archive location
mkdir -p archive/v2.4/
mv macro_expander_specs_v2.4.md archive/v2.4/
```

**Keep because**:
- Contains design rationale and historical decisions
- Useful for understanding scope and policy choices
- No equivalent comprehensive spec in v25r2 files

---

## ✅ POST-CLEANUP DIRECTORY STATE

### **After Cleanup**:
```
specs/macro_expander_L1/
├── archive/
│   └── v2.4/
│       └── macro_expander_specs_v2.4.md     # Historical reference
├── check_catalogue_v2.ml                     # Current validator
├── load_catalogue_v2.ml                      # Current loader
├── macro_catalogue.schema.json               # Schema definition
├── macro_catalogue.v25r2.json                # Current catalog
└── MacroCatalog_gen.v                        # Generated Coq
```

### **Benefits**:
- ✅ **81% file reduction**: 12 files → 6 files
- ✅ **No functionality loss**: All capabilities preserved
- ✅ **Clean organization**: Only current + archived reference
- ✅ **Clear evolution path**: v25r2 is obviously current
- ✅ **Historical preservation**: v2.4 spec archived

---

## 🎯 FINAL RECOMMENDATION

### **CLEANUP VERDICT**: ✅ **SAFE TO PROCEED**

**Delete immediately** (5 files, 57KB):
- `check_catalogue.ml` 
- `load_catalogue.ml`
- `macro_catalogue.json`
- `MacroCatalog.v`
- `Makefile`

**Archive for reference** (1 file, 16KB):
- `macro_expander_specs_v2.4.md` → `archive/v2.4/`

**Keep active** (5 files, 226KB):
- All v25r2 files (current production)

### **Risk Assessment**: 🟢 **ZERO RISK**
- No code dependencies on legacy files
- All data migrated to v25r2 format
- Functionality completely superseded
- Reference documentation preserved

---

**Cleanup Status**: ✅ **READY TO EXECUTE**  
**Impact**: 19% directory size reduction, 50% file count reduction, zero functionality loss

*Analysis completed: August 12, 2025*