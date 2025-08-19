# 🧹 MAINTENANCE QUICK REFERENCE

**For Claude Code Sessions - Keep this handy!**

---

## ⚡ INSTANT HEALTH CHECK
```bash
./scripts/check_organization.sh
```
**Expected**: "🎉 PERFECT! Organization is pristine."

---

## 🚀 SESSION START (EVERY TIME)

```bash
# 1. Organization check
./scripts/check_organization.sh

# 2. If ANY issues, run cleanup
make clean && rm -rf _build .DS_Store && find . -name "*.bak" -delete

# 3. Verify fixed
./scripts/check_organization.sh  # Must show PERFECT
```

---

## ✅ BEFORE COMMITS

```bash
# MANDATORY check
./scripts/check_organization.sh

# If errors: DO NOT COMMIT
# Fix all issues first!
```

---

## 🔥 EMERGENCY CLEANUP

### **Light Cleanup** (safe)
```bash
make clean
rm -rf _build
rm .DS_Store
find . -name "*.bak" -o -name "*.tmp" -delete
```

### **Deep Cleanup** (careful)
```bash
make distclean
git clean -fdx --dry-run  # PREVIEW first
git clean -fdx             # Execute (DANGEROUS)
```

---

## 📋 GOLDEN RULES

### **NEVER** ❌
- Put files in root (except allowed list)
- Leave .cmo/.cmx in source
- Commit backup files
- Mix layer code (L0 in L1, etc)
- Create "temp" files without cleanup

### **ALWAYS** ✅
- Run check before commits
- Keep layers separate
- Use proper directories
- Clean build artifacts
- Update documentation

---

## 📁 WHERE THINGS GO

| What | Where |
|------|-------|
| New L0 code | `src/core/l0_lexer/` |
| New L1 code | `src/core/l1_expander/` |
| New validator | `src/validators/` |
| New test | `test/unit/` or `test/integration/` |
| Performance test | `test/performance/` |
| Documentation | `docs/` |
| Old docs | `docs/archive/[date]/` |

---

## 🔗 ESSENTIAL DOCS

- **Full Guidelines**: `docs/developer/ORGANIZATION_GUIDELINES.md`
- **Health Checker**: `scripts/check_organization.sh`
- **Main Instructions**: `CLAUDE.md`

---

## 🎯 SUCCESS CRITERIA

```
✅ Root directory clean
✅ No build artifacts in source
✅ No backup/temp files
✅ Layer separation maintained
✅ Documentation current
✅ Naming conventions followed
✅ 3 admits only (tactical helpers)
```

---

**Remember**: A clean project is a fast project!

*Keep running `./scripts/check_organization.sh` until it's PERFECT!*