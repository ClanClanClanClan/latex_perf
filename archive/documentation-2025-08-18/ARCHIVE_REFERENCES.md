# ARCHIVE REFERENCES

**Date**: August 18, 2025  
**Action**: Moved archives external for v25_R1 compliance

## External Archive Locations

**Primary Archive**: `../LaTeX-Perfectionist-Archives-20250818/archive/`
- **Size**: 73MB
- **Content**: Development history, obsolete binaries, session reports
- **Reason**: v25_R1 requires repository <200MB; archives moved external

## Archive Structure Moved

```
../LaTeX-Perfectionist-Archives-20250818/archive/
├── cleanup-artifacts-2025-08-14/          # 25MB - Build artifacts
├── layer-reorganization-2025-08-14/       # 18MB - Old implementations  
├── obsolete-binaries-2025-08-14/          # 20MB - Compiled binaries
├── session-reports-2025-08-14/            # 10MB - Historical reports
└── old-build-directory-2025-08-14/        # Additional artifacts
```

## Access Instructions

If you need to reference archived materials:
1. Access: `cd ../LaTeX-Perfectionist-Archives-20250818/archive/`
2. Key historical documents remain in `session-reports-2025-08-14/`
3. Important implementations preserved in `layer-reorganization-2025-08-14/`

## Repository Size Impact

- **Before**: 185MB total (73MB archives)
- **After**: 112MB (39% reduction)
- **v25_R1 Target**: <200MB ✅ **ACHIEVED**

This cleanup maintains project history while achieving v25_R1 repository size compliance.