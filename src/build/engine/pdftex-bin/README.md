# LaTeX Perfectionist v24 - pdfTeX Engine Directory

## V24-R3 Specification Requirements

This directory should contain the frozen pdfTeX binary and verification files as specified in the v24-R3 architecture document:

### Required Files

1. **pdftex** (binary)
   - Version: pdfTeX 1.40.26
   - Frozen binary for reproducible builds
   - Platform-specific executable

2. **pdftex.sha256**
   - SHA-256 hash of the binary
   - Container SHA256: `b68d...(full 256-bit hash)`
   - Used for verification and integrity checking

3. **pdftex.version**
   - Version information file
   - Build timestamp and configuration
   - Used for compatibility checking

### Security Model

The frozen binary ensures:
- No shell escape capabilities (`--shell-escape` disabled)
- Workspace-relative file access only
- No network access
- No `write18` functionality

### Usage Notes

- Binary is called with `--no-shell-escape --interaction=nonstopmode`
- Input restricted to workspace `*.tex` files only
- Fallback to classic TeX compile on LaTeX epsilon perimeter violations
- UI shows yellow shield badge when falling back

### Implementation Status

**Current Status**: PLACEHOLDER STRUCTURE
- Directory structure: ✅ Created
- Binary files: ❌ Not included (licensing/distribution restrictions)
- Verification hashes: ❌ Awaiting actual binary
- Version metadata: ❌ Awaiting actual binary

### Production Deployment

For production deployment:
1. Obtain pdfTeX 1.40.26 binary for target platform
2. Generate SHA-256 hash and store in `pdftex.sha256`
3. Create version metadata file
4. Update container configuration with full SHA-256
5. Test with adversarial test suite