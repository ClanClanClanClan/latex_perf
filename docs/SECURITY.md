# Security Policy — LaTeX Perfectionist v25

## Supported Versions

| Version | Supported |
|---------|-----------|
| v25.x   | ✅ Active development |
| < v25   | ❌ End of life |

## Reporting Vulnerabilities

If you discover a security vulnerability, please report it responsibly:

1. **Do NOT** open a public GitHub issue
2. Email: security@latex-perfectionist.dev (or use GitHub Security Advisories)
3. Include: description, reproduction steps, impact assessment
4. Expected response: within 72 hours

## Security Measures

### Sandboxing (§11 of v25_master.md)

Runtime sandboxing via seccomp profile: `scripts/sandbox/seccomp.json`

The profile restricts the validator runtime to a minimal syscall allowlist:
- File I/O (read, write, open, close, stat)
- Memory management (mmap, mprotect, munmap, brk)
- Networking (socket, connect — for REST API and IPC)
- Process management (clone, fork, exit)
- Time (clock_gettime, gettimeofday)

### Supply Chain

- **SBOM**: CycloneDX JSON generated in CI (`latex-perfectionist.yml` security job)
- **Dependencies**: Pinned via `dune-project` (Coq = 8.18.0, OCaml >= 5.1.1)
- **Actions**: All GitHub Actions pinned to v4+ with SHA verification

### FFI Boundaries

C extensions in `latex-parse/src/` (SIMD stubs, clock, hedge timer) are wrapped with:
- Input validation (size checks before buffer access)
- `caml_enter_blocking_section` / `caml_leave_blocking_section` for long operations
- No user-controlled input reaches FFI without sanitization

### Code Signing

Release artifacts will be signed with Cosign (planned for W151-155 release engineering phase).
Public key will be published here upon first signed release.

## Vulnerability Disclosure Timeline

1. Report received → acknowledge within 72h
2. Triage and impact assessment → within 1 week
3. Fix developed and tested → within 2 weeks
4. Advisory published → upon fix release
