# Appendix E — SIMD Implementation Notes

Per v25 master plan §15, Table E (11 pages).

## E.1 Architecture Overview

The SIMD subsystem provides hardware-accelerated tokenization and hashing for the L0 lexer layer. Three tiers are supported:

| Tier | ISA | Target | Throughput |
|------|-----|--------|------------|
| Tier A | Scalar (pure OCaml) | All platforms | baseline |
| Tier B | NEON (ARM) | Apple Silicon, ARM servers | 6x baseline |
| Tier C | AVX-512 (x86) | Intel/AMD servers | 10x baseline |

Runtime feature detection selects the fastest available tier. Fallback is always Tier A.

## E.2 Catcode Scanner

**Purpose**: Classify each byte of input into one of 16 TeX category codes using a lookup table.

**Implementation**: `core/l0_lexer/simd/catcode_avx2.S`, `catcode_neon.S`

**Algorithm**:
1. Load 16/32/64 bytes into SIMD register
2. Use `vpshufb` (AVX2) or `vtbl` (NEON) as parallel LUT lookup
3. Store catcode results to output array
4. Advance pointer by register width

**Scalar fallback** (`latex-parse/src/catcode.ml`):
```
classify_char : char -> catcode
```
Single byte → catcode via match statement. Proven total in `proofs/Catcode.v`.

## E.3 xxHash (xxh64)

**Purpose**: Fast content hashing for cache keys and dirty-region detection.

**Implementation**: `latex-parse/src/xxh64.ml` (OCaml), `core/l0_lexer/src/scan_simd.rs` (Rust)

**Targets**:
- Scalar: 2 GB/s
- SIMD: 20 GB/s (AVX2), 15 GB/s (NEON)

**Self-check**: `xxh-selfcheck` CI job verifies OCaml and Rust implementations produce identical hashes on reference inputs.

## E.4 Memory Layout

**SoA (Structure of Arrays)** layout for token storage:
- `kinds : catcode array` — 1 byte per token
- `offsets : int array` — 4 bytes per token (byte offset in source)
- `lengths : int array` — 2 bytes per token

64-byte alignment for cache-line efficiency. AoS (Array of Structures) fallback for platforms without alignment guarantees.

## E.5 Performance Measurement

**Benchmark suite**: `scripts/bench_simd.sh`

| Benchmark | Scalar | NEON | AVX2 |
|-----------|--------|------|------|
| catcode_scan (1 MB) | 3.2 ms | 0.53 ms | 0.32 ms |
| xxh64 (1 MB) | 0.49 ms | 0.067 ms | 0.050 ms |
| full_lex (1.1 MB) | 8.36 ms | 1.4 ms | 0.84 ms |

Hardware baseline: M2-Pro, 3.5 GHz, 32 GiB RAM.

## E.6 Proof Obligations

| File | Theorem | Status |
|------|---------|--------|
| `Catcode.v` | `nat_catcode_inverse` — LUT is bijective | QED |
| `Catcode.v` | `catcode_eq_dec` — decidable equality | QED |
| `LexerDeterminism.v` | Scalar lexer is deterministic | QED |
| `LexerTotality.v` | Every byte consumed, no stuck states | QED |
| (future) `Lexer_simd_equiv.v` | SIMD output ≡ scalar | Stub (W120) |

## E.7 Build Instructions

```bash
# OCaml scalar (always available)
dune build latex-parse

# Rust SIMD proxy
cd rust-proxy && cargo build --release

# Benchmark
./scripts/bench_simd.sh
```

## E.8 Tool-chain Requirements

- OCaml 5.1.1+ (for Atomic module in lock-free queue)
- Rust 1.75+ (for SIMD intrinsics stabilisation)
- NASM or GAS (for assembly kernels, optional)
- `perf` or Instruments.app for profiling
