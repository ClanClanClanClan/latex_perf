# Appendix E -- SIMD Implementation Notes

Revision 2026-04-05. Engineering guidance for the optional Rust/SIMD acceleration
layer with OCaml FFI bindings.

Objective: keep `perf_smoke` p95 under 25 ms (full 1.1 MB document) and under
1 ms (4 KiB edit window), with portable scalar fallbacks and strict correctness
parity against the Coq-proven OCaml reference path.

---

## E-1 Where SIMD Is Used

The spec defines five kernel families. The current implementation covers two of
them natively; the remaining three are approximated by the scalar OCaml path.

| # | Kernel | Spec Status | Implementation Status |
|---|--------|-------------|----------------------|
| 1 | Byte-class scanners (ASCII/punctuation/quote/dash) | Spec E-4.1 | **Scalar OCaml** (`catcode.ml`) -- proven total in `Catcode.v` |
| 2 | xxHash content hashing | Spec E-4.4 | **Dual path**: scalar OCaml (`xxh64.ml`) + Rust SIMD FFI (`xxh64_simd`) |
| 3 | UTF-8 fast-path validation | Spec E-4.2 | **Scalar OCaml** (`tokenizer_lite.ml:decode_uchar_at`) |
| 4 | Multi-pattern memchr probes | Spec E-4.4 | **Scalar OCaml** via `Str.regexp` |
| 5 | Delimiter balance pre-scan | Spec E-4.5 | **Scalar OCaml** (`parser_l2.ml`) |

The scalar path is always available and is the proven-correct reference. SIMD
acceleration is opt-in via the `L0_USE_SIMD_XXH` environment variable (xxHash
only) or by linking the Rust proxy for the full catcode scanner.

---

## E-2 Catcode Scanner (`catcode.ml`)

### E-2.1 Algorithm

The catcode scanner classifies each input byte into one of 16 TeX category codes
using a direct `match` statement. This mirrors the Coq model in `Catcode.v`.

```ocaml
(* latex-parse/src/catcode.ml *)
let classify_ascii (b : int) : int =
  match b land 0xFF with
  | 92  -> cc_escape     (* \ *)
  | 123 -> cc_beginGrp   (* { *)
  | 125 -> cc_endGrp     (* } *)
  | 36  -> cc_math       (* $ *)
  | 38  -> cc_alignTab   (* & *)
  | 10 | 13 -> cc_newline
  | 35  -> cc_param      (* # *)
  | 94  -> cc_superscr   (* ^ *)
  | 95  -> cc_subscr     (* _ *)
  | 0   -> cc_ignored    (* NUL *)
  | 32 | 9 -> cc_space   (* space/tab *)
  | 126 -> cc_active     (* ~ *)
  | 37  -> cc_comment    (* % *)
  | 127 -> cc_invalid    (* DEL *)
  | c when is_letter c -> cc_letter
  | _   -> cc_other
```

Integer codes 0--15 correspond to the Coq `catcode` inductive type. The mapping
is proven bijective:

```coq
(* proofs/Catcode.v *)
Lemma nat_catcode_inverse : forall c,
  nat_to_catcode (catcode_to_nat c) = Some c.
Proof. destruct c; reflexivity. Qed.
```

### E-2.2 Spec SIMD Kernel (Not Yet Implemented)

The spec describes a vectorised scanner using `vpshufb` (AVX2) or `vtbl` (NEON)
as a parallel 16-entry LUT. Each SIMD register processes 32/64 bytes
simultaneously, writing catcode results to an output array.

This kernel is not yet implemented. The scalar OCaml path handles all catcode
classification. A future `Lexer_simd_equiv.v` proof will establish bit-for-bit
equivalence between the vectorised and scalar paths.

---

## E-3 xxHash (`xxh64.ml`)

### E-3.1 Purpose

Fast content hashing for cache keys (`cache_key.ml`) and dirty-region detection.
xxHash64 provides collision resistance sufficient for cache indexing without
cryptographic overhead.

### E-3.2 Scalar Implementation

`latex-parse/src/xxh64.ml` implements bit-exact scalar xxHash64. The algorithm
processes input in 32-byte stripes with four accumulators:

```ocaml
(* latex-parse/src/xxh64.ml -- key constants *)
let prime1 = 0x9E3779B185EBCA87L
let prime2 = 0xC2B2AE3D27D4EB4FL
let prime3 = 0x165667B19E3779F9L
let prime4 = 0x85EBCA77C2B2AE63L
let prime5 = 0x27D4EB2F165667C5L

let hash64_bytes ?(seed = 0L) (b : bytes) : int64 =
  (* 32-byte stripe loop with four v1..v4 accumulators *)
  (* then 8-byte, 4-byte, and single-byte tails *)
  (* final avalanche mix *)
```

The implementation uses `Bytes.unsafe_get` for zero-bounds-check access in the
hot loop. Little-endian 64-bit and 32-bit loads are inlined via manual byte
shifting (`get64_le`, `get32_le`).

### E-3.3 SIMD FFI Path

```ocaml
external xxh64_simd : bytes -> int64 -> int64 = "ocaml_xxh64_simd"

let hash64 ?seed b =
  match Sys.getenv_opt "L0_USE_SIMD_XXH" with
  | Some "1" -> (
      try hash64_bytes_simd ?seed b
      with Failure _ -> hash64_bytes ?seed b)
  | _ -> hash64_bytes ?seed b
```

The external function `ocaml_xxh64_simd` is provided by the Rust proxy. Dispatch
is controlled by the `L0_USE_SIMD_XXH` environment variable. On failure (e.g.,
missing Rust library), the implementation falls back to the scalar path.

### E-3.4 Correctness Parity

The `xxh-selfcheck` CI job verifies that the OCaml scalar and Rust SIMD
implementations produce identical hashes on a reference input set. This is a
required check in the branch protection rules.

---

## E-4 UTF-8 Handling (`tokenizer_lite.ml`)

### E-4.1 Decode Function

The tokenizer handles multi-byte UTF-8 sequences via `decode_uchar_at`:

```ocaml
(* latex-parse/src/tokenizer_lite.ml *)
let decode_uchar_at (src : string) (i : int) : int * int =
  let b0 = Char.code (String.unsafe_get src i) in
  if b0 land 0x80 = 0 then (b0, 1)                    (* 1-byte ASCII *)
  else if b0 land 0xE0 = 0xC0 && i + 1 < n then ...   (* 2-byte *)
  else if b0 land 0xF0 = 0xE0 && i + 2 < n then ...   (* 3-byte *)
  else if b0 land 0xF8 = 0xF0 && i + 3 < n then ...   (* 4-byte *)
  else (0xFFFD, 1)                                     (* replacement char *)
```

Returns `(codepoint, byte_count)`. Malformed sequences produce U+FFFD with a
1-byte advance to prevent infinite loops.

### E-4.2 Unicode Letter Classification

```ocaml
let is_unicode_letter (cp : int) : bool =
  (cp >= 0xC0   && cp <= 0x24F)  (* Latin Extended *)
  || (cp >= 0x0370 && cp <= 0x03FF) (* Greek *)
  || (cp >= 0x0400 && cp <= 0x04FF) (* Cyrillic *)
  || (cp >= 0x0600 && cp <= 0x06FF) (* Arabic *)
  || (cp >= 0x0750 && cp <= 0x077F) (* Arabic Supplement *)
  || (cp >= 0x3040 && cp <= 0x30FF) (* Hiragana + Katakana *)
  || (cp >= 0x3400 && cp <= 0x4DBF) (* CJK Extension A *)
  || (cp >= 0x4E00 && cp <= 0x9FFF) (* CJK Unified *)
  || (cp >= 0xAC00 && cp <= 0xD7AF) (* Hangul *)
  || (cp >= 0xF900 && cp <= 0xFAFF) (* CJK Compat *)
```

### E-4.3 CJK Word Boundary Rule

CJK codepoints are each treated as individual `Word` tokens (no whitespace
word boundaries in CJK text). Non-CJK Unicode letters accumulate into
multi-character `Word` tokens alongside ASCII letters.

```ocaml
let is_cjk (cp : int) : bool =
  (cp >= 0x3040 && cp <= 0x30FF)     (* Hiragana/Katakana *)
  || (cp >= 0x3400 && cp <= 0x4DBF)  (* CJK Extension A *)
  || (cp >= 0x4E00 && cp <= 0x9FFF)  (* CJK Unified *)
  || (cp >= 0xF900 && cp <= 0xFAFF)  (* CJK Compat *)
  || (cp >= 0x20000 && cp <= 0x2A6DF)(* CJK Extension B *)
```

---

## E-5 Memory Layout

### E-5.1 Token Representation

Tokens use a simple record type with start/end byte offsets:

```ocaml
(* latex-parse/src/tokenizer_lite.ml *)
type kind = Word | Space | Newline | Command | Bracket_open
           | Bracket_close | Quote | Symbol

type tok = { kind : kind; s : int; e : int; ch : char option }
```

Each token is 32 bytes on 64-bit platforms (4-word OCaml record: tag + 3 fields
+ option boxing). This is AoS (Array of Structures) layout.

### E-5.2 Spec SoA Layout (Not Yet Implemented)

The spec describes SoA (Structure of Arrays) with 64-byte alignment:
- `kinds : catcode array` -- 1 byte per token
- `offsets : int array` -- 4 bytes per token
- `lengths : int array` -- 2 bytes per token

This layout is planned for the SIMD-accelerated path where vectorised loads
benefit from homogeneous memory access patterns.

---

## E-6 Proof Obligations

| File | Theorem | Status |
|------|---------|--------|
| `proofs/Catcode.v` | `nat_catcode_inverse` -- 16-entry LUT is bijective | QED |
| `proofs/Catcode.v` | `catcode_eq_dec` -- decidable equality on catcodes | QED |
| `proofs/Catcode.v` | `nat_to_catcode_inv` -- inverse direction | QED |
| `proofs/LexerDeterminism.v` | Scalar lexer produces deterministic output | QED |
| `proofs/LexerTotality.v` | Every byte is consumed; no stuck states | QED |
| `proofs/LexerSmallstep.v` | Small-step lexer semantics | QED |
| `proofs/LexerFaithfulStep.v` | Step-by-step fidelity | QED |
| `proofs/LexerIncremental.v` | Incremental re-lexing correctness | QED |
| `proofs/LexerSoA.v` | SoA layout equivalence | QED |
| (future) `Lexer_simd_equiv.v` | SIMD output = scalar output | Stub |

---

## E-7 Determinism and Parity

The scalar OCaml implementation is the reference. All behaviour is deterministic:

- `catcode.ml:classify_ascii` is a pure function (no state, no IO).
- `xxh64.ml:hash64_bytes` is a pure function with deterministic arithmetic.
- `tokenizer_lite.ml:tokenize` processes input left-to-right with no
  non-determinism.

The CI differential test (`xxh-selfcheck`) runs on every PR and compares the
OCaml and Rust hash outputs on reference inputs. Any divergence fails the build.

Endianness is handled explicitly: `get64_le` and `get32_le` read bytes in
little-endian order regardless of host byte order.

---

## E-8 Benchmark Methodology and Results

### E-8.1 Methodology

- Harness: 100 iterations, drop top/bottom 5, report median and p95.
- Hardware baseline: M2 Pro, 3.5 GHz, 32 GiB RAM (macOS 14).
- CI job: `perf-ci` with gate `p95 <= SLA`.

### E-8.2 Measured Results (2026-02-22, scalar OCaml path)

| Benchmark | Target | Measured |
|-----------|--------|----------|
| Full document A+B (1.1 MB) p95 | <= 20 ms | 3.25 ms |
| First-token p95 | <= 350 us | 27 us |
| Edit-window (4 KB) p95 | <= 3 ms | 0.012 ms |

All measurements are well within SLA on the scalar path alone. The SIMD path
is a future optimization for server-side batch processing.

---

## E-9 Build and CI

### E-9.1 OCaml (always available)

```bash
dune build latex-parse
```

Compiles the full OCaml scanner, tokenizer, and xxHash. No external dependencies
beyond the opam lockfile.

### E-9.2 Rust SIMD Proxy

The Rust proxy is an optional component. When built, it provides `ocaml_xxh64_simd`
via C FFI.

CI enforces:
- `cargo fmt --check` -- formatting
- `cargo clippy -D warnings` -- lint

### E-9.3 CI Required Checks

The following checks are required for merge and relate to SIMD/lexer:

| Check | Purpose |
|-------|---------|
| `xxh-selfcheck` | OCaml/Rust hash parity |
| `l1-smoke` | L1 expansion pipeline smoke test |
| `perf-ci` | Latency regression gate (p95 <= SLA) |
| `proof-ci` | Coq proofs compile with 0 admits |

---

## E-10 Portability

| Platform | Scanner | xxHash | Notes |
|----------|---------|--------|-------|
| macOS arm64 (Apple Silicon) | Scalar OCaml | Scalar OCaml (+ optional Rust SIMD) | Primary dev platform |
| Linux x86-64 | Scalar OCaml | Scalar OCaml (+ optional Rust SIMD) | CI runner |
| Linux arm64 | Scalar OCaml | Scalar OCaml | Container builds |
| Windows x86-64 | Scalar OCaml | Scalar OCaml | Not tested in CI |

The OCaml scalar path requires only OCaml 5.1.1+ (for `Atomic` module used by
`lockfree_queue.ml`). No platform-specific code in the scanner.

---

## E-11 Micro-Optimisations (Applied)

1. `Bytes.unsafe_get` in xxHash hot loop -- skips bounds checks.
2. `String.unsafe_get` in tokenizer -- skips bounds checks after manual
   length guard.
3. `is_letter` uses range comparisons (`c >= 65 && c <= 90`) instead of
   character matching for branch-predictor friendliness.
4. Token list built with cons (`::`), reversed once at end -- avoids
   repeated list traversal.
5. UTF-8 decoder returns byte count alongside codepoint -- eliminates
   redundant length recomputation.

---

End of Appendix E.
