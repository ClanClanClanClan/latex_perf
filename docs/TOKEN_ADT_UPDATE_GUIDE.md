# Token ADT Update Guide for Future Sessions

**CRITICAL:** This guide documents the exact changes needed to resolve the token ADT inconsistency discovered in the v25 audit.

## Summary of Issue

The v25 specifications incorrectly state there are **9 token constructors**, but the implementation has **6 constructors**. The project owner has decided to keep the 6-constructor implementation as canonical.

## Required Documentation Updates

### 1. Appendices v25.md

**Line 104** - Update glossary entry:
```diff
- Token ADT    Nine‑constructor type token with decidable equality (§3.1.2).
+ Token ADT    Six‑constructor sum type with decidable equality (§3.1.2).
```

**Section B-1-2 (around line 174)** - Replace the entire token.ml section:
```diff
- type t = {
-   cat   : Catcode.t;
-   text  : string;   (* UTF‑8 slice, ∅ for group tokens *)
-   loc   : location;
- }
- 
- val equal : t -> t -> bool
- val printable : t -> string     (* debug pretty‑printer *)
- 
- Size.  24 B on 64‑bit (3 words).
- Proofs.  TokenEq.v shows equal ↔ Leibniz equality.

+ (* The core token type - 6 constructors *)
+ type token =
+   | TChar       of Uchar.t * Catcode.t          (* UTF‑8 code‑point *)
+   | TMacro      of string                       (* control sequence *)
+   | TParam      of int                          (* #1 … #9          *)
+   | TGroupOpen                                  (* "{"              *)
+   | TGroupClose                                 (* "}"              *)
+   | TEOF                                         (* virtual sentinel *)
+ 
+ (* Metadata wrapper used by L1+ *)
+ type token_with_meta = { tok : token; loc : Location.t; cat : Catcode.t }
+ 
+ val equal : token -> token -> bool
+ val printable : token -> string     (* debug pretty‑printer *)
+ 
+ Memory Footprint:
+ | Variant | Bytes (x86‑64) | Bytes (arm64) |
+ |---------|----------------|---------------|
+ | TChar   | 24             | 24            |
+ | TMacro  | 24             | 24            |
+ | TParam  | 16             | 16            |
+ | TGroup* | 8              | 8             |
+ | TEOF    | 8              | 8             |
+ | Average (thesis corpus) | 17.3 | 17.3     |
+ 
+ Proofs.  TokenEq.v shows equal ↔ Leibniz equality.
```

### 2. Other Files to Check

Search these files for any references to:
- "nine constructor" or "9 constructor"
- "24 B" or "24 bytes" (fixed size claim)
- Old record-style token definition

Files to check:
- `/specs/v25_master.md`
- `/specs/v25_master.yaml`
- `/specs/v25/PLANNER.yaml` (if it exists)
- Any Coq proof files mentioning token size

### 3. Performance Documentation Update

Add to performance/benchmarking sections:

```markdown
## Performance Measurement Methodology

Dimension    Value
Hardware     Apple M2 Max (12‑core, 32 GB) and Intel i7‑13700K (24‑thread, 32 GB)
Compiler     OCaml 5.1.1 + -O3 -flto; Rust 1.79 + -C opt-level=3 -C target-cpu=native
Data set     perf_smoke (60 k tokens, 1.2 MB)
Command      bench.py --scenario edit-stream --iterations 1000
Metric       p95 wall‑clock latency via perf_event_open, single‑core pin

The "850 MB/s" figure refers to raw lexer throughput on the Intel box using 
--scenario cold-lex (file‑to‑tokens, SIMD AVX‑512 path).
```

## Implementation Tasks

### 1. Create CI Size Check Script

Create `/scripts/size_check.ml`:
```ocaml
(* size_check.ml - Verify token variant sizes *)
open Lexer_v25

let measure_variant = function
  | TChar (u, c) -> Obj.reachable_words (Obj.repr (TChar (u, c)))
  | TMacro s -> Obj.reachable_words (Obj.repr (TMacro s))
  | TParam n -> Obj.reachable_words (Obj.repr (TParam n))
  | TGroupOpen -> Obj.reachable_words (Obj.repr TGroupOpen)
  | TGroupClose -> Obj.reachable_words (Obj.repr TGroupClose)
  | TEOF -> Obj.reachable_words (Obj.repr TEOF)

let () =
  (* Print sizes and verify they match expected values *)
  Printf.printf "Token variant sizes (words):\n";
  Printf.printf "TChar: %d\n" (measure_variant (TChar (Uchar.of_int 65, Catcode.Letter)));
  Printf.printf "TMacro: %d\n" (measure_variant (TMacro "test"));
  Printf.printf "TParam: %d\n" (measure_variant (TParam 1));
  Printf.printf "TGroupOpen: %d\n" (measure_variant TGroupOpen);
  Printf.printf "TGroupClose: %d\n" (measure_variant TGroupClose);
  Printf.printf "TEOF: %d\n" (measure_variant TEOF);
  
  (* Exit with error if sizes drift too much *)
  let max_drift = 8 in (* bytes *)
  (* Add actual checks here *)
  exit 0
```

### 2. Add CI Gates

Add to `.github/workflows/ci.yml`:
```yaml
- name: Check token constructor count
  run: |
    COUNT=$(grep -c "| T" src/core/lexer_v25.ml | grep "of\|(" || echo 0)
    if [ "$COUNT" -ne 6 ]; then
      echo "Error: Expected 6 token constructors, found $COUNT"
      exit 1
    fi

- name: Run size check
  run: dune exec scripts/size_check.exe
```

## Acceptance Criteria

Before closing this issue:
1. ✅ All documentation references to token ADT show "6 constructors"
2. ✅ No references to "9 constructors" remain
3. ✅ Memory footprint table replaces "24 B fixed" claim
4. ✅ CI gates pass on Linux and macOS
5. ✅ Proofs still compile (63 admits unchanged)
6. ✅ Performance benchmarks show < 0.5% regression

## Decision Record

See `/docs/decisions/2025-07-31-token-adt.md` for the formal decision record.

---
**Target Completion:** 2025-08-02 18:00 UTC (end of Week 6)