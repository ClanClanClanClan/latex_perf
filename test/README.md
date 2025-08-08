# Test Suite Organization

## Directory Structure

```
test/
├── unit/           # Unit tests for individual components
├── integration/    # Integration tests (L0→L1→L2 pipeline)
├── performance/    # Performance benchmarks and tests
├── correctness/    # Correctness verification tests
└── scripts/        # Test runner scripts
```

## Key Test Files

### Performance Tests (`performance/`)
- **Arena Implementation Tests**:
  - `test_arena_flambda2_direct.ml` - Tests with Flambda2 compiler
  - `test_real_arena_implementation.ml` - Real Arena implementation test
  - `test_arena_optimized_packed.ml` - Packed token optimization test

- **L0 Lexer Tests**:
  - `test_l0_performance_verification.ml` - Official L0 performance test
  - `test_l0_actual_benchmark.ml` - Benchmark against corpus
  - `test_l0_standalone.ml` - Standalone lexer test

### Integration Tests (`integration/`)
- `test_pipeline_simple.ml` - Basic L0→L1→L2 pipeline
- `test_full_pipeline.ml` - Complete pipeline with all layers
- `test_l2_with_correct_tokens.ml` - L2 parser with real tokens

### Scripts (`scripts/`)
- `FOOLPROOF_PERFORMANCE_TEST.sh` - **OFFICIAL** performance test (use this!)
- `run_performance_tests.sh` - Run all performance benchmarks

## Running Tests

### Quick Performance Check
```bash
./test/scripts/FOOLPROOF_PERFORMANCE_TEST.sh
```

This will:
1. Check for Flambda2 compiler (REQUIRED)
2. Compile with optimization flags
3. Test on 1.1MB corpus
4. Report PASS/FAIL clearly

### Run All Tests
```bash
make test
```

### Run Specific Test Category
```bash
# Unit tests only
dune runtest test/unit

# Performance tests only
dune runtest test/performance

# Integration tests only
dune runtest test/integration
```

## Performance Targets

### L0 Lexer (CRITICAL)
- **Target**: ≤20ms on 1.1MB file
- **Requires**: OCaml 5.1.1+flambda2 compiler
- **Test with**: `FOOLPROOF_PERFORMANCE_TEST.sh`

### Expected Results
| Component | Target | With Flambda2 | Without Flambda2 |
|-----------|--------|---------------|------------------|
| L0 Lexer | ≤20ms | 17-18ms ✅ | 31.40ms ❌ |

## Writing New Tests

### Performance Test Template
```ocaml
(* test/performance/my_benchmark.ml *)
open Unix

let test_corpus = "corpora/perf/perf_smoke_big.tex"

let benchmark name f =
  let times = ref [] in
  for i = 1 to 10 do
    Gc.minor ();
    let start = gettimeofday () in
    let _ = f () in
    let elapsed = (gettimeofday () -. start) *. 1000.0 in
    times := elapsed :: !times
  done;
  let sorted = List.sort compare !times in
  let median = List.nth sorted 5 in
  Printf.printf "%s: median %.2fms\n" name median;
  median <= 20.0  (* Pass if ≤20ms *)
```

### Integration Test Template
```ocaml
(* test/integration/my_integration_test.ml *)
let test_pipeline () =
  let input = "\\documentclass{article}..." in
  let tokens = L0_lexer.tokenize input in
  let expanded = L1_expander.expand tokens in
  let ast = L2_parser.parse expanded in
  (* Verify results *)
  assert (List.length tokens > 0);
  assert (ast <> Empty)
```

## CI Integration

Tests are run automatically on:
- Every commit to main
- All pull requests
- Nightly performance regression tests

Performance regressions block merge if:
- L0 lexer exceeds 20ms
- Any test fails with Flambda2 compiler

## Troubleshooting

### "Performance test fails"
1. Check you're using Flambda2: `opam switch`
2. Run `FOOLPROOF_PERFORMANCE_TEST.sh` for diagnosis
3. See `SINGLE_SOURCE_OF_TRUTH_PERFORMANCE.md`

### "Can't find test file"
Tests have been reorganized. Check:
- Old location: root directory
- New location: `test/performance/` or `test/integration/`

---

*For performance investigation history, see `docs/archive/performance-investigation-2025-08/`*