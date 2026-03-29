# 🚀 NEXT STEPS - Week 2-5 Development Plan

## 🎯 **CURRENT STATUS: Week 8 In-Flight**

✅ **Build Baseline**: `dune build` green for `latex-parse/`
✅ **Proof Admits**: 0 (`proofs/CoreProofs.v`, `proofs/Catcode.v`, `proofs/Arena_safe.v`)
✅ **Performance Numbers**: p95 ≈ 2.73 ms (200 k), ≈ 2.96 ms (1 M); edit-window p95 ≈ 0.017 ms (4 KB)
✅ **Catcode**: runtime classifier aligned + self-test in benches
✅ **REST**: JSON schema, /ready + bonded /health, positive/negative smoke in CI; L0_DEBUG_L1 expander summary documented
✅ **Rust Proxy**: short smoke in CI (3 requests), verify_r1 evidence workflow available
✅ **Formatting Gate**: `dune fmt --check` in CI
🟨 **SIMD xxHash**: scalar bench + optional gate present; SIMD lane pending
✅ **Validators**: Pilot rules live; Unicode heuristics are paragraph‑aware; L1 post‑expansion rules (MOD‑001/2/3/4, EXP‑001) added with goldens and CI smokes; message alignment enforced for Unicode/L1/pilot

---

## 📋 **WEEK 2-3: Runtime Reconciliation & Bench Bring-up**

### **Objective**: Reconcile the archived L0 prototypes with the active SIMD runtime and regenerate baseline measurements.

**Deliverables**:
- Shared arena/token SoA between `core/l0_lexer` and `latex-parse`
- Bench + service builds runnable after temporarily restoring `core/**/dune`
- ✅ Fresh perf_smoke benchmark report committed to `core/l0_lexer/current_baseline_performance.json`

**Exit Criteria**:
- Document a safe workflow for restoring `dune.disabled` files during local experiments
- `ab_microbench` run recorded (target: ≥100k iters, p95 < 20 ms Tier A) — done via 200k/500k/1M iters (see `core/l0_lexer/current_baseline_performance.json`)
- Updated README / docs reference the new measurements

---

## 📋 **WEEK 4: Catcode Module + Proof Stubs**

### **Objective**: Restore the catcode classifier and accompanying Coq proof skeleton on top of the unified runtime.

**Deliverables (status)**:
- `latex-parse/src/catcode.ml` aligned with `Data.Types.Catcode` ✅
- Catcode self-test bench ✅
- Proofs remain zero-admit; additional lemmas can be staged 🟨

**Exit Criteria**:
- Coq build extends beyond CoreProofs while keeping admits = 0
- Unit tests / benches confirm catcode lookup correctness

---

## 📋 **WEEK 5: Performance α Gate (re-run)** 🎯

### **Objective**: With runtime + catcodes reinstated, rerun the perf_smoke gate and publish results.

**Hard Requirements**:
```bash
# Performance Gate (rerun)
- p95 < 20 ms (Tier A) on corpora/perf/perf_smoke_big.tex (1.1 MB)
- 4 KB edit-window p95 ≤ 1.2 ms (`scripts/edit_window_gate.sh`)
- Bench CSVs uploaded via scripts/perf_gate.sh / edit_window_gate.sh
- README + docs updated with the new measurements
```

**Test Commands**:
```bash
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/ab_microbench.exe \
  corpora/perf/perf_smoke_big.tex 10000 --csv /tmp/ab_microbench.csv
bash scripts/perf_gate.sh corpora/perf/perf_smoke_big.tex 100
OPAMSWITCH=l0-testing opam exec -- \
  ./_build/default/latex-parse/bench/edit_window_bench.exe \
  corpora/perf/edit_window_4kb.tex 5000 --csv /tmp/edit_window_bench.csv
bash scripts/edit_window_gate.sh corpora/perf/edit_window_4kb.tex 2000
```

**CI Integration**:
- Performance gates present; add nightly perf job once infra is stable 🟨
- Rust proxy smoke ✅; verify_r1 evidence workflow ✅

---

## 📋 **WEEKS 6-10: Q1 Completion**

### **Week 6-8: Incremental Lexer Proof**
- **Deliverable**: `LexerSmallstep.v` foundation (done), upgrade to `LexerIncremental.v` with 0 admits
- **Focus**: Prove `lexer_locality` and single-step determinism for a faithful L0 relation
- **Target**: Incremental re-lexing for 16KB windows

### **Week 9: SIMD xxHash**
- **Deliverable**: AVX2/NEON xxHash implementation
- **Target**: ≥ 20 GB/s throughput
- **Platforms**: x86_64 (AVX2) and ARM64 (NEON)

### **Week 10: Proof β Gate** 🎯
- **Hard Requirement**: Global admits = 0 and axioms = 0 (enforced)
- **CI**: `proof-gate.yml` enforces zero admits/axioms (Coq 8.18.0)

---

## 🔧 **TECHNICAL IMPLEMENTATION DETAILS**

### **Catcode Classification (Week 2-3)**
```ocaml
type catcode =
  | Escape      (* \ *)
  | BeginGroup  (* { *)
  | EndGroup    (* } *)
  | MathShift   (* $ *)
  | AlignTab    (* & *)
  | EndOfLine   (* \n *)
  | MacroParam  (* # *)
  | Superscript (* ^ *)
  | Subscript   (* _ *)
  | Ignored     (* null *)
  | Space       (* space/tab *)
  | Letter      (* a-z, A-Z *)
  | Other       (* default *)
  | Active      (* ~ *)
  | Comment     (* % *)
  | Invalid     (* delete char *)
```

### **Performance Optimization Strategy**
1. **Week 2-3**: Reconcile runtime + capture fresh baseline numbers (<40 ms placeholder)
2. **Week 4**: Restore catcode classifier + proofs while keeping latency budget intact
3. **Week 5**: Re-run perf α gate (<20 ms Tier A target) and re-enable CI guardrails
4. **Week 9**: Resume SIMD-specific optimizations once scalar lane is stable

---

## 🎯 **SUCCESS METRICS**

### Q1 End State (Week 13)
| Metric | Target | Current | Path |
|--------|--------|---------|------|
| Performance p95 | <20ms (Tier A) | ✅ (p95 ≈2.96 ms @1M) | Week 5 gate |
| Proof Admits | ≤10 | 0 | Maintain |
| Validators | 80 | specs-only | Rebuild L0 ↔︎ core |
| SIMD Prototype | Started | Pending | Resume post gate |

---

## 🚀 **LONG-TERM TRAJECTORY**

### Q2 (Weeks 14-26)
- L1 macro expander implementation
- Fuel proofs for termination
- Validator DSL v1
- **Gate**: L0-L1 formal checkpoint

### Q3 (Weeks 27-39)
- Generic proof tactics
- ML span extractor training
- First 80 validators generated
- **Target**: Scalar ≤20ms achieved

### Q4 (Weeks 40-52)
- SIMD tokenizer implementation
- PEG parser code generation
- L2 parser delivery
- **Gate**: p95 < 1.2ms end-to-end

---

## 🎯 **DEFINITION OF DONE - Week 5**

**Performance α Gate Requirements**:
1. ✅ p95 ≤ 20ms (Tier A) on 1.1MB file
2. ✅ Edit-window pipeline wired
3. ✅ SIMD bench infrastructure ready
4. ✅ CI gates active and enforced
5. ✅ Zero regression from Week 1 baseline

---

**BOTTOM LINE**: Week 1 complete with refreshed performance baseline (p95 < 3 ms across 200 k–1 M iter). Focus now shifts to Week 2-3 catcode implementation while maintaining the gate.
