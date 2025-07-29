# Appendix R — Comprehensive Risk Register  
*Project — LaTeX Perfectionist v25*  
*Revision : 2025-07-27 UTC*  
*Owner    : solo-dev ‹your-handle›*  

> **Legend**  
>  P · Probability — L = Low (≤20 %), M = Medium (21–60 %), H = High (>60 %)  
>  I · Impact      — L = <1 week slip · M = release slip ≤2 months · H = ≥2 months / severe quality hit  
>  Score = P×I (L=1, M=2, H=3) → 1–9  

| # | Area | Risk Description | P | I | Score | Mitigation / Contingency | Owner | Trigger Metric |
|---|------|-----------------|---|---|-------|---------------------------|--------|-----------------|
| T-1 | Tech | Pattern-mining produces over-general rules ⇒ FP ↑ | M | H | 6 | Precision gate ≥95 %; manual review of first 5 % of output | solo-dev | FP rate > 0.3 % nightly CI |
| T-2 | Tech | Coq 8.20 upgrade breaks 400+ proofs              | M | H | 6 | Pin image; bisect script; port on branch | solo-dev | CI proofs failing > 5 |
| T-3 | Tech | Incremental parser fallback to O(n²) on corner cases | M | M | 4 | Grammar LL(2) audit; fuzz-parser; perf gate | solo-dev | p99 parse > 8 ms |
| T-4 | Tech | Unicode RTL segmentation bug                    | M | M | 4 | ICU test-suite; Arabic/Hebrew sample docs | solo-dev | RTL tests red |
| T-5 | Tech | SIMD path mis-detects CPU features on exotic ARM chips | L | M | 2 | Runtime CPUID guard, scalar fallback | solo-dev | Crash log “illegal instr” |
| T-6 | Tech | GPU cold-start prototype starves CPU threads    | L | M | 2 | Opt-in flag; watchdog abort if latency > 15 % | solo-dev | Latency regression CI |
| S-1 | Sec  | FFI library (Hyperscan) CVE                     | M | M | 4 | Dependabot; run under seccomp; auto-patch | solo-dev | New CVE matching lib ver |
| S-2 | Sec  | Supply-chain attack via Coq opam pin            | L | H | 3 | Pinned SHAs; reproducible nix lock-file | solo-dev | Hash mismatch on CI |
| L-1 | Legal| Upstream licence revoked / DMCA                 | L | H | 3 | Takedown pipeline; replace with alt doc | solo-dev | DMCA notice |
| L-2 | Legal| GDPR: accidental PII in corpus                  | M | M | 4 | PII scrub script; encrypted audit log | solo-dev | pii_scan >0 hits |
| Q-1 | Qual | False-positive spike after ML batch             | M | H | 6 | Canary 5 %; auto-rollback threshold FP >0.2 % | solo-dev | Canary alerts |
| Q-2 | Qual | Proof debt resurfaces (Admitted added)          | M | M | 4 | CI gate: no new admits; weekly debt chart | solo-dev | Admits count > 0 |
| Q-3 | Qual | Validator overlaps conflict (fix-ordering)     | L | M | 2 | no_overlapping_fixes theorem; integration test | solo-dev | Test failure |
| O-1 | Ops  | Proof farm outage (k8s cluster)                 | M | M | 4 | Fail-over to GH-hosted; scripts/ci_switch.sh | solo-dev | Job timeout >30 m |
| O-2 | Ops  | Disk-space exhaustion from snapshots            | M | L | 2 | LRU purge >1 GB; alert at 80 % disk | solo-dev | df <15 % free |
| O-3 | Ops  | Proof cache mismatch ⇒ recompile storm          | L | M | 2 | Cache key includes tactic hash; smoke-test | solo-dev | CI runtime >20 m |
| O-4 | Ops  | AWS S3 bucket permission drift                  | L | M | 2 | Terraform drift-detect; weekly audit | solo-dev | tf plan ≠ empty |
| B-1 | Biz  | Solo-developer burnout (>4 weeks hiatus)        | M | H | 6 | 4-week buffer in timeline; rotate tasks; sabbatical plan | solo-dev | Velocity <70 % for 3 w |
| B-2 | Biz  | Funding gap for cloud compute                  | L | M | 2 | Pre-pay credits; local fallback farm | solo-dev | AWS credit < $500 |
| R-1 | Res  | Pattern-mining research stagnates              | L | H | 3 | Adopt simpler heuristics; 10 % manual quota | solo-dev | Validator throughput <10/wk |
| E-1 | Eth  | Bias in NLP model penalises non-EN dialects     | M | M | 4 | Lang-balanced eval set; fairness metrics | solo-dev | Δ precision dialects >5 pt |
| P-1 | Perf | AVX-512 path slower on some Xeons               | L | M | 2 | Runtime perf test, auto-switch to AVX2 | solo-dev | Perf harness regression |
| P-2 | Perf | Cache-thrash on >M documents                    | M | M | 4 | Sharded elder tries; memory cap toggle | solo-dev | RSS >300 MB |
| P-3 | Perf | L4 NLP exceeds 12 ms budget on CJK              | M | M | 4 | Jieba fast-seg; rayon parallel; cache | solo-dev | Profiling alert |
| X-1 | Ext  | New TeX engine primitives in LuaTeX 2.0         | L | M | 2 | Engine detection; fallback warnings | solo-dev | Regression test fail |
| X-2 | Ext  | File format changes in spaCy v5                 | M | L | 2 | Vendor wheel; pin exact v4.x | solo-dev | Import error |
| I-1 | Inf  | CI minute budget exceeded on GitHub             | M | L | 2 | Self-hosted runner; nightly heavy jobs | solo-dev | GH actions minutes >90 % |
| D-1 | Doc  | Documentation backlog (tutorial stale)         | M | L | 2 | Docs sprint every milestone; lint | solo-dev | Docs coverage <85 % |

*Total rows : 28 — matching governance §11.*
