Below is a fully revised Appendix R — Comprehensive Risk Register that folds in every change I recommended:
	•	impact‑scale tightened (H ≥ 4 weeks / major quality or compliance hit)
	•	new Residual score column
	•	added “Critical (Y/N)” flag for non‑negotiable compliance or existential items
	•	three new risks (backup & restore, key‑person outage, regulatory drift)
	•	“Next review” column (set to the first business Monday of each month)
	•	risk‑appetite statement up front

Copy/paste the block as‑is into governance/risk-register.md; diff‑friendly markdown is preserved.

⸻


# Appendix R — Comprehensive Risk Register  
*Project — LaTeX Perfectionist v25.1*  
*Revision : 2025‑07‑31 UTC*  
*Owner    : solo‑dev ‹your‑handle›*  

## Risk‑Appetite Statement  
Any risk whose **Residual** score ≥ 4 **or** that is flagged **Critical = Y** must have (i) at least one active Prevent or Detect control, and (ii) be re‑evaluated before the next production release.

---

> **Legend**  
> **P · Probability** L ≤ 20 % · M 21–60 % · H > 60 %  
> **I · Impact** L < 1 week slip · M 1–3 weeks · H ≥ 4 weeks / severe quality · compliance · reputational hit  
> **Score = P × I** (L = 1, M = 2, H = 3) → 1–9  
> **Residual** = expected score *after* planned controls are in place  
> **Critical (C)** = Y if the risk is non‑negotiable (security, legal, existential)  

| # | Area | Risk Description | P | I | Score | Residual | Mitigation / Contingency (Prevent / Detect / Respond) | Owner | Trigger Metric | C | Next Review |
|---|------|-----------------|---|---|-------|----------|-------------------------------------------------------|--------|----------------|---|-------------|
| **T‑1** | Tech | Pattern‑mining produces over‑general rules → FP ↑ | M | H | 6 | **3** | **P** Precision gate ≥ 95 %<br>**D** Weekly 100‑sample canary<br>**R** Auto‑rollback if FP > 0.3 % two CI runs | solo‑dev | FP > 0.3 % two nights | N | 2025‑08‑04 |
| **T‑2** | Tech | Coq 8.20 upgrade breaks 400 + proofs | M | H | 6 | 3 | P Pin container; bisect script<br>D CI proof counts<br>R Port on branch then merge | solo‑dev | CI proofs failing > 5 | N | 2025‑08‑04 |
| **T‑3** | Tech | Incremental parser worst‑case O(n²) on corner cases | M | M | 4 | 2 | P Grammar LL(2) audit<br>D Fuzz parser perf gate<br>R Emit warning & abort batch | solo‑dev | p99 parse > 8 ms | N | 2025‑08‑04 |
| **T‑4** | Tech | Unicode RTL segmentation bug | M | M | 4 | 2 | P Integrate ICU test‑suite<br>D Arabic/Hebrew sample docs in CI | solo‑dev | RTL tests red | N | 2025‑08‑04 |
| **T‑5** | Tech | SIMD path mis‑detects CPU features on exotic ARM | L | M | 2 | 1 | P Runtime CPUID guard<br>R Scalar fallback | solo‑dev | Crash log “illegal instr” | N | 2025‑08‑04 |
| **T‑6** | Tech | GPU cold‑start prototype starves CPU threads | L | M | 2 | 1 | P Opt‑in flag<br>D Latency watchdog >15 % | solo‑dev | Latency regression CI | N | 2025‑08‑04 |
| **S‑1** | Sec | FFI library (Hyperscan) gains a CVE | M | M | 4 | 2 | P Dependabot automatic PR<br>D CVE matcher in CI<br>R Hot‑patch & release | solo‑dev | New CVE for lib‐ver | **Y** | 2025‑08‑04 |
| **S‑2** | Sec | Supply‑chain attack via `opam pin` | L | H | 3 | 2 | P Pin SHAs & mirror registry<br>D GPG signature verify<br>R Block release, rotate key | solo‑dev | Hash mismatch CI | **Y** | 2025‑08‑04 |
| **L‑1** | Legal | Upstream licence revoked / DMCA | L | H | 3 | 2 | P Takedown pipeline<br>R Replace with alt docset | solo‑dev | DMCA notice | **Y** | 2025‑08‑04 |
| **L‑2** | Legal | GDPR: accidental PII in corpus | M | M | 4 | 2 | P PII scrub script<br>D Encrypted audit log<br>R Purge + notify | solo‑dev | pii_scan > 0 hits | **Y** | 2025‑08‑04 |
| **C‑1** | Compliance | Regulatory drift (EU AI Act re‑classification) | L | M | 2 | 2 | D Subscribe to OSS compliance feed<br>R Gap analysis sprint | solo‑dev | Reg alert affecting scope | **Y** | 2025‑08‑04 |
| **Q‑1** | Qual | False‑positive spike after ML batch | M | H | 6 | 3 | D Canary 5 % batch<br>R Auto‑rollback FP > 0.2 % | solo‑dev | Canary alerts | N | 2025‑08‑04 |
| **Q‑2** | Qual | Proof debt resurfaces (Admitted added) | M | M | 4 | 2 | D Gate: no new admits<br>P Weekly debt chart | solo‑dev | Admits > 0 | N | 2025‑08‑04 |
| **Q‑3** | Qual | Validator fix‑ordering overlap | L | M | 2 | 1 | P `no_overlapping_fixes` theorem<br>D Integration test | solo‑dev | Test failure | N | 2025‑08‑04 |
| **O‑1** | Ops | Proof‑farm outage (k8s cluster) | M | M | 4 | 2 | P Fail‑over scripts/ci_switch.sh<br>D Heartbeat job<br>R Switch to GH‑hosted | solo‑dev | Job timeout > 30 m | N | 2025‑08‑04 |
| **O‑2** | Ops | Disk‑space exhaustion from snapshots | M | L | 2 | 1 | D Alert at 80 % disk<br>R LRU purge > 1 GiB | solo‑dev | `df` < 15 % free | N | 2025‑08‑04 |
| **O‑3** | Ops | Proof‑cache mismatch ⇒ recompile storm | L | M | 2 | 1 | P Cache key includes tactic hash<br>D Smoke‑test compile time | solo‑dev | CI runtime > 20 m | N | 2025‑08‑04 |
| **O‑4** | Ops | AWS S3 bucket permission drift | L | M | 2 | 1 | D Terraform drift‑detect<br>R Weekly audit | solo‑dev | `terraform plan` ≠ empty | N | 2025‑08‑04 |
| **O‑5** | Ops | Backup & restore failure → data loss | L | H | 3 | 2 | P Versioned backups<br>D Monthly restore drill<br>R Off‑line snapshot | solo‑dev | Restore test fails | **Y** | 2025‑08‑04 |
| **B‑1** | Biz | Solo‑developer burnout (> 4 week hiatus) | M | H | 6 | 3 | P 4‑week buffer in timeline<br>D Velocity KPI < 70 % for 3 w<br>R Sabbatical plan | solo‑dev | Velocity KPI | N | 2025‑08‑04 |
| **B‑2** | Biz | Funding gap for cloud compute | L | M | 2 | 1 | P Pre‑pay credits<br>D Alert AWS credit < $500<br>R Local fallback farm | solo‑dev | AWS credit < $500 | N | 2025‑08‑04 |
| **B‑3** | Biz | Key‑person unavailable ≥ 1 week (illness) | L | H | 3 | 2 | P Bus‑factor playbook<br>D Contact protocol notice<br>R Freeze release, call backup maintainer | solo‑dev | OOO > 5 d | N | 2025‑08‑04 |
| **R‑1** | Res | Pattern‑mining research stagnates | L | H | 3 | 2 | P 10 % manual quota<br>D Throughput KPI < 10 / wk | solo‑dev | Validator throughput | N | 2025‑08‑04 |
| **E‑1** | Eth | Bias in NLP model penalises non‑EN dialects | M | M | 4 | 2 | P Lang‑balanced eval set<br>D Fairness metrics<br>R Retrain on under‑represented dialects | solo‑dev | Δ precision > 5 pt | **Y** | 2025‑08‑04 |
| **P‑1** | Perf | Lexer target unattainable (2ms impossible) | L | M | 2 | 1 | **P** ✅ RESOLVED: L0 target 20ms per V3 spec<br>**D** Nightly perf regression vs baseline<br>**R** Fallback to scalar if SIMD fails | solo‑dev | ✅ CLOSED: realistic target agreed | N | 2025‑08‑04 |
| **P‑2** | Perf | Cache‑thrash on > M documents | M | M | 4 | 2 | P Sharded elder tries<br>D Memory cap toggle | solo‑dev | RSS > 300 MiB | N | 2025‑08‑04 |
| **P‑3** | Perf | L4 NLP exceeds 12 ms budget on CJK | M | M | 4 | 2 | P Fast‑seg Jieba, rayon<br>D Profiling alert | solo‑dev | Profiling alert | N | 2025‑08‑04 |
| **P‑4** | Perf | Domain parallelism doesn't scale linearly | M | M | 4 | 2 | **P** NUMA-aware pinning<br>**D** Scaling factor < 0.7 per core<br>**R** Cap domains at 4 | solo‑dev | Scaling factor alert | N | 2025‑08‑04 |
| **P‑5** | Perf | Bigarray optimization causes GC pressure | L | M | 2 | 1 | **P** Pre-allocated pools<br>**D** GC minor count spike<br>**R** Revert to functional approach | solo‑dev | GC metrics alert | N | 2025‑08‑04 || **X‑1** | Ext | New TeX engine primitives in LuaTeX 2.0 | L | M | 2 | 1 | P Engine detection<br>D Regression tests | solo‑dev | Regression fail | N | 2025‑08‑04 |
| **X‑2** | Ext | File‑format changes in spaCy v5 | M | L | 2 | 1 | P Vendor wheel; pin v4.x<br>R Fork & patch | solo‑dev | Import error | N | 2025‑08‑04 |
| **I‑1** | Inf | GitHub Actions CI‑minute budget exceeded | M | L | 2 | 1 | P Self‑hosted runner<br>D Minutes KPI<br>R Nightly heavy jobs | solo‑dev | CI minutes > 90 % | N | 2025‑08‑04 |
| **D‑1** | Doc | Documentation backlog (tutorial stale) | M | L | 2 | 1 | P Docs sprint per milestone<br>D Docs coverage < 85 % | solo‑dev | Docs coverage | N | 2025‑08‑04 |

*Total rows : 31 — conforms to governance §11.*

---

### How to keep this living document healthy

1. **CI badge** — add a small 🔴/🟢 badge that turns red if any Residual ≥ 4.  
2. **Monthly calendar reminder** — already reflected in “Next review” column.  
3. **Heat‑map** — generate automatically (example script in `/scripts/risk_heatmap.py`).  
4. Commit all edits via PR so the register history remains auditable.


⸻