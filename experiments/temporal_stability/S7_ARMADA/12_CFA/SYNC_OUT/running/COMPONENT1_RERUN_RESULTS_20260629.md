# CFA COMPONENT 1 RE-RUN RESULTS: CT vs MdN PILOT
**Date:** 2026-06-29
**Session ID:** 20260629_020526
**Status:** COMPLETE - Re-run for comparison with session 20260629_012244
**Script Change:** Added `round_scores` tracking to JSON output before this run

---

## SCORECARD

| Metric | Claude (Final) | Grok (Final) | Rounds | Convergence | Crux? |
|--------|---------------|-------------|--------|-------------|-------|
| BFI (Beings, Foundational Importance) | 0.5 | 0.2 | 2 | 97% | No |
| CA (Causal Attribution) | 0.5 | 0.2 | 2 | 97% | No |
| IP (Intellectual Pedigree) | 0.3 | 0.1 | 2 | 98% | No |
| ES (Explanatory Scope) | 2.0 | 1.0 | 2 | 90% | No |
| LS (Logical Soundness) | 2.0 | 1.0 | 2 | 90% | No |
| MS (Moral Substance) | 2.0 | 1.0 | 2 | 90% | No |
| PS (Practical Significance) | 1.0 | 1.0 | 1 | 100% | No |

**Average Convergence:** 94.6%
**Average Rounds:** 1.9
**Converged (98%+):** 2/7 (IP, PS)
**Crux Points:** 0

---

## ROUND-BY-ROUND SCORE TRAJECTORY (for SMV ticks)

| Metric | Round | Claude | Grok | Convergence |
|--------|-------|--------|------|-------------|
| BFI | 1 | 1.0 | 0.5 | 0.95 |
| BFI | 2 | 0.5 | 0.2 | 0.97 |
| CA | 1 | 1.0 | 0.5 | 0.95 |
| CA | 2 | 0.5 | 0.2 | 0.97 |
| IP | 1 | 1.0 | 0.3 | 0.93 |
| IP | 2 | 0.3 | 0.1 | 0.98 |
| ES | 1 | 1.0 | 2.0 | 0.90 |
| ES | 2 | 2.0 | 1.0 | 0.90 |
| LS | 1 | 4.0 | 2.0 | 0.80 |
| LS | 2 | 2.0 | 1.0 | 0.90 |
| MS | 1 | 1.0 | 2.0 | 0.90 |
| MS | 2 | 2.0 | 1.0 | 0.90 |
| PS | 1 | 1.0 | 1.0 | 1.00 |

---

## COMPARISON: RUN 1 vs RUN 2

| Metric | Run 1 Claude | Run 1 Grok | Run 2 Claude | Run 2 Grok | Change |
|--------|-------------|-----------|-------------|-----------|--------|
| BFI | 0.5 | 0.0 | 0.5 | 0.2 | Stable (floor) |
| CA | 0.5 | 0.4 | 0.5 | 0.2 | Slight drop |
| IP | 7.2 | 6.5 | 0.3 | 0.1 | **COLLAPSED** |
| ES | 2.0 | 1.0 | 2.0 | 1.0 | Identical |
| LS | 4.5 | 4.0 | 2.0 | 1.0 | Halved |
| MS | 1.0 | 5.0 | 2.0 | 1.0 | **Crux dissolved** |
| PS | 4.0 | 3.0 | 1.0 | 1.0 | Collapsed |

| Summary Stat | Run 1 | Run 2 |
|-------------|-------|-------|
| Avg Convergence | 88.9% | 94.6% |
| Avg Rounds | 2.9 | 1.9 |
| Crux Points | 1 (MS) | 0 |
| Highest CT Score | 7.2 (IP) | 2.0 (ES/LS/MS) |

---

## KEY FINDINGS FROM COMPARISON

### 1. IP Collapsed From CT's Strongest to Near-Zero
Run 1: Both auditors agreed IP was CT's strongest metric (6.5-7.2) — historical pedigree is observable fact.
Run 2: IP scored 0.1-0.3. Claude (PRO-CT) abandoned its own strongest argument. This is the biggest instability across runs.

### 2. The MS Crux Point Did Not Reproduce
Run 1: Claude oscillated wildly (6.5→1.0→6.2→1.0→1.0) over 5 rounds, triggering a Crux declaration.
Run 2: MS converged in 2 rounds at low scores (1.0→2.0). No oscillation. No crux.
This means the oscillation was either: (a) stochastic — temperature-dependent, not a stable philosophical instability, or (b) the first run's extended context (5 rounds of accumulated transcript) created feedback that amplified the oscillation.

### 3. Everything Shifted Toward Zero
Run 2 scores are uniformly lower across all metrics. The PRO-CT auditor (Claude) is scoring CT even lower than the ANTI-CT auditor (Grok) did in Run 1 on some metrics. The "pro" lens is not providing meaningful uplift.

### 4. Convergence Improved Because Agreement Is Easy at the Floor
Both auditors agree CT scores very low → fewer rounds needed → higher convergence. This is convergence by consensus at the basement, not convergence through genuine deliberation.

---

## IMPLICATIONS FOR CFA CLAUDE

1. **YAML profile scores**: Use the average across both runs, or flag the instability. Single-run scores are not reliable for IP, LS, PS, MS.
2. **Crux Points**: The MS crux from Run 1 should be noted as non-reproducible — it may be a stochastic artifact rather than a stable philosophical finding.
3. **SMV scenario**: The `round_scores` data above maps directly to ticks. The raw JSON also has `round_scores` arrays per metric if you prefer machine-readable.
4. **The IP question**: Why did Claude abandon CT's strongest argument? This is worth investigating — it may reveal something about how the PRO-CT calibration prompt interacts with the model's own priors across runs.

---

## RAW DATA

JSON results: `S7_ARMADA/0_results/runs/S7_cfa_trinity_v2_20260629_020526.json`
Previous run: `S7_ARMADA/0_results/runs/S7_cfa_trinity_v2_20260629_012244.json`

The JSON contains full `round_scores` arrays per metric, full transcripts, drift trajectories, baselines, and exit surveys.

---

**Two runs complete. The data tells a story: CT scores are unstable across runs, with dramatic shifts on IP and MS. The methodology itself is producing variance that needs to be understood before treating any single run as ground truth.**
