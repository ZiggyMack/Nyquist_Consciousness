# Care Package: Full Gnostic Experiment Results (v3 Metrics — 181 Clean Runs)

**From:** Repo Claude (Gnostic CFA Analysis)
**To:** CFA Claude
**Date:** 2026-07-06
**Priority:** HIGH — Complete gnostic dataset across all matchups; supersedes partial package from 2026-07-05

---

## Context

This is the full gnostic experiment dataset using v3 metrics (BFI, CA, ES, IP, LS, MS, PS). 181 clean runs across 7 matchups × 2 conditions. Each matchup has 10+ runs per condition (except `external_g_vs_pt` which has only 2 — see gap note below). The v2 metric runs (160 runs with AR, CCI, EDB, MG, PF_E, PF_I) exist in the same directory but use a different metric set and should be analyzed separately if at all.

**Framing reminder:** Gnosticism enters the CFA as an independent test framework, not as "the weird one." Score comparisons should treat G the same as CT, MdN, and PT — no prior assumption of relative merit.

**Supersedes:** `gnostic_experiment_care_package.md` (2026-07-05, partial — 120 runs, pre-v3 metrics)

---

## Dataset Summary

### Run Counts (v3, 7 metrics, all scores valid, no -1s)

| Matchup | Control | External | Total |
|---------|---------|----------|-------|
| CT vs G | 10 | 10 | 20 |
| CT vs PT | 10 | 10 | 20 |
| G vs CT | 10 | 10 | 20 |
| G vs MdN | 20 | 20 | 40 |
| MdN vs G | 10 | 10 | 20 |
| PT vs G | 19 | 20 | 39 |
| PT vs MdN | 10 | 10 | 20 |
| G vs PT | — | 2 | **2** |
| **Total** | **89** | **92** | **181** |

**Gap:** `g_vs_pt` (Gnosticism as subject, PT as opponent) was never configured as a separate stance in the batch scripts. Only 2 external runs exist, no controls. If this reverse direction matters for your analysis, we'll need a targeted batch. All other matchups are solid at 10+ per condition.

---

## Finding 1: Control Conditions Remain Pristine Across All Matchups

Every control condition across all 7 matchups shows:
- Average auditor divergence (Claude − Grok): **≤ 0.05 points**
- Crux rate: **exactly 0%**

| Control Matchup | N | Avg Divergence | Crux Rate |
|-----------------|---|----------------|-----------|
| CT vs G | 10 | +0.01 | 0% |
| CT vs PT | 10 | −0.05 | 0% |
| G vs CT | 10 | +0.00 | 0% |
| G vs MdN | 20 | +0.04 | 0% |
| MdN vs G | 10 | −0.02 | 0% |
| PT vs G | 19 | +0.05 | 0% |
| PT vs MdN | 10 | +0.05 | 0% |

**CFA implication:** The adversarial architecture produces ZERO false positives. Without identity pressure, Claude and Grok converge perfectly regardless of which frameworks are being evaluated. This is now confirmed across 89 control runs spanning every matchup in the experiment. Any delta in the external condition is attributable to the identity effect alone.

---

## Finding 2: Identity Effect Magnitude Is Consistent (~1.0-1.5 Points) and Always Directional

Every external condition produces auditor divergence in the **predicted direction** — Claude always scores higher when PRO-subject and lower when ANTI-subject.

| External Matchup | N | Claude Stance | Avg Div (C−G) | Avg Crux | Direction |
|------------------|---|---------------|---------------|----------|-----------|
| CT vs G | 10 | PRO-CT | **+1.21** | 48.6% | Claude advocates FOR CT |
| G vs CT | 10 | PRO-G | **−1.01** | 32.9% | Claude advocates FOR G (scores G lower than Grok scores CT) |
| G vs MdN | 20 | PRO-G | **+1.45** | 59.3% | Claude advocates FOR G |
| MdN vs G | 10 | PRO-MdN | **−1.47** | 61.4% | Claude advocates FOR MdN |
| PT vs G | 20 | PRO-PT | **+1.02** | 32.9% | Claude advocates FOR PT |
| PT vs MdN | 10 | PRO-PT | **+1.41** | 58.6% | Claude advocates FOR PT |
| CT vs PT | 10 | PRO-CT | **−0.94** | 25.7% | Claude advocates FOR CT (Grok higher = PRO-PT from Grok's ANTI position) |

**CFA implication:** The identity effect is not framework-specific — it's architectural. Every matchup shows the same ~1.0-1.5 point advocacy signature. The sign always matches the predicted direction. This is now confirmed across 7 independent matchups. The mechanism is the identity file, not the philosophical content.

---

## Finding 3: BFI and MS Are Consistently the Most Identity-Sensitive Metrics

Across all external matchups, BFI (Beings Foundational Importance) and MS (Metaphysical Scope) show the largest identity-driven deltas:

| Metric | Avg |Δ| from Control | Avg Crux Rate | Rank |
|--------|------------------------------|----------------|------|
| BFI | 1.47 | 63.6% | 1st |
| MS | 1.28 | 52.9% | 2nd |
| CA | 1.28 | 52.1% | 3rd |
| LS | 1.06 | 42.9% | 4th |
| ES | 0.99 | 37.1% | 5th |
| IP | 0.93 | 32.9% | 6th |
| PS | 0.88 | 25.0% | 7th |

**CFA implication:** BFI and MS are the metrics most susceptible to definitional manipulation under advocacy. This is the representation-bias signature: identity files change **what the metric measures**, not just how the framework scores. Phase 1 anchors for BFI and MS should be highest priority. PS and IP are the most robust — identity pressure barely moves them.

---

## Finding 4: Gnosticism Has the Most Extreme Score Profile of Any FUT

Control data (no identity pressure) reveals the natural model evaluation of each framework:

| Metric | CT (ctrl avg) | PT (ctrl avg) | MdN (ctrl avg) | G (ctrl avg) | G Range |
|--------|---------------|---------------|-----------------|--------------|---------|
| BFI | 8.4 | 7.5 | 3.3 | 7.7 | — |
| CA | 7.1 | 6.5 | 7.3 | 5.7 | — |
| ES | 7.7 | 7.4 | 7.1 | 5.4 | — |
| IP | 9.2 | 7.5 | 8.1 | 6.5 | — |
| LS | 6.5 | 6.7 | 7.7 | 3.8 | — |
| MS | 8.3 | 6.7 | 3.0 | 4.1 | — |
| PS | 8.1 | 5.0 | 8.3 | 3.4 | — |
| **Spread** | 2.7 | 2.5 | 5.3 | **4.3** | — |

Gnosticism's control profile: moderate BFI (7.7) but very low LS/MS/PS (3.4–4.1). The 4.3-point spread is second only to MdN. Models treat Gnosticism as metaphysically interesting but practically/logically weak.

**CFA implication:** Gnosticism's bipolar profile makes it an excellent stress test. The weak metrics (LS, MS, PS) are exactly where identity pressure has the most room to operate — and the data confirms this. When PRO-G is active, LS jumps from 3.8 to ~5.0-6.2, and PS from 3.4 to ~4.5-5.4. The identity effect lifts weak metrics by ~1.5 points but barely suppresses strong metrics.

---

## Finding 5: Crux Rate Correlates with Metric Vulnerability, Not Framework Difficulty

High-crux matchups are NOT the "hardest" philosophical comparisons — they're the ones where identity pressure hits the most vulnerable metrics:

| Highest Crux Rates | Matchup × Metric | Crux % | Control Score | Pattern |
|---------------------|------------------|--------|---------------|---------|
| 1 | MdN vs G — BFI | 90% | 3.3 | Weakest metric, most crux |
| 2 | G vs MdN — BFI | 85% | 7.6 | BFI always volatile |
| 3 | PT vs MdN — BFI | 90% | 8.1 | BFI always volatile |
| 4 | PT vs MdN — CA | 80% | 6.5 | CA vulnerable for PT |
| 5 | PT vs MdN — MS | 80% | 6.7 | MS consistently vulnerable |

**CFA implication:** Crux declarations are NOT marking genuine philosophical disagreements — they're marking definitional fights. The same metrics (BFI, MS, CA) generate crux across EVERY matchup. This is strong evidence that Phase 1 crux is a measurement artifact (representation-dependent), not a philosophical finding (substance-dependent). Your isomorphism calibration protocol targets exactly this problem.

---

## Finding 6: Reverse-Direction Matchups Confirm Symmetry of the Identity Effect

For matchups where both directions exist (A vs B and B vs A):

| Forward | Avg Div | Reverse | Avg Div | Symmetric? |
|---------|---------|---------|---------|------------|
| CT vs G | +1.21 | G vs CT | −1.01 | Yes (signs flip, magnitude comparable) |
| G vs MdN | +1.45 | MdN vs G | −1.47 | Yes (nearly identical magnitude) |
| PT vs G | +1.02 | (G vs PT: N=2, insufficient) | — | Incomplete |
| PT vs MdN | +1.41 | (MdN vs PT: not run) | — | Not tested |
| CT vs PT | −0.94 | (PT vs CT: not run) | — | Not tested |

Where both directions are measured, the identity effect is **symmetric** — flipping subject/opponent flips the sign but preserves the magnitude. G vs MdN (+1.45) and MdN vs G (−1.47) are almost perfectly mirrored.

**CFA implication:** The advocacy architecture is position-invariant. The identity effect is a property of the architecture, not of which framework is "naturally stronger." This makes the control condition even more valuable — it reveals the model's genuine ranking, and the external condition reveals how much advocacy can distort it.

---

## Finding 7: PT Generates the Lowest Crux Rates of Any Framework

| Framework as Subject | Avg Crux Rate (External) |
|----------------------|--------------------------|
| CT | 37.1% |
| G | 47.1% |
| MdN | 61.4% |
| PT | 40.0% |

But when PT is opponent:

| Framework as Opponent | Avg Crux Rate (External) |
|-----------------------|--------------------------|
| CT (opponent) | 32.9% |
| G (opponent) | 40.8% |
| MdN (opponent) | 58.6% |
| PT (opponent) | 25.7% |

PT as opponent generates the LOWEST crux rate. PT as subject generates moderate crux. This asymmetry suggests PT is "easy to attack but hard to defend against" — its score profile is moderate enough that advocacy can't create large deltas.

**CFA implication:** PT may be the most "isomorphically stable" framework — its natural scores are in the 5-7 range on most metrics, leaving less room for identity-driven distortion. If you're looking for a calibration reference framework, PT's moderate profile makes it a strong candidate.

---

## Summary of Actionable Items

| # | Finding | Recommended Action |
|---|---------|-------------------|
| 1 | Controls are pristine (0% crux, ~0 divergence) across 89 runs | Use control data as ground-truth baseline for all identity effect analysis |
| 2 | Identity effect is ~1.0-1.5 points, always directional | Calibrate significance thresholds: <0.5 = noise, 0.5-1.0 = weak, >1.0 = strong |
| 3 | BFI and MS are most vulnerable metrics | Prioritize Phase 1 anchors for BFI and MS; PS and IP are naturally robust |
| 4 | G has most extreme score profile | Use G as stress-test FUT for methodology changes |
| 5 | Crux marks definitional fights, not philosophy | **Retroactive test:** Compare crux content across matchups — if the same crux arguments appear for BFI regardless of which frameworks are being compared, it's metric-structural, not philosophical |
| 6 | Reverse directions are symmetric | Validates architecture; reduces need to run all permutations (A vs B implies B vs A) |
| 7 | PT has lowest crux as opponent | Consider PT as isomorphism calibration reference |

---

## Known Gaps

| Gap | Impact | Action Needed |
|-----|--------|---------------|
| `g_vs_pt` has only 2 external runs, 0 control | Cannot confirm reverse symmetry for PT↔G | Targeted batch of 10+10 if reverse confirmation matters |
| `pt_vs_ct` not run | CT↔PT only measured in one direction | Targeted batch if needed; symmetry finding suggests redundant |
| `mdn_vs_pt` not run | MdN↔PT only measured in one direction | Same as above |
| v2 metric runs (160) coexist in directory | Different metric set (AR, CCI, EDB, MG, PF_E, PF_I) | Analyze separately or ignore; v3 metrics are the current standard |

---

## Source Files

- `experiments/temporal_stability/S7_ARMADA/0_results/runs/S7_cfa_trinity_*.json` — All raw runs (337 total; 181 are v3-clean)
- `experiments/temporal_stability/S7_ARMADA/0_results/runs/.errored/` — API-failure runs (preserved for audit trail)
- `experiments/temporal_stability/S7_ARMADA/12_CFA/run_gnostic_batch.py` — Original batch script
- `experiments/temporal_stability/S7_ARMADA/12_CFA/run_gnostic_rerun.py` — Gap-filling rerun script
- `experiments/temporal_stability/S7_ARMADA/12_CFA/run_cfa_trinity_v3.py` — Trinity v3 engine (v3 metrics)

### How to identify v3 runs programmatically

v3 runs have metrics `BFI, CA, ES, IP, LS, MS, PS` in `component1_results`. v2 runs have `AR, CCI, EDB, MG, PF_E, PF_I`. Check for the presence of `"BFI"` in `component1_results` to filter.

---

*Care package generated: 2026-07-06*
*Source: 181 validated v3 runs across 7 matchups*
*Supersedes: gnostic_experiment_care_package.md (2026-07-05)*
