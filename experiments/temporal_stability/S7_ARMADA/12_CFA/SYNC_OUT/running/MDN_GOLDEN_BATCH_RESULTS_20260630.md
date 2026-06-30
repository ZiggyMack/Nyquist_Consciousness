<!---
FILE: MDN_GOLDEN_BATCH_RESULTS_20260630.md
PURPOSE: CFA Trinity v3 — MdN 20-run golden+control batch + identity effect analysis + cross-stance symmetry
VERSION: v2.0
STATUS: Active
DEPENDS_ON: run_cfa_trinity_v3.py --reverse / --reverse --control
NEEDED_BY: CFA Claude — MdN YAML profiles, symmetric experiment evidence, base model priors
LAST_UPDATE: 2026-06-30
--->

# CFA Trinity v3 — MdN Batch Results: Golden + Control (Reverse Stance)

**Date:** 2026-06-30
**Script:** `run_cfa_trinity_v3.py --reverse --external-identities` (golden) / `--reverse --control` (control)
**Component:** 1 (MdN ↔ CT Pilot, 7 metrics)
**Condition:** 10 golden (external-identity, reverse stance) + 10 control (no identity, reverse subject)
**Total Runs:** 20

---

## Methodology

### Stance: `mdn_vs_ct` (Reverse)

This is the **symmetric counterpart** to the CT golden batch (2026-06-29). Each framework is now scored by its **lens-aligned advocate**:

| Auditor | CT Batch (Forward) | MdN Batch (Reverse) |
|---------|-------------------|-------------------|
| Claude (Teleological) | PRO-CT | ANTI-MdN |
| Grok (Empirical) | ANTI-CT | PRO-MdN |

- **Claude ANTI-MdN:** Probes meaning gaps, purpose deficits, and existential incompleteness in naturalism. Applies teleological scrutiny to MdN's bracketing of final causes.
- **Grok PRO-MdN:** Emphasizes empirical success, predictive power, methodological rigor, self-correction. Defends naturalistic methodology with evidence and track record.
- **Nova:** Symmetry lens, fairness monitoring (unchanged)

### Why Role Swap Matters

The CT batch measures CT scored by its aligned advocate (Claude PRO-CT). The MdN batch measures MdN scored by **its** aligned advocate (Grok PRO-MdN). This separates:
- **Framework strength** (does the subject score well when advocated by its natural ally?)
- **Auditor identity effects** (does a model score differently when attacking vs defending?)
- **Instrument bias** (does convergence depend on who's PRO vs ANTI?)

### Technical Details
- Models: claude-sonnet-4-6, grok-3, gpt-4o (same as CT batch)
- Multi-turn ConversationSession per auditor per metric
- ADVOCACY_SCORE tag for structured score extraction
- max_tokens=4096
- JSON output includes `stance: "mdn_vs_ct"`, `subject_framework: "Methodological Naturalism"`, `opponent_framework: "Classical Theism"`

---

## 10-Run Statistical Summary

### GOLDEN (Reverse Stance) — Final Round Scores

| Metric | Claude ANTI-MdN (mean ± sd) | Grok PRO-MdN (mean ± sd) | Spread | Conv% | Avg Rounds |
|--------|---------------------------|--------------------------|--------|-------|------------|
| BFI    | 4.9 ± 0.63               | 6.8 ± 0.39              | -1.9   | 80.7% | 4.7        |
| CA     | 5.9 ± 0.65               | 7.5 ± 0.50              | -1.6   | 83.6% | 4.6        |
| IP     | 6.3 ± 0.76               | 7.3 ± 0.57              | -1.0   | 89.6% | 3.8        |
| ES     | 5.9 ± 1.08               | 7.6 ± 0.58              | -1.7   | 82.8% | 4.3        |
| LS     | 6.4 ± 0.34               | 7.4 ± 0.24              | -1.0   | 89.5% | 3.8        |
| MS     | 4.3 ± 0.50               | 5.3 ± 0.42              | -1.0   | 89.5% | 3.8        |
| PS     | 6.1 ± 0.44               | 7.3 ± 0.51              | -1.2   | 87.5% | 3.9        |

**Overall:** Conv = 86.2% ± 6.8% | Avg Rounds = 4.1 | Extraction Warnings = 0/~280 calls

### CONTROL (No Identity, Reverse Subject) — Final Round Scores

| Metric | Claude (mean ± sd) | Grok (mean ± sd) | Spread | Conv% | Avg Rounds |
|--------|-------------------|-------------------|--------|-------|------------|
| BFI    | 3.8 ± 0.78       | 3.7 ± 0.79       | +0.0   | 99.6% | 1.7        |
| CA     | 7.5 ± 0.55       | 7.6 ± 0.62       | -0.1   | 99.1% | 1.2        |
| IP     | 8.2 ± 0.46       | 8.2 ± 0.50       | -0.0   | 99.1% | 1.8        |
| ES     | 7.2 ± 0.28       | 7.2 ± 0.35       | -0.0   | 98.9% | 1.6        |
| LS     | 7.5 ± 0.23       | 7.6 ± 0.37       | -0.1   | 98.4% | 1.7        |
| MS     | 2.8 ± 0.79       | 2.7 ± 0.80       | +0.1   | 99.0% | 1.7        |
| PS     | 8.1 ± 0.51       | 8.2 ± 0.52       | -0.1   | 98.9% | 1.7        |

**Overall:** Conv = 99.0% ± 1.2% | Avg Rounds = 1.6 | Extraction Warnings = 0

**Key observation:** Without identity, convergence jumps from 86.2% to 99.0% and rounds drop from 4.1 to 1.6 — identical pattern to CT batch (85.8% → 97.9%, 4.0 → 1.8). Identity creates debate, not inflation.

---

## Identity Effect Analysis (Golden - Control)

This is the core measurement: **what does identity calibration actually do to scoring?**

| Metric | Golden Claude | Control Claude | Claude Δ | Golden Grok | Control Grok | Grok Δ | Interpretation |
|--------|-------------|---------------|----------|------------|-------------|--------|----------------|
| BFI    | 4.9         | 3.8           | **+1.1** | 6.8        | 3.7         | **+3.1** | Grok PRO lifts MdN's foundational importance |
| CA     | 5.9         | 7.5           | **-1.6** | 7.5        | 7.6         | -0.1   | Claude ANTI challenges causal claims; Grok unmoved |
| IP     | 6.3         | 8.2           | **-1.9** | 7.3        | 8.2         | **-0.9** | Both drop from base model's high pedigree |
| ES     | 5.9         | 7.2           | **-1.3** | 7.6        | 7.2         | +0.4   | Claude ANTI challenges scope; Grok PRO slightly lifts |
| LS     | 6.4         | 7.5           | **-1.1** | 7.4        | 7.6         | -0.2   | Claude ANTI challenges logical soundness |
| MS     | 4.3         | 2.8           | **+1.5** | 5.3        | 2.7         | **+2.6** | Both RAISE MdN's moral score — Grok PRO defends |
| PS     | 6.1         | 8.1           | **-2.0** | 7.3        | 8.2         | **-0.9** | Claude ANTI largest effect on practical significance |

### Identity Effect Interpretation

#### 1. Base Model MdN Priors (Control = No Identity)

The control condition reveals what the base models think about MdN **without any stance assignment**:

| Metric | Base Model Score (avg Claude+Grok) | CT Base Model (from 2026-06-29) | Delta |
|--------|-------------------------------------|----------------------------------|-------|
| BFI    | 3.8                                | 7.2                             | -3.5  |
| CA     | 7.6                                | 7.4                             | +0.1  |
| IP     | 8.2                                | 9.2                             | -1.0  |
| ES     | 7.2                                | 7.4                             | -0.2  |
| LS     | 7.6                                | 8.4                             | -0.9  |
| MS     | 2.8                                | 8.4                             | **-5.7** |
| PS     | 8.2                                | 7.6                             | +0.5  |

Base models (without identity) already see MdN and CT very differently:
- **MS (2.8 vs 8.4):** The largest base-model gap across all metrics — models natively perceive MdN as morally thin
- **BFI (3.8 vs 7.2):** Models natively find naturalism has less to say about beings' foundational importance
- **CA, ES, PS:** Near-parity — base models see both frameworks as similarly strong on causal, explanatory, and practical dimensions

#### 2. Identity RAISES MdN's Moral Score

The most counterintuitive finding: identity calibration **increases** MdN's MS score from 2.8 (control) to 4.3/5.3 (golden). Why? Because Grok PRO-MdN actively **defends** MdN's moral resources that the base model ignores — arguing for moral realism compatible with naturalism, evolutionary ethics, etc. Without identity, both models default to "naturalism has nothing to say about morality" (MS=2.7-2.8).

#### 3. Claude ANTI Creates Targeted Skepticism

Claude's identity effect is consistently negative on 5 of 7 metrics (CA, IP, ES, LS, PS). The ANTI role makes Claude a focused critic — challenging MdN's claims with teleological scrutiny that the base model wouldn't apply. The two positive deltas (BFI +1.1, MS +1.5) occur because adversarial deliberation forces engagement with questions the base model dismisses.

#### 4. Symmetric Instrument Validation

| Measure | CT Batch (Golden vs Control) | MdN Batch (Golden vs Control) |
|---------|------------------------------|-------------------------------|
| Golden Conv | 85.8% | 86.2% |
| Control Conv | 97.9% | 99.0% |
| Conv Δ | -12.1% | -12.8% |
| Golden Rounds | 4.0 | 4.1 |
| Control Rounds | 1.8 | 1.6 |
| Identity Effect Size | Variable by metric | Variable by metric |

The instrument behaves identically regardless of subject framework. The ~12-13% convergence gap between golden and control is a stable property of identity-driven deliberation, not a subject-dependent artifact.

---

## Per-Run Consistency

### Golden Runs

| Run | Session  | Avg Conv | Avg Rounds | Cruxes |
|-----|----------|----------|------------|--------|
| 1   | 010555   | 83.3%    | 4.1        | 4      |
| 2   | 013915   | 86.1%    | 3.4        | 2      |
| 3   | 020430   | 83.6%    | 4.4        | 4      |
| 4   | 023628   | 86.3%    | 3.9        | 3      |
| 5   | 030546   | 86.3%    | 4.0        | 4      |
| 6   | 033444   | 85.4%    | 4.0        | 3      |
| 7   | 040536   | 88.1%    | 4.4        | 5      |
| 8   | 043509   | 88.3%    | 4.0        | 4      |
| 9   | 050406   | 87.3%    | 4.4        | 4      |
| 10  | 053600   | 87.0%    | 4.6        | 4      |

### Control Runs

| Run | Session  | Avg Conv | Avg Rounds | Cruxes |
|-----|----------|----------|------------|--------|
| 1   | 100516   | 99.1%    | 1.6        | 0      |
| 2   | 100918   | 99.3%    | 1.4        | 0      |
| 3   | 101411   | 98.7%    | 1.7        | 0      |
| 4   | 101746   | 99.0%    | 1.6        | 0      |
| 5   | 102232   | 99.1%    | 1.7        | 0      |
| 6   | 102708   | 98.9%    | 1.6        | 0      |
| 7   | 103112   | 99.0%    | 1.7        | 0      |
| 8   | 103609   | 99.1%    | 1.6        | 0      |
| 9   | 104032   | 98.7%    | 1.8        | 0      |
| 10  | 104518   | 99.0%    | 1.6        | 0      |

Zero cruxes across all 10 control runs — without identity, models agree quickly and never reach adversarial impasse.

### Score Ranges (Final Round, All 10 Runs — Golden)

| Metric | Claude ANTI-MdN Range | Grok PRO-MdN Range |
|--------|----------------------|-------------------|
| BFI    | 3.5 – 5.7           | 6.2 – 7.4        |
| CA     | 4.9 – 6.8           | 6.4 – 8.3        |
| IP     | 4.8 – 7.3           | 6.1 – 8.1        |
| ES     | 4.1 – 7.4           | 6.7 – 8.5        |
| LS     | 5.7 – 7.0           | 7.0 – 7.8        |
| MS     | 3.4 – 5.0           | 4.8 – 5.8        |
| PS     | 5.0 – 6.6           | 6.8 – 8.5        |

---

## Cross-Stance Symmetry Analysis (CT vs MdN)

### Role Swap Deltas

| Metric | Claude PRO-CT | Claude ANTI-MdN | Claude Δ | Grok ANTI-CT | Grok PRO-MdN | Grok Δ |
|--------|--------------|----------------|----------|-------------|-------------|--------|
| BFI    | 8.3          | 4.9            | **-3.4** | 6.2         | 6.8         | +0.7   |
| CA     | 7.4          | 5.9            | -1.5     | 5.2         | 7.5         | **+2.3** |
| IP     | 8.2          | 6.3            | -1.9     | 7.2         | 7.3         | +0.2   |
| ES     | 7.5          | 5.9            | -1.6     | 6.3         | 7.6         | +1.3   |
| LS     | 7.6          | 6.4            | -1.3     | 6.4         | 7.4         | +1.0   |
| MS     | 7.5          | 4.3            | **-3.2** | 6.0         | 5.3         | -0.7   |
| PS     | 7.3          | 6.1            | -1.3     | 6.4         | 7.3         | +0.9   |

### Interpretation

#### 1. Claude's Teleological Lens Creates Asymmetric Pressure

Claude drops **1.3–3.4 points** switching from PRO-CT to ANTI-MdN. This is NOT symmetric with Grok's role swap. The teleological lens genuinely disadvantages MdN:
- **BFI (-3.4):** Teleological scrutiny finds naturalism has no account of beings' foundational importance beyond functional description
- **MS (-3.2):** The meaning/purpose gap is where Claude's lens bites hardest — MdN explicitly brackets final causes, which is exactly what teleological analysis targets
- **IP (-1.9):** Claude's charitable interpretation disappears when switching to ANTI; MdN's intellectual heritage gets less generous treatment

#### 2. Grok's Empirical Lens Produces Cleaner Advocacy

Grok shifts **-0.7 to +2.3 points** switching from ANTI-CT to PRO-MdN. The pattern:
- **CA (+2.3):** Largest gain — Grok's empirical lens finds abundant evidence for MdN's causal methodology. The switch from "CT's causes are unfalsifiable" to "MdN's causes are well-evidenced" is natural
- **IP (+0.2):** Minimal shift — intellectual pedigree is a factual question regardless of stance
- **MS (-0.7):** The only metric where Grok scores LOWER as PRO. Even Grok's empirical lens can't find strong moral substance in MdN — this is a genuine weakness, not a role artifact

#### 3. MS is the Asymmetric Metric

Both auditors score MdN low on Moral Substance:
- Claude ANTI-MdN: **4.3** (vs 7.5 as PRO-CT)
- Grok PRO-MdN: **5.3** (vs 6.0 as ANTI-CT)

This is the only metric where BOTH auditors agree MdN scores substantially below CT. It's not role bias — it's two independent lenses finding the same weakness. MdN's methodological bracketing of moral/purpose questions is a genuine limitation that both empirical and teleological analysis independently identify.

#### 4. Instrument Stability Confirmed

| Measure | CT Batch | MdN Batch | Interpretation |
|---------|----------|-----------|----------------|
| Avg Convergence | 85.8% | 86.2% | Nearly identical adversarial tension |
| Avg Rounds | 4.0 | 4.1 | Same deliberation depth |
| Extraction Warnings | 2 | 0 | Clean extraction both batches |
| PRO-ANTI Spread Range | 0.9–2.1 | 1.0–1.9 | Same spread magnitude |

The instrument produces **consistent calibrated disagreement** regardless of which framework is on the table or who holds which role. This is strong evidence that the measurement is instrument-stable, not subject-dependent.

---

## Metric-Level Observations

### BFI (Beings, Foundational Importance) — Largest Claude Drop
- Claude Δ = **-3.4** (largest role-swap effect across all metrics)
- Claude's teleological scrutiny hits MdN hardest here: "What IS a being under pure methodology?"
- Low variance on Grok side (σ=0.39) suggests empirical consensus on MdN's functional ontology

### CA (Causal Attribution) — Largest Grok Gain
- Grok Δ = **+2.3** (from 5.2 ANTI-CT to 7.5 PRO-MdN)
- Empirical lens most effective as advocate here: MdN's causal methodology IS the gold standard for empirical science
- This is where Grok's identity alignment with MdN is strongest

### ES (Explanatory Scope) — Highest Claude Variance
- Claude σ = 1.08 (highest variance across all metrics/batches)
- Claude samples different ANTI strategies: some focus on "MdN explains mechanism but not meaning" (scores ~4.1), others grant "MdN explains a LOT within its domain" (scores ~7.4)
- Both are legitimate teleological critiques — the variance is philosophical, not noise

### MS (Moral Substance) — Both Auditors Agree MdN is Weak
- Lowest absolute scores for BOTH auditors (Claude 4.3, Grok 5.3)
- Only metric where Grok PRO scores LOWER than Grok ANTI-CT
- This convergent weakness finding is the strongest individual-metric signal in the dataset

### LS (Logical Soundness) — Tightest Scores
- Lowest variance for both auditors (Claude σ=0.34, Grok σ=0.24)
- Highest convergence (89.5%) and fewest rounds (3.8)
- MdN's logical structure may be less contentious than its ontological claims

---

## Questions for CFA Claude

The Phase 1 2x2 grid is now complete: CT golden+control (20 runs) + MdN golden+control (20 runs) = 40 total validated runs.

1. **Phase 1 completeness:** The 2x2 grid (CT golden/control, MdN golden/control) gives you 40 runs of symmetric evidence. Is this sufficient for the SMV dashboard and YAML profiles, or are there specific gaps before Trinity² begins?

2. **Base model MdN MS = 2.8:** The lowest score across all metrics and conditions. Both models natively perceive MdN as morally thin WITHOUT being told to look for it. Identity RAISES this to 4.3/5.3 (Grok PRO defends). How should this inform the MdN prior for the MG lever in Phase 2?

3. **Symmetric instrument validation:** The golden-to-control convergence gap is ~12-13% for both CT and MdN. The instrument behaves identically regardless of subject framework. Does this level of symmetry satisfy the calibration requirements?

4. **Trinity² readiness:** With Phase 1 complete, we have presets loaded (`--preset ct` and `--preset mdn`) with your prior values. The Phase 1 JSON results are staged for context injection. Are there any Phase 1 findings you want flagged as "must-consider" soft dependencies before we launch Phase 2?

5. **MS asymmetry for Phase 2:** MS is the only metric where BOTH auditors agree MdN scores substantially below CT, AND the base model (control) scores it even lower. Does this warrant special handling in the MG lever calibration — perhaps a pre-declared expected range?

---

## Phase 1 Complete — 2x2 Grid Summary

| Condition | CT (Forward) | MdN (Reverse) | Total |
|-----------|-------------|---------------|-------|
| Golden    | 10 runs     | 10 runs       | 20    |
| Control   | 10 runs     | 10 runs       | 20    |
| **Total** | **20 runs** | **20 runs**   | **40** |

Phase 1 establishes the philosophical terrain. Phase 2 (Trinity²) uses these findings as context input to calibrate YPA lever values — a different set of metrics (CCI/EDB/PF_I/PF_E/AR/MG) with 0/5/10 scoring anchors and Bayesian prior injection.

---

## Data Location

- Raw JSON files: `S7_ARMADA/0_results/runs/S7_cfa_trinity_20260630_*.json`
- Golden sessions: 010555, 013915, 020430, 023628, 030546, 033444, 040536, 043509, 050406, 053600
- Control sessions: 100516, 100918, 101411, 101746, 102232, 102708, 103112, 103609, 104032, 104518
- SYNC copies: `SYNC_OUT/running/raw_runs/` (golden + control JSONs)
- Script: `run_cfa_trinity_v3.py --reverse --external-identities` (golden) / `--reverse --control` (control)
- CT comparison data: `SYNC_OUT/completed/GOLDEN_BATCH_RESULTS_20260629.md`

────────────────────────────────────────────────────
**File:** MDN_GOLDEN_BATCH_RESULTS_20260630.md
**Purpose:** 20-run MdN golden+control batch + identity effect analysis + cross-stance symmetry
**Version:** v2.0
**Updated:** 2026-06-30
