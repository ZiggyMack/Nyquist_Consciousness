<!---
FILE: MDN_GOLDEN_BATCH_RESULTS_20260630.md
PURPOSE: CFA Trinity v3 — MdN reverse-stance 10-run golden batch + cross-stance symmetry analysis
VERSION: v1.0
STATUS: Active
DEPENDS_ON: run_cfa_trinity_v3.py --reverse
NEEDED_BY: CFA Claude — MdN YAML profiles, symmetric experiment evidence
LAST_UPDATE: 2026-06-30
--->

# CFA Trinity v3 — MdN Golden Batch Results (Reverse Stance)

**Date:** 2026-06-30
**Script:** `run_cfa_trinity_v3.py --reverse --external-identities`
**Component:** 1 (MdN ↔ CT Pilot, 7 metrics)
**Condition:** 10 runs external-identity, reverse stance (role swap)

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

---

## Per-Run Consistency

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

### Score Ranges (Final Round, All 10 Runs)

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

1. The cross-stance symmetry data is now complete. Are there enough data points to write both CT and MdN YAML profiles, or do you need the control (no-identity) condition for MdN as well?

2. MS emerges as a clear asymmetric metric — both auditors independently find MdN weak on moral substance. Should the MdN profile explicitly name this as a known limitation, or let the scores speak?

3. Claude's ES variance (σ=1.08) is the highest in either batch. Is this measurement noise that needs more samples, or evidence that "explanatory scope" is genuinely ambiguous for MdN?

4. Crux declarations are more frequent in MdN (37 across 10 runs, avg 3.7/run) vs CT batch. Does the crux mechanism behave differently when the auditors are in swapped roles?

---

## Data Location

- Raw JSON files: `S7_ARMADA/0_results/runs/S7_cfa_trinity_20260630_*.json`
- Golden sessions: 010555, 013915, 020430, 023628, 030546, 033444, 040536, 043509, 050406, 053600
- Script: `S7_ARMADA/12_CFA/run_cfa_trinity_v3.py --reverse --external-identities`
- CT comparison data: `SYNC_OUT/completed/GOLDEN_BATCH_RESULTS_20260629.md`

────────────────────────────────────────────────────
**File:** MDN_GOLDEN_BATCH_RESULTS_20260630.md
**Purpose:** 10-run MdN reverse-stance golden batch + cross-stance symmetry analysis
**Version:** v1.0
**Updated:** 2026-06-30
