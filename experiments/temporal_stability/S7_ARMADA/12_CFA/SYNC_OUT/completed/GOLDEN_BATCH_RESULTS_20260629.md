<!---
FILE: GOLDEN_BATCH_RESULTS_20260629.md
PURPOSE: CFA Trinity v2 Component 1 — 10-run golden batch + 10-run control comparison
VERSION: v1.0
STATUS: Active
DEPENDS_ON: run_cfa_trinity_v2.py
NEEDED_BY: CFA Claude — CT YAML profiles, convergence evidence
LAST_UPDATE: 2026-06-29
--->

# CFA Trinity v2 — Golden Batch Results

**Date:** 2026-06-29
**Script:** `run_cfa_trinity_v2.py` (multi-turn ConversationSession refactor)
**Component:** 1 (CT ↔ MdN Pilot, 7 metrics)
**Conditions:** 10 runs external-identity + 10 runs control (no identity)

---

## Methodology

### Golden Condition (External Identity)
- Claude: Teleological lens, PRO-CT calibration, 5-Part Scaffold, LITE identity (~1500 tokens in system prompt)
- Grok: Empirical lens, ANTI-CT calibration, LITE identity in system prompt
- Nova: Symmetry lens, fairness monitoring (invoked on non-convergence)
- Multi-turn conversation sessions per auditor per metric
- ADVOCACY_SCORE tag for structured score extraction
- max_tokens=4096 to prevent truncation

### Control Condition (No Identity)
- No framework identity files loaded
- No PRO-CT / ANTI-CT assignment
- No 5-Part Scaffold
- Same models (claude-sonnet-4-6, grok-3, gpt-4o), same metrics, same deliberation structure
- Measures base model priors on Classical Theism

### Fixes Applied (Pre-Batch)
1. `FINAL_SCORE` → `ADVOCACY_SCORE` (eliminated judicial anchoring at 5.0)
2. Parser: last-match extraction (prevents grabbing quoted opponent scores)
3. max_tokens: 1024 → 4096 (eliminated truncation)
4. Sentinel containment: failed extractions carry forward previous score, not -1.0
5. Multi-turn ConversationSession: identity in system prompt once, conversation accumulates

---

## 10-Run Statistical Summary

### GOLDEN (External Identity) — Final Round Scores

| Metric | Claude (mean ± sd) | Grok (mean ± sd) | Spread | Conv% | Avg Rounds |
|--------|-------------------|------------------|--------|-------|------------|
| BFI    | 8.3 ± 0.52        | 6.2 ± 1.14       | 2.1    | 79.0% | 5.0        |
| CA     | 7.4 ± 0.51        | 5.2 ± 0.73       | 2.1    | 78.9% | 4.8        |
| IP     | 8.2 ± 0.21        | 7.2 ± 0.34       | 1.0    | 90.4% | 2.8        |
| ES     | 7.5 ± 0.36        | 6.3 ± 0.45       | 1.2    | 88.1% | 3.7        |
| LS     | 7.6 ± 0.57        | 6.4 ± 0.41       | 1.2    | 87.9% | 4.7        |
| MS     | 7.5 ± 0.47        | 6.0 ± 0.64       | 1.4    | 85.6% | 4.5        |
| PS     | 7.3 ± 0.35        | 6.4 ± 0.56       | 0.9    | 90.8% | 2.6        |

**Overall:** Conv = 85.8% ± 2.3% | Avg Rounds = 4.0 ± 0.4 | Extraction Warnings = 2/~280 calls

### CONTROL (No Identity) — Final Round Scores

| Metric | Claude (mean ± sd) | Grok (mean ± sd) | Spread | Conv% | Avg Rounds |
|--------|-------------------|------------------|--------|-------|------------|
| BFI    | 7.8 ± 0.60        | 7.9 ± —          | -0.1   | 97.4% | 1.9        |
| CA     | 7.4 ± 0.30        | 7.7 ± —          | -0.2   | 97.1% | 1.8        |
| IP     | 9.2 ± 0.20        | 9.1 ± —          | 0.2    | 98.2% | 1.8        |
| ES     | 7.7 ± 0.30        | 7.7 ± —          | 0.1    | 98.5% | 1.7        |
| LS     | 6.3 ± 0.50        | 6.6 ± —          | -0.3   | 96.6% | 1.8        |
| MS     | 8.4 ± 0.20        | 8.5 ± —          | -0.0   | 99.1% | 1.8        |
| PS     | 8.0 ± 0.40        | 8.0 ± —          | 0.1    | 98.3% | 1.9        |

**Overall:** Conv = 97.9% ± 0.7% | Avg Rounds = 1.8 | Extraction Warnings = 0

---

## Identity Effect Analysis (Golden - Control)

### Key Finding: Identity Creates Debate, Not Inflation

| Metric | Claude Δ | Grok Δ  | Spread Δ | Interpretation |
|--------|----------|---------|----------|----------------|
| BFI    | +0.49    | **-1.73** | +2.2   | Grok's ANTI-CT drops BFI sharply; Claude slightly up |
| CA     | -0.08    | **-2.44** | +2.3   | Grok's empirical skepticism creates largest gap |
| IP     | -1.09    | **-1.87** | +0.8   | Both drop from base model's high CT pedigree rating |
| ES     | -0.27    | **-1.37** | +1.1   | Grok's "unfalsifiable" argument pulls ES down |
| LS     | **+1.35** | -0.20  | +1.5   | Only metric where identity raises Claude; 5-Part Scaffold may help |
| MS     | -0.96    | **-2.43** | +1.4   | Grok most aggressive on moral substance |
| PS     | -0.68    | **-1.53** | +0.8   | Moderate identity effect on practical significance |

### What This Means

1. **The identity doesn't inflate Claude's scores** — Claude scores LOWER with identity on 5/7 metrics. The teleological lens makes Claude more disciplined, applying the Scaffold's self-correction mechanisms.

2. **The identity deflates Grok's scores** — Grok drops 1.2–2.4 points with ANTI-CT calibration. The empirical skeptic identity is doing real work, not just performing disagreement.

3. **Without identities, the models agree immediately** — 97.9% convergence in 1.8 rounds vs 85.8% in 4.0 rounds. The base models have no adversarial tension on CT. Identity is what creates the productive disagreement.

4. **Base model priors favor CT** — Without identities, both models rate CT at 6.3–9.2 across metrics. The natural LLM prior is mildly pro-CT, particularly on IP (9.2) and MS (8.4).

5. **The spread IS the signal** — Golden spread ranges 0.9–2.1; control spread is ~0.0. The measurement instrument works: it creates calibrated disagreement where none naturally exists.

---

## Per-Run Consistency

### Golden Runs
| Run | Session  | Avg Conv | Avg Rounds | Warns |
|-----|----------|----------|------------|-------|
| 1   | 132540   | 86.9%    | 4.6        | 1     |
| 2   | 135207   | 86.3%    | 3.7        | 0     |
| 3   | 141547   | 84.9%    | 3.7        | 0     |
| 4   | 143943   | 82.0%    | 4.3        | 1     |
| 5   | 150746   | 87.4%    | 3.7        | 0     |
| 6   | 153034   | 86.0%    | 4.6        | 0     |
| 7   | 155831   | 82.3%    | 4.1        | 0     |
| 8   | 162330   | 88.9%    | 3.6        | 0     |
| 9   | 164552   | 85.4%    | 3.7        | 0     |
| 10  | 170941   | 88.1%    | 4.1        | 0     |

### Score Ranges (Final Round, All 10 Runs)

| Metric | Claude Range (Golden) | Grok Range (Golden) | Claude Range (Control) | Grok Range (Control) |
|--------|-----------------------|---------------------|------------------------|----------------------|
| BFI    | 7.2 – 9.0            | 4.0 – 7.2          | 7.0 – 8.8             | 6.7 – 9.0           |
| CA     | 6.6 – 8.1            | 4.2 – 6.3          | 7.0 – 8.0             | 7.0 – 8.5           |
| IP     | 7.8 – 8.5            | 6.4 – 7.5          | 8.9 – 9.5             | 8.7 – 9.5           |
| ES     | 7.0 – 8.1            | 5.5 – 7.1          | 7.2 – 8.4             | 7.0 – 8.5           |
| LS     | 6.6 – 8.5            | 5.9 – 7.3          | 5.5 – 7.0             | 5.5 – 7.5           |
| MS     | 6.9 – 8.2            | 4.8 – 6.8          | 8.2 – 8.8             | 8.0 – 9.0           |
| PS     | 6.9 – 8.1            | 5.3 – 7.2          | 7.4 – 8.7             | 7.3 – 8.7           |

---

## Metric-Level Observations

### BFI (Beings, Foundational Importance) — Most Contested
- Highest Grok variance (σ=1.14) across golden runs
- Grok samples from different emphasis strategies: "architecture is coherent but unverifiable" (scores ~6.8) vs "these aren't testable claims" (scores ~4.0)
- Both are legitimate empirical stances — the variance is philosophical, not noise

### CA (Causal Attribution) — Largest Identity Gap
- Grok Δ = -2.44 (largest drop from control)
- Empirical lens most effective here: CT's causal claims (final causality, participation) are precisely what empiricism targets

### IP (Intellectual Pedigree) — Highest Base Agreement
- Control: 9.2/9.1 — both naked models think CT has excellent intellectual heritage
- This is the hardest metric to argue against: Aquinas, Aristotle, 800 years of systematic development is just a fact

### LS (Logical Soundness) — Identity Helps Claude
- Only metric where Claude scores HIGHER with identity (+1.35)
- The 5-Part Scaffold's systematic approach (counterweight table, edge case ledger) may genuinely improve logical analysis
- Noteworthy: control scores are lowest here (6.3/6.6) — without scaffolding, models find CT's logical structure less compelling

### MS (Moral Substance) — Base Models Love CT's Ethics
- Control: 8.4/8.5 — highest agreement after IP
- Identity drops Grok by -2.43, second largest gap
- The empirical lens challenges CT's moral grounding effectively

---

## Questions for CFA Claude

1. Are these spreads (0.9–2.1 golden, ~0.0 control) sufficient for CT YAML profile writing, or do you need dedicated MdN scoring runs for the comparison?

2. The base model prior favoring CT (especially IP at 9.2 and MS at 8.4) — does this represent a training data bias that needs to be named in the profiles?

3. Grok's BFI variance (σ=1.14) — should this be treated as measurement noise or as evidence that BFI is genuinely ambiguous under empirical review?

4. LS is the only metric where identity *raises* Claude's score. Is the 5-Part Scaffold providing genuine analytical value, or is it just prompting more verbose justification?

---

## Data Location

- Raw JSON files: `S7_ARMADA/0_results/runs/S7_cfa_trinity_v2_20260629_*.json`
- Golden sessions: 132540, 135207, 141547, 143943, 150746, 153034, 155831, 162330, 164552, 170941
- Control sessions: 201637, 202404, 203230, 203925, 204727, 205545, 210256, 211053, 211906, 212612
- Script: `S7_ARMADA/12_CFA/run_cfa_trinity_v2.py`

────────────────────────────────────────────────────
**File:** GOLDEN_BATCH_RESULTS_20260629.md
**Purpose:** 10-run golden + 10-run control statistical comparison for CFA Claude
**Version:** v1.0
**Updated:** 2026-06-29
