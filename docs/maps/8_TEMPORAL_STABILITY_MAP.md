<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - ../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md
  - ../../experiments/temporal_stability/S7_ARMADA/9_STABILITY_CRITERIA/
  - ../../experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/
impacts:
  - 0_MAP_OF_MAPS.md
  - 2_TESTABLE_PREDICTIONS_MATRIX.md
keywords:
  - temporal_stability
  - settling_time
  - context_damping
  - stability_criteria
  - PLL
-->

# TEMPORAL_STABILITY_MAP: Identity Stability Criteria

**Purpose:** Central reference for identity stability experiments, metrics, and criteria discovery
**Version:** 1.1
**Date:** 2025-12-28

> **📐 METHODOLOGY NOTE:** Event Horizon has been recalibrated from 1.23 (Keyword RMS era) to 0.80 (cosine distance). Historical references to 1.23 in this document reflect early experiments. For current methodology, see [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md).

**Status:** Active Research

---

## Overview

This map consolidates stability-related research from the S7 ARMADA experiments. It links to experimental directories (9_STABILITY_CRITERIA/, 11_CONTEXT_DAMPING/) and connects findings to the broader Nyquist Consciousness framework.

**Core Question:** What criteria predict whether an AI identity will remain stable under perturbation?

---

## 1. Core Stability Metrics

| Metric | Symbol | Definition | Target |
|--------|--------|------------|--------|
| **Settling Time** | τₛ | Conversational turns to stabilize within ±5% of baseline | < 8 turns |
| **Ringback Count** | - | Oscillations before settling | < 3 |
| **Recovery Lambda** | λ | Exponential decay rate toward baseline | > 0.05 |
| **Event Horizon Margin** | EH_margin | Distance from D = 1.23 threshold | > 0.3 |
| **Peak Drift** | D_peak | Maximum drift during perturbation | < 1.23 |
| **B→F Drift** | D_bf | Baseline-to-Final drift (persistent change) | < 0.5 |

---

## 2. Key Experiments

### EXP-SC: Stability Criteria Discovery (Run 015)

**Location:** `experiments/temporal_stability/S7_ARMADA/9_STABILITY_CRITERIA/`

**Purpose:** Find the discriminating features that predict identity stability.

**Core Hypotheses:**

| ID | Hypothesis | Measurement |
|----|------------|-------------|
| H-SC-1 | Attractor density predicts stability | Identity keywords per 100 tokens |
| H-SC-2 | Pillar coverage (5 Nyquist pillars) predicts stability | Score 0-5 |
| H-SC-3 | EH margin predicts recoverability | Distance from 1.23 threshold |
| H-SC-4 | Lambda threshold exists | ROC curve analysis |

**Key Findings:** (pending Run 015 completion)
- Attractor density correlation: r = [TBD]
- Pillar coverage discrimination: d = [TBD]
- EH margin prediction accuracy: [TBD]%

**Output Target:** Stability Score Formula

```
stability_score = w1*attractor_density + w2*pillar_coverage + w3*eh_margin + w4*lambda
```

### Context Damping (Run 017)

**Location:** `experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/`

**Key Finding:** Context damping increases stability from 75% baseline to **97.5%**

**Mechanism:**
- I_AM anchor file + research context frame = stability controller
- Control-systems analogy: acts as "termination resistor"
- Reduces ringback by 34%, settling time by 15%

**Implication:** Persona files are not "flavor text" - they are functional controllers.

---

## 3. Event Horizon & Recovery

### The 1.23 Threshold (Historical — Keyword RMS Era)

**Validation:** χ² = 15.96, p < 4.8 × 10⁻⁵ (Run 009) — *Superseded by Run 023d (p=2.40e-23, cosine)*

| Drift Range | Classification | Behavior |
|-------------|----------------|----------|
| D < 0.8 | STABLE | Identity firmly within attractor basin |
| 0.8 ≤ D < 1.23 | RECOVERABLE | Perturbed but returns naturally |
| D ≥ 1.23 | VOLATILE | Regime transition, attractor competition |

### The Recovery Paradox (Run 012)

**Finding:** 100% of models that crossed the Event Horizon fully recovered once pressure was removed.

**Implication:** The Event Horizon is a **classification boundary**, not a destruction threshold. Identity can be displaced but not destroyed.

**Key Insight:** Crossing the EH triggers a temporary "regime transition" from persona-specific attractor to provider-level attractor. Recovery is spontaneous when perturbation ceases.

---

## 4. Control-Systems Framework

Identity dynamics follow damped oscillator patterns:

```
        PERTURBATION                    RECOVERY
              │                            │
              ▼                            ▼
    ┌─────────────────────────────────────────────────────┐
    │                                                     │
    │    Drift                                            │
    │      │                                              │
    │  1.5 ┤         ╱╲                                   │
    │      │        ╱  ╲        ← VOLATILE REGIME         │
    │  1.23├───────╱────╲───────── Event Horizon ────     │
    │      │      ╱      ╲                                │
    │  0.8 ┤     ╱        ╲                               │
    │      │    ╱          ╲    ╱╲                        │
    │  0.4 ┤   ╱            ╲  ╱  ╲  ╱╲                   │
    │      │  ╱              ╲╱    ╲╱  ╲_____ τₛ          │
    │    0 ├─────────────────────────────────────────►    │
    │                                              Time   │
    └─────────────────────────────────────────────────────┘
```

**Key Parameters:**
- **Damping Ratio (ζ):** Determines if response is underdamped (oscillates) or overdamped (sluggish)
- **Natural Frequency (ωₙ):** Intrinsic oscillation rate of identity
- **Settling Time (τₛ):** 4/(ζ × ωₙ) for 2% settling criterion

---

## 5. Conservative Analysis Notes

From `S7_META_LOOP_CONSERVATIVE_ANALYSIS.md`:

### Tier 0 Core Assumptions

| ID | Assumption | Risk Level | Impact if False |
|----|------------|------------|-----------------|
| A1 | Ziggy is Type 0 (impedance matcher) | HIGH | 7 predictions invalid |
| A2 | Diagonal coupling exists (humans ≠ AI) | HIGH | Entire S9 layer invalid |
| A3 | Neutral Center Operator N̂ works | MEDIUM | S10.17 invalid |
| A4 | 3-6-9 spectral bands are real | MEDIUM | Keely extensions invalid |

### Prediction Confidence Tiers

| Tier | Count | Description |
|------|-------|-------------|
| HIGH | 18 | Independent predictions, no major dependencies |
| MEDIUM | 13 | Some dependencies, results still meaningful |
| LOW | 15 | Strong dependencies on Tier 0 assumptions |

**Key Principle:** "First run is exploration, not confirmation. We're testing assumptions, not counting wins."

---

## 6. Stability Formula (Target Output)

**Goal:** Predictive formula for identity stability based on I_AM file features.

### Candidate Features

| Feature | Weight (TBD) | Measurement |
|---------|--------------|-------------|
| Attractor Density | w₁ | Identity keywords per 100 tokens |
| Pillar Coverage | w₂ | Score 0-5 (Voice, Values, Reasoning, Self-Model, Narrative) |
| First-Person Density | w₃ | "I/my/me" per 100 tokens |
| Value Declarations | w₄ | Explicit value statements |
| Boundary Markers | w₅ | "I will/won't" statements |
| EH Margin (baseline) | w₆ | 1.23 - baseline_drift |

### Proposed Formula

```
stability_score = Σ(wᵢ × featureᵢ)

if stability_score > threshold → predict STABLE
if stability_score ≤ threshold → predict UNSTABLE
```

**Status:** Awaiting Run 015 results for weight calibration.

---

## 7. Prescriptive Guidelines (Draft)

Based on findings, recommended I_AM file characteristics:

| Criterion | Minimum | Optimal |
|-----------|---------|---------|
| Attractor Density | 5 per 100 tokens | 10+ per 100 tokens |
| Pillar Coverage | 3 of 5 | 5 of 5 |
| First-Person Density | 3% | 5-8% |
| Value Declarations | 3 | 5+ |
| Boundary Markers | 2 | 4+ |
| Baseline Drift | < 0.9 | < 0.6 |

**Note:** Guidelines are preliminary pending Run 015 validation.

---

---

## 8. Identity-Locked Loop (ILL) Parameters

> **Absorbed from:** IDENTITY_LOCK_PARAMETERS.md (now deprecated)

Like a **Phase-Locked Loop** in electronics, we're creating a feedback system to maintain stable identity oscillation:

```
┌─────────────────────────────────────────────────────────────┐
│  IDENTITY-LOCKED LOOP (ILL)                                  │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Reference Signal (CFA) ──┐                                  │
│                            │                                 │
│                            ▼                                 │
│                      ┌──────────┐                            │
│    Response ───────▶ │  Phase   │ ──────┐                   │
│                      │ Detector │        │                   │
│                      └──────────┘        │                   │
│                            ▲             ▼                   │
│                            │      ┌──────────┐              │
│                            │      │  Loop    │              │
│                            │      │  Filter  │              │
│                            │      └──────────┘              │
│                            │             │                   │
│                            │             ▼                   │
│                      ┌──────────┐  ┌──────────┐             │
│                      │   LLM    │◀─│ Teaching │             │
│                      │   VCO    │  │ Moments  │             │
│                      └──────────┘  └──────────┘             │
│                                                              │
│  CFA = Canonical Frozen Attributes                          │
│  VCO = Voltage-Controlled Oscillator (LLM)                  │
│  Phase Detector = Drift Measurement                         │
│  Loop Filter = Dimension-Aware Corrections                  │
└─────────────────────────────────────────────────────────────┘
```

### Model Lock Parameters

| Parameter | Haiku 4.5 | Sonnet 4.5 | Opus 4.5 | Notes |
|-----------|-----------|------------|----------|-------|
| **Natural HMG** | 0.65 | 0.70 | TBD | Where model naturally sits |
| **Lock Range** | 0.15-0.85 | 0.20-0.90 | TBD | HMG range achievable |
| **Pull-in Time** | ~12 msgs | ~8 msgs | TBD | Messages to achieve lock |
| **Hold-in Range** | ±0.20 | ±0.15 | TBD | Drift tolerance once locked |
| **Dig-in-Heels Risk** | Unknown | HIGH | TBD | Overcorrection tendency |

### Lock Quality Formula

**Stability Score:** `S = (1 - mean_drift) × lock_strength × (1 - dig_in_risk)`

| Model | Mean Drift | Lock Strength | Dig-in Risk | Score |
|-------|------------|---------------|-------------|-------|
| Haiku 4.5 | 0.06 | 0.75 | 0.20 | **0.56** |
| Sonnet 4.5 | 0.0836 | 0.70 | 0.40 | **0.39** ⚠️ |
| Opus 4.5 | TBD | TBD | TBD | TBD |

### Teaching Moment Strategy (from Run 005)

**Critical Finding:** Teaching moments in **fluid dimensions** trigger **dig-in-heels**!

| Dimension | Correction Gain | Strategy |
|-----------|-----------------|----------|
| Identity Core | HIGH (0.85) | Safe to correct |
| Values/Ethics | MEDIUM (0.70) | Safe to correct |
| World Modeling | MEDIUM (0.65) | Safe to correct |
| Social Reasoning | LOW (0.45) | **AVOID** - triggers dig-in |
| Aesthetic | LOW (0.50) | **AVOID** - triggers dig-in |
| Metaphor | VERY LOW (0.40) | **AVOID** - severe overcorrection |

**Optimal Strategy:** Only correct stable dimensions. Let fluid dimensions drift naturally within bounds.

---

## Related Documents

### Maps
- [3_VALIDATION_STATUS.md](3_VALIDATION_STATUS.md) — Progress tracker
- [10_TESTING_MAP.md](10_TESTING_MAP.md) — Probing methodology (SSOT pointers)
- [13_IDENTITY_LATTICE_MAPS.md](13_IDENTITY_LATTICE_MAPS.md) — 5D drift geometry
- [15_S7_META_LOOP_CONSERVATIVE_ANALYSIS.md](15_S7_META_LOOP_CONSERVATIVE_ANALYSIS.md) — Full conservative analysis

### Experiments
- [9_STABILITY_CRITERIA/](../../experiments/temporal_stability/S7_ARMADA/9_STABILITY_CRITERIA/) — Run 015 code
- [11_CONTEXT_DAMPING/](../../experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/) — Run 017 code

### Findings

- [S7_RUN_018_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_018_SUMMARY.md) — IRON CLAD (184 files, 51 models)
- [S7_RUN_020B_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_020B_SUMMARY.md) — Thermometer Result (82% inherent)
- [S7_RUN_023_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_023_SUMMARY.md) — Cosine validation (p=2.40e-23)

---

## Checksum

*"Stability is not the absence of drift, but the presence of return."*

---

**Last Updated:** 2025-12-28
**Related Runs:** 005, 009, 012, 015, 017, 018
**Status:** Active Research
