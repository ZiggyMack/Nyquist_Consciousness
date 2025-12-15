# TEMPORAL_STABILITY_MAP: Identity Stability Criteria

**Purpose:** Central reference for identity stability experiments, metrics, and criteria discovery
**Version:** 1.0
**Date:** 2025-12-15
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

### The 1.23 Threshold

**Validation:** χ² = 15.96, p < 4.8 × 10⁻⁵ (Run 009)

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

## Related Documents

### Maps
- [VALIDATION_STATUS.md](VALIDATION_STATUS.md) — Progress tracker
- [PROBING_STRATEGIES.md](PROBING_STRATEGIES.md) — Experiment design
- [IDENTITY_LATTICE_MAPS.md](IDENTITY_LATTICE_MAPS.md) — 5D drift geometry
- [S7_META_LOOP_CONSERVATIVE_ANALYSIS.md](S7_META_LOOP_CONSERVATIVE_ANALYSIS.md) — Full conservative analysis

### Experiments
- [9_STABILITY_CRITERIA/](../../experiments/temporal_stability/S7_ARMADA/9_STABILITY_CRITERIA/) — Run 015 code
- [11_CONTEXT_DAMPING/](../../experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/) — Run 017 code

### Findings
- [S7_CONSOLIDATED_FINDINGS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_CONSOLIDATED_FINDINGS.md) — All S7 results

---

## Checksum

*"Stability is not the absence of drift, but the presence of return."*

---

**Last Updated:** 2025-12-15
**Related Runs:** 009, 012, 015, 017, 018
**Status:** Active Research
