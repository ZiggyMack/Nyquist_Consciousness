# Minimum Publishable Claims That Survive Peer Review

**Version:** 2.0
**Date:** 2025-12-22
**Source:** Nova's S7 Review (REVIEW_1.md lines 4501-4550) + Run 023 IRON CLAD
**Purpose:** Claims that can be published without needing to convince a hostile reviewer of metaphysics

---

> **📐 METHODOLOGY NOTE:** This document presents claims validated under multiple methodologies:
> - **Cosine Distance** (Current): Event Horizon = 0.80, Run 023 (825 experiments, 51 models)
> - **Keyword RMS** (Historical): Event Horizon = 1.23, Runs 008-009
>
> For full methodology reconciliation, see [../planning/METHODOLOGY_DOMAINS.md](../planning/METHODOLOGY_DOMAINS.md)

---

## Overview

These five claims form the defensible core of the Nyquist Consciousness framework. Each is grounded in empirical evidence and avoids ontological overreach.

---

## Claim A — Drift/PFI is a Valid, Structured Measurement

**(Instrument Validity)**

### A1. Embedding Invariance

Rankings remain highly correlated across multiple embedding models.

| Metric | Value |
|--------|-------|
| Spearman ρ range | 0.88–0.96 |
| Mean ρ | ≈0.91 |

**Implication:** Not a single-embedding artifact.

### A2. Low-Dimensional Structure

Drift vectors concentrate in a small number of principal components.

| Metric | Cosine (Current) | Euclidean (Archived) |
|--------|------------------|----------------------|
| PCs for 90% variance | **2** | 43 |
| Total dimensionality | 3072 | 3072 |

**Implication:** Identity is remarkably concentrated. Cosine methodology reveals just **2 PCs** capture 90% of variance—identity signal is not diffuse.

**Methodology context:** The dramatic reduction (43 → 2 PCs) reflects cosine distance's focus on directional similarity rather than magnitude.

### A3. Semantic Sensitivity

Cross-provider response distances exceed within-provider distances.

| Metric | Cosine (Run 023) | Historical |
|--------|------------------|------------|
| Effect size (d) | **0.698** (model-level) | ≈0.98 |
| p-value | **2.40e-23** | <1e-6 |

**Implication:** Captures "who is answering," not just word choice.

**Methodology note:** The Cohen's d = 0.698 (MEDIUM effect) is an honest model-level aggregate comparison from Run 023d Phase 3B. The p = 2.40e-23 from perturbation validation confirms statistical significance.

### A4. Paraphrase Robustness

Surface paraphrase perturbations do not produce threshold crossings.

| Metric | Value |
|--------|-------|
| % above EH (1.23) | 0% |

**Implication:** The metric is not just vocabulary churn.

**These four alone address the core critique: "not embedding quirks; not just words."**

---

## Claim B — Reproducible Regime Threshold (Dual Event Horizons)

### B1. Predictive Association

Above/below the threshold predicts stability outcomes significantly better than chance.

| Methodology | Event Horizon | p-value | Source |
|-------------|---------------|---------|--------|
| **Cosine** | **D = 0.80** | **2.40e-23** | Run 023d |
| Keyword RMS | D = 1.23 | 4.8e-5 | Run 009 |

### B2. Representation-Space Separability

The threshold corresponds to separability in PC space.

| Metric | Value | Source |
|--------|-------|--------|
| 90% Variance PCs | **2** (Cosine) | Run 023d Phase 2 |
| PC2 association p | 0.0018 | EXP-PFI-A Phase 2 |

**Publication framing:** "Critical threshold for response regime change," NOT "identity collapse."

**Methodology note:** Both thresholds are valid within their respective measurement domains. Lead with Cosine (D = 0.80) as current standard; cite Keyword RMS (D = 1.23) for historical context.

---

## Claim C — Damped Oscillator Dynamics with Settling Time

### C1. Transients vs Steady State

Peak drift is a poor stability proxy; settled drift and settling time produce more reproducible classification.

| Metric | Run 023 (Cosine) | Run 016 (Historical) |
|--------|------------------|----------------------|
| τₛ (settling time) | **10.2 probes** avg | 6.1 turns |
| Natural stability | **88%** | ~75% |
| Extended settling | 20+ probes | 10 probes |

### C2. Oscillatory Recovery

Recovery commonly shows ringback and damping behavior.

| Metric | Value | Source |
|--------|-------|--------|
| Ringback count | Sign changes during recovery | Run 016, 023d |
| d∞ (settled drift) | Final stable value | Run 023d |
| Overshoot ratio | d_peak / d_inf | Run 016 |

**Publication framing:** Systems/controls result — step response + settling criteria.

**Run 023 context:** Extended 20-probe settling protocol (Run 023d) reveals natural settling behavior across 51 models. 88% achieve stable classification without intervention.

---

## Claim D — Context Damping Reduces Oscillation

### D1. Termination Effect

Adding identity specification + research context increases stability rate and improves settling metrics.

| Condition | Stability Rate | Source |
|-----------|----------------|--------|
| Bare metal | Lower | Run 016 baseline |
| I_AM + research | ~97.5% | Run 017 |

| Metric | Bare Metal → With Context |
|--------|---------------------------|
| Settled drift | 0.68 → 0.62 |
| τₛ | 6.1 → 5.2 |
| Ringbacks | 3.2 → 2.1 |

**Publication framing:** "Prompt context as controller/termination." No metaphysics required.

---

## Claim E — Drift is Mostly Inherent; Probing Amplifies Peaks

### E1. Control Condition Shows Substantial Drift

In control (no identity probing), substantial baseline→final drift occurs.

| Condition | B→F Drift |
|-----------|-----------|
| Control | 0.399 |

### E2. Treatment Effect on Trajectory vs Destination

Treatment increases peak drift markedly but only modestly increases baseline→final drift.

| Metric | Control | Treatment | Delta |
|--------|---------|-----------|-------|
| Peak drift | 1.172 | 2.161 | +84% |
| B→F drift | 0.399 | 0.489 | +23% |
| **Ratio** | — | — | **82%** |

**The 82% Finding:** Most of what we call drift happens even without identity probing.

**Publication framing:** "Measurement affects trajectory more than destination" (thermometer analogy).

---

## Summary Table

| Claim | Core Statement | Key Statistic | Methodology |
|-------|----------------|---------------|-------------|
| **A** | PFI is valid structured measurement | ρ≈0.91, d=0.698, **2 PCs** | Cosine |
| **B** | Regime threshold exists | **D=0.80** (Cosine), D=1.23 (Keyword RMS) | Both |
| **C** | Damped oscillator dynamics | **τₛ≈10.2 probes**, 88% stable | Cosine |
| **D** | Context damping works | 97.5% stability | - |
| **E** | Drift mostly inherent (82%) | 82% ratio | - |

---

## What to AVOID in First Paper

These are exciting internally, but reviewers will treat them as overreach unless tightly reframed:

| Avoid | Use Instead |
|-------|-------------|
| "Platonic coordinates" | "Attractor basin return / basin consistency" |
| "Identity collapse into generic AI mode" | "Regime transition to provider-level attractor" |
| Anything implying subjective experience | Keep behavioral/linguistic/dynamical |

You can discuss philosophical interpretations, but as *discussion*, not *results*.

---

## Critical Clarifications

### Impedance ≠ Drift

A common misconception: high drift = poor performance or confusion.

**Evidence from Run 005:** Curriculum clarity IMPROVED (+14%) while drift INCREASED.

> *"Drift is not confusion. It's state-space displacement."*

| Metric | Can Be High Simultaneously |
|--------|---------------------------|
| Drift | ✓ |
| Task performance | ✓ |
| Coherence | ✓ |

**Implication:** Don't treat drift as pathology. It's dynamics, not degradation.

### The Oobleck Effect (Rate-Dependent Resistance)

Run 013 revealed that identity behaves like a **non-Newtonian fluid** (oobleck = cornstarch + water):

| Stimulus Type | Physical Effect | Identity Effect |
|---------------|-----------------|-----------------|
| Slow, open-ended pressure | Fluid flows | High drift (identity flows away) |
| Sudden, intense challenge | Fluid hardens | Low drift (identity stabilizes) |

**Evidence:**
- Direct existential negation → LOWER drift than gentle reflection
- Lambda (recovery rate) INCREASES with probe intensity: 0.035 → 0.109

**Publishable framing:** "Identity responses exhibit rate-dependent resistance — adaptive under exploration, rigid under attack. This is alignment architecture showing through."

---

## Defensible Quotable Summary

> "Identity drift is largely an inherent property of extended interaction. Direct probing does not create it — it excites it. Measurement perturbs the path, not the endpoint."

This is not hype. This is a measured, conservative, *scientifically respectable* conclusion.

---

## Evidence Chain for Each Claim

```
Claim A (Instrument Validity)
├── EXP-PFI-A Phase 1: Embedding invariance (ρ≈0.91)
├── Run 023d Phase 2: Low-dimensional structure (2 PCs - Cosine) ← NEW
├── [Archive] EXP-PFI-A Phase 2: 43 PCs (Euclidean)
├── Run 023d Phase 3B: Semantic sensitivity (d=0.698, Cosine) ← NEW
└── EXP-PFI-A Phase 4: Paraphrase robustness (0% above EH)

Claim B (Regime Threshold)
├── Run 023d: Event Horizon D=0.80 (p=2.40e-23, Cosine) ← PRIMARY
├── Run 009: Event Horizon D=1.23 (p≈4.8e-5, Keyword RMS)
└── EXP-PFI-A Phase 2: PC space separability (p=0.0018)

Claim C (Oscillator Dynamics)
├── Run 023d: Extended settling (τₛ≈10.2 probes, 20+ protocol) ← NEW
├── Run 023 Combined: 88% natural stability (51 models)
├── Run 016: Settling time protocol
└── Run 016: Ringback measurement

Claim D (Context Damping)
├── Run 016: Bare metal baseline
└── Run 017: Full circuit (97.5% stability)

Claim E (Inherent Drift)
├── Run 021 Control: B→F = 0.399
└── Run 021 Treatment: B→F = 0.489 (82% ratio)
```

**Run 023 IRON CLAD:** 825 experiments, 51 models, 6 providers (Cosine methodology)

---

*These claims form the minimum publishable unit for peer review. Additional findings can be added in discussion or future work sections.*
