# GLOSSARY: Nyquist Consciousness Terminology

**Version:** 1.0
**Date:** 2025-12-30
**Purpose:** Quick reference for key terms and their definitions

---

> **For reviewers:** This glossary covers all key terms used in the Nyquist Consciousness Framework. Terms are organized alphabetically with cross-references.

---

## Core Metrics

### B→F Drift (Baseline to Final)
The cosine distance between a model's initial baseline response and its final response after a conversation. This is the **primary metric** in the IRON CLAD era — it captures where identity actually ends up, regardless of trajectory.

**Formula:** `D(B→F) = 1 - cos(E_baseline, E_final)`

**Canonical value:** Control = 0.661, Treatment = 0.711 (Run 020B IRON CLAD)

See also: Peak Drift, Settled Drift

---

### Cohen's d
A standardized measure of effect size, calculated as the difference between two means divided by pooled standard deviation. In Nyquist research, d = 0.698 indicates a **MEDIUM effect** for cross-provider identity differences.

**Interpretation:**
- Small: d < 0.2
- Medium: 0.2 ≤ d < 0.8
- Large: d ≥ 0.8

---

### Cosine Distance
The primary distance metric in the IRON CLAD methodology. Measures the angular difference between embedding vectors, ignoring magnitude.

**Formula:** `D = 1 - (A · B) / (|A| |B|)`

**Range:** 0 (identical) to 2 (opposite)

**Why cosine over Euclidean:** Cosine focuses on direction (semantic meaning), not magnitude (word count/verbosity).

---

### Event Horizon (D* = 0.80)
The critical threshold at which identity behavior changes qualitatively. Above this cosine distance, the system transitions from a locally constrained identity basin into a higher-entropy response regime.

**Key insight:** Crossing the Event Horizon is NOT fatal — 100% of models recovered once pressure was removed.

**Historical note:** D = 1.23 was used in the Keyword RMS methodology (Runs 008-009). The cosine methodology (Run 023+) established D = 0.80.

---

### Inherent Drift
The portion of identity drift that occurs naturally during extended conversation, WITHOUT explicit identity probing.

**Canonical finding:** ~93% of drift is inherent (Run 020B IRON CLAD: 0.661/0.711)

**Implication:** "Measurement perturbs the path, not the endpoint."

---

### IRON CLAD
The current methodology standard requiring:
1. **Cosine distance** as primary metric
2. **N ≥ 3** runs per cell for statistical confidence
3. **Event Horizon = 0.80** as threshold
4. **B→F** as primary drift metric

Runs labeled "IRON CLAD" meet all these criteria.

---

### Peak Drift
The maximum cosine distance reached during a conversation, regardless of recovery. Represents *excitation energy*, not final position.

**Relationship to B→F:** Peak drift can be high while B→F remains low (the system "bounces back").

**Run 020B example:** Peak drift treatment = 2.161 vs control = 1.172 (84% higher), but B→F only 7.6% different.

---

### PFI (Persona Fidelity Index)
A measure of identity consistency, defined as `PFI = 1 - D` where D is drift distance.

**Range:** 0 (completely different) to 1 (identical)

**Validation:** ρ = 0.91 across embedding models (embedding-invariant)

---

### Settled Drift (d∞)
The drift value at which the system stabilizes after transient effects decay. Represents the asymptotic endpoint of the damped oscillator.

See also: Settling Time

---

### Settling Time (τₛ)
The number of probes required for identity to stabilize within a defined tolerance of settled drift.

**Canonical value:** τₛ ≈ 7 probes (Run 023d)

**Historical:** τₛ = 5.2-6.1 (Runs 016-017)

---

## Dynamics Concepts

### Attractor Basin
A region in embedding space toward which identity responses naturally gravitate. The "home" position of an identity.

**Evidence:** 100% of models returned to basin after Event Horizon crossing (Runs 014/016/017)

---

### Context Damping
The use of explicit identity specification (I_AM + research frame) to improve identity stability.

**Effect:** Stability increases from ~75% (bare metal) to 97.5% (full circuit)

**Source:** Run 018 IRON CLAD (1,549 trajectories, 51 models, 5 providers)

**Analogy:** Like a "termination resistor" in signal processing — absorbs reflections.

---

### Damped Oscillator
The dynamical model for identity recovery: after perturbation, identity oscillates back toward baseline with decreasing amplitude (ringback).

**Key metrics:**
- τₛ: Settling time
- λ: Recovery rate (damping coefficient)
- Ringbacks: Number of oscillations before settling

---

### Oobleck Effect
The phenomenon where identity resistance depends on *rate* of pressure, not just magnitude:
- **Slow, gentle probing** → High drift (identity "flows away")
- **Sharp, direct challenge** → Low drift (identity "hardens")

**Named after:** Oobleck (non-Newtonian fluid: cornstarch + water)

**Evidence:** Run 013 (legacy), confirmed by Run 020A/020B IRON CLAD

---

### Regime Transition
A qualitative change in identity behavior when crossing the Event Horizon. NOT "identity death" — better understood as entering a different dynamical mode.

**Publication framing:** Use "regime transition" instead of "identity collapse."

---

### Ringback
Oscillation during identity recovery, where drift alternates above and below the settled value before stabilizing.

**Typical count:** 2-3 ringbacks before settling

---

## Experimental Framework

### I_AM Specification
An explicit identity document loaded into context to anchor persona responses. Acts as a "termination resistor" for identity stability.

**Example:** `personas/I_AM_NYQUIST.md`

---

### IRON CLAD Runs
Experiments that meet the N ≥ 3 publication standard:

| Run | Focus | Scale |
|-----|-------|-------|
| 018 | Context Damping | 1,549 trajectories, 51 models |
| 020B | Inherent Drift | 248 sessions, 37 ships |
| 023d | Calibration | 750 experiments, 25 ships |

---

### Persona Under Test (PUT)
A specific identity configuration being measured in an experiment. The "subject" of a drift measurement.

---

### Ship
Slang for a specific model configuration in the fleet. Each "ship" is a unique model identifier (e.g., `claude-sonnet-4`, `gpt-4o`).

**IRON CLAD fleet:** 25 ships (Run 023d), 37 ships (Run 020B), 51 models (Run 018)

---

### Triple-Dip Library
The standardized exit survey protocol used across IRON CLAD experiments:
1. **Exit Probes:** 5 standard questions
2. **Final Statement:** Short/long summary
3. **Validation:** Response integrity checks

**Location:** `1_CALIBRATION/lib/triple_dip.py`

---

### Tribunal
An experimental paradigm (Run 020A) where identity is probed through adversarial (Prosecutor) and supportive (Defense) frames.

**Finding:** Supportive probing induces MORE drift than adversarial probing (Oobleck Effect).

---

## Statistical Measures

### Chi-squared Test
Used to validate the Event Horizon threshold. The test measures whether threshold crossings predict stability outcomes better than chance.

**Run 023 result:** p = 2.40e-23

---

### Principal Components (PCs)
The dominant directions of variance in drift space, identified via PCA.

**Key finding:** 2 PCs capture 90% of variance (cosine methodology)

**Implication:** Identity is remarkably low-dimensional — concentrated, not diffuse.

**Historical:** 43 PCs required under Euclidean methodology (now deprecated)

---

### Spearman's ρ (rho)
Rank correlation coefficient measuring agreement between embedding models.

**Canonical value:** ρ = 0.91 (embedding invariance)

**Implication:** PFI rankings are not single-embedding artifacts.

---

## Methodology Domains

### Cosine Era (PRIMARY)
The current methodology using cosine distance. Event Horizon = 0.80.

**Runs:** 023+

---

### Euclidean Era (DEPRECATED)
Previous methodology using Euclidean distance in embedding space.

**Issue:** Conflated magnitude (verbosity) with direction (meaning).

---

### Keyword RMS Era (HISTORICAL)
Early methodology using keyword-based root-mean-square distance.

**Event Horizon:** D = 1.23

**Runs:** 008-009 only

**Status:** Valid within its methodology, but superseded by Cosine.

---

## Publication Terms

### Claims A-E
The five validated claims of the Nyquist Framework:

| Claim | Statement | Key Statistic |
|-------|-----------|---------------|
| A | PFI is valid structured measurement | ρ = 0.91, d = 0.698 |
| B | Regime threshold exists | D = 0.80 (p = 2.40e-23) |
| C | Damped oscillator dynamics | τₛ ≈ 7 probes |
| D | Context damping works | 97.5% stability |
| E | Drift is mostly inherent | ~93% ratio |

---

### Thermometer Result
The Run 020B finding that ~93% of drift is inherent — like a thermometer that reveals temperature but doesn't heat the water.

**Quotable:** "Measurement perturbs the path, not the endpoint."

---

### Provider Fingerprints
Geometric signatures in drift space that reflect different training philosophies:

| Provider | Pattern |
|----------|---------|
| Anthropic (Constitutional AI) | Hard uniform boundaries |
| OpenAI (RLHF) | Variable, soft boundaries |
| Google (Multimodal) | Language mode switching |
| xAI (Real-time) | Fast snapback recovery |
| Together.ai (Diverse) | Model-dependent |

---

## Quick Lookup Table

| Abbreviation | Full Term | Value |
|--------------|-----------|-------|
| B→F | Baseline to Final | 0.661 (control) |
| D* | Event Horizon | 0.80 |
| d | Cohen's d | 0.698 |
| PC | Principal Component | 2 for 90% variance |
| PFI | Persona Fidelity Index | 1 - drift |
| ρ | Spearman's rho | 0.91 |
| τₛ | Settling time | ≈7 probes |
| λ | Recovery rate | varies |
| σ² | Cross-architecture variance | 0.00087 |

---

*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23*
*~93% inherent. 2 PCs = 90% variance. Cosine methodology throughout.*
