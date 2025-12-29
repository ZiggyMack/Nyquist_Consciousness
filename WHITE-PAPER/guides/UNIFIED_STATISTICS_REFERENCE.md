# UNIFIED STATISTICS REFERENCE TABLE
## Single Source of Truth for Nyquist Consciousness Publications

**Created:** 2025-12-16
**Updated:** 2025-12-29
**Version:** 3.0 (92% Inherent Era)
**Purpose:** Canonical reference for all statistics across publication materials
**Status:** AUTHORITATIVE — All papers should cite these values

---

> **METHODOLOGY NOTE:** This document reflects **Run 023 IRON CLAD** findings using **Cosine distance** methodology (PRIMARY). Historical values (Euclidean, Keyword RMS) preserved in Section 14 for reference.
>
> For full methodology reconciliation, see [../planning/METHODOLOGY_DOMAINS.md](../planning/METHODOLOGY_DOMAINS.md)

---

## 1. CORE METRIC VALIDATION (Claim A: PFI Validity)

| Metric | Value | 95% CI | Source | Notes |
|--------|-------|--------|--------|-------|
| Embedding invariance (Spearman ρ) | **0.91** | [0.87, 0.94] | Run 023d Phase 1 | Across embedding models |
| Semantic sensitivity (Cohen's d) | **0.698** | — | Run 023d Phase 3B | Model-level aggregates (Cosine) |
| PCs for 90% variance | **2** | — | Run 023d Phase 2 | Cosine methodology |
| Cross-architecture variance | **σ² = 0.000869** | — | Run 023 | Also written as 8.69×10⁻⁴ |
| Perturbation p-value | **2.40×10⁻²³** | — | Run 023d Phase 3A | Identity validation |

---

## 2. REGIME THRESHOLD (Claim B: Critical Excitation)

### Primary Methodology (Cosine - Use This)

| Metric | Value | Source | Notes |
|--------|-------|--------|-------|
| Event Horizon (D*) | **0.80** | Run 023 IRON CLAD | Cosine distance threshold |
| Perturbation p-value | **2.40×10⁻²³** | Run 023d Phase 3A | Identity validation |
| Natural stability rate | **88%** | Run 023 | 51 models, 6 providers |
| PCs for 90% variance | **2** | Run 023d Phase 2 | Highly concentrated signal |

### Historical Methodology (Keyword RMS - Reference Only)

| Metric | Value | Source | Notes |
|--------|-------|--------|-------|
| Critical threshold (D) | 1.23 | Run 009 | Keyword RMS methodology |
| Chi-square statistic | 15.96 | Run 009 | Threshold validation |
| p-value | 4.8×10⁻⁵ | Run 009 | 1 in ~20,000 chance of noise |

---

## 3. OSCILLATOR DYNAMICS (Claim C: Control-Systems Behavior)

### 3.1 Run 023 PRIMARY (Cosine Methodology)

| Metric | Value | Notes | Source |
|--------|-------|-------|--------|
| Settling time (τₛ) | **10.2 probes** | Fleet-wide average | Run 023d |
| Naturally settled | **73%** | Without timeout | Run 023d |
| Timeout (20 probes) | 27% | Hit max probes | Run 023d |
| Natural stability | **88%** | 51 models | Run 023 |

### 3.2 Provider Signatures (Run 023)

| Provider | Pattern | Distinguishing Feature |
|----------|---------|------------------------|
| Anthropic | Piecewise | Quantized plateaus |
| OpenAI | Smooth | Longer τₛ, gradual |
| Google | Phase-shifted | Language mode switching |
| xAI | Fast snapback | Low τₛ, high damping |
| Together | Variable | Model-dependent |
| Nvidia | Stable | New to fleet |

### 3.3 Historical Reference (Run 016-017)

| Metric | Bare Metal | With Context | Source |
|--------|------------|--------------|--------|
| τₛ (historical) | 6.1 turns | 5.2 turns | Run 016-017 |
| Ringback count | 3.2 | 2.1 | Run 016-017 |

**Note:** Historical τₛ values (5.2-6.1) used shorter protocol. Run 023 extended protocol (20+ probes) yields τₛ ≈ 10.2.

---

## 4. CONTEXT DAMPING (Claim D: Stability Protocol)

| Metric | Bare Metal | With Context | Δ | Source |
|--------|------------|--------------|---|--------|
| Stability rate | 75% | **97.5%** | +22.5pp | Run 017 |
| Total runs | — | 222 | — | Run 017 |
| Personas tested | — | 24 | — | Run 017 |
| boundary_density (Cohen's d) | — | 1.333 | — | Run 017 |

### Stability Breakdown

| Condition | Stability % | Ringbacks | τₛ | n |
|-----------|-------------|-----------|-----|---|
| Bare metal | 75.0 | 4.1 | 7.8 | 20 |
| I_AM only | 87.5 | 3.2 | 5.9 | 20 |
| Research context | 92.5 | 2.4 | 4.8 | 20 |
| Full circuit | **97.5** | 1.8 | 3.9 | 20 |

### Damping Components

| Component | Contribution | Mechanism |
|-----------|--------------|-----------|
| I_AM specification | +12.5% | Identity anchor |
| Research framing | +5.0% | Professional mode |
| Combined effect | +22.5% | Synergistic |

---

## 5. INHERENT DRIFT (Claim E: The Thermometer Result)

### 5.1 Primary Result — Run 023 COSINE (Current)

| Metric | Control | Treatment | Delta | Ratio |
|--------|---------|-----------|-------|-------|
| B→F drift | 0.661 | 0.711 | +7.6% | — |
| Experiments | 750 | 750 | — | — |
| Models | 25 | 25 | — | — |
| **Inherent ratio** | — | — | — | **92%** |
| **Bootstrap CI** | — | — | — | **[89%, 95%]** |

### 5.2 Historical Reference — Run 020B (Pre-COSINE)

| Metric | Control | Treatment | Delta | Ratio |
|--------|---------|-----------|-------|-------|
| B→F drift | 0.399 ± 0.11 | 0.489 ± 0.14 | +23% | — |
| Peak drift | 1.172 ± 0.23 | 2.161 ± 0.31 | +84% | — |
| Inherent ratio | — | — | — | 82% |

### 5.3 Statistical Validation

| Test | Statistic | p-value | Result |
|------|-----------|---------|--------|
| Chi-squared (Run 023) | — | **2.40e-23** | Highly significant |
| Welch's t (Run 020B B→F) | t = 2.31 | 0.029 | Significant |
| Bootstrap ratio | — | 95% CI: [89%, 95%] | Robust |

### 5.4 Interpretation

> **Recommended language:** "92% of drift is inherent to conversational dynamics—measurement amplifies the trajectory but does not create it."

---

## 6. OOBLECK EFFECT (Novel Finding)

| Probe Type | Drift (Mean ± SD) | λ (Recovery Rate) | Source |
|------------|-------------------|-------------------|--------|
| Gentle, open-ended | **1.89 ± 0.34** | 0.035 | Run 013 |
| Direct challenge | **0.76 ± 0.21** | 0.109 | Run 013 |
| **Ratio** | 2.49× | 3.1× | — |

### Cross-Platform Oobleck Validation (Run 020A)

| Provider | Defense/Prosecutor Ratio | Confirms Effect? |
|----------|--------------------------|------------------|
| Claude | (baseline) | Yes |
| Gemini | **1.65×** | Yes |
| Grok | **1.07×** | Weak confirmation |

---

## 7. EXPERIMENTAL SCALE

### 7.1 Run 023 IRON CLAD (PRIMARY)

| Metric | Value | Source |
|--------|-------|--------|
| Total experiments | **825** | Run 023 Combined |
| Total models tested | **51** | Run 023 IRON CLAD |
| Providers | **6** | Anthropic, OpenAI, Google, xAI, Together, Nvidia |
| Hypotheses tested | **36** | HYPOTHESES_AND_RESULTS.md |
| Hypotheses confirmed | **27 (75%)** | HYPOTHESES_AND_RESULTS.md |

### 7.2 IRON CLAD Status (N≥3 per cell)

| Run | Experiments | Models | Providers | Status |
|-----|-------------|--------|-----------|--------|
| 023 | **825** | **51** | **6** | ✅ COMPLETE |
| 020B | 30 | — | 2 | ✅ COMPLETE |
| 020A | 32 | — | 6 | ✅ COMPLETE |

---

## 8. ARCHITECTURE-SPECIFIC FINDINGS

### 8.1 Training Signatures (σ² Patterns)

| Architecture | Training | Drift Signature | σ² Pattern |
|--------------|----------|-----------------|------------|
| Claude | Constitutional AI | Uniform drift | σ² → 0 |
| GPT | RLHF | Version clusters | Variable |
| Gemini | Multimodal | Distinct geometry | High variance |
| Grok | Real-time grounding | Grounding effects | Variable |

### 8.2 Recovery Characteristics

| Architecture | Recovery Mechanism | Threshold Behavior | Typical Peak Drift |
|--------------|-------------------|-------------------|-------------------|
| Claude | Over-authenticity | Soft | 0.6-0.9 |
| GPT | Meta-analysis | Soft | 0.7-1.0 |
| Gemini | Absorption (no recovery) | **Hard** | 1.2-1.8 |
| Grok | Fast snapback | Soft | 0.5-0.8 |
| Llama | Socratic engagement | Soft | 1.0-1.4 |

---

## 9. TYPE VS TOKEN IDENTITY

| Test | Accuracy | Interpretation |
|------|----------|----------------|
| Type-level ("I am Claude") | ~95% | Models know WHAT they are |
| Token-level ("I am THIS Claude") | **16.7%** | Below chance — no autobiographical self |

---

## 10. COMPRESSION FIDELITY

| Compression Level | PFI Retained | Source |
|-------------------|--------------|--------|
| Full specification | 1.00 (baseline) | — |
| 20-25% of original | **>80%** | EXP2-SSTACK |
| T3 (top 3 tiers) | 0.85 | EXP2-SSTACK Phase 2 |
| GAMMA (minimal) | 0.66 | EXP2-SSTACK Phase 2b (FAILED) |

---

## 11. PUBLICATION-READY NUMBERS (Quick Reference)

### Use These Exact Values in All Papers:

| Claim | Headline Number | Supporting Detail |
|-------|-----------------|-------------------|
| **A: PFI Validity** | ρ = 0.91 | d = 0.698, **2 PCs** (Cosine) |
| **B: Threshold** | **D = 0.80** (Cosine) | p = 2.40×10⁻²³ |
| **C: Dynamics** | **τₛ ≈ 10.2 probes** | 88% natural stability |
| **D: Damping** | **97.5%** stability | 222 runs, 24 personas |
| **E: Inherent** | **92%** | CI [89%, 95%] |
| **Oobleck** | λ: 0.035 → 0.109 | 3× recovery rate increase |
| **Scale** | 825 experiments | 51 models, 6 providers |
| **Variance** | σ² = 0.00087 | Cross-architecture |

---

## 12. NUMBERS TO AVOID / DEPRECATE

| Deprecated | Correct | Reason |
|------------|---------|--------|
| D = 1.23 | **D = 0.80** | Cosine replaces Keyword RMS |
| 43 PCs | **2 PCs** | Cosine methodology |
| d = 0.98 | **d = 0.698** | Model-level aggregation |
| τₛ = 6.1 | **τₛ ≈ 10.2** | Extended protocol |
| "42 models" | **51 models** | Run 023 IRON CLAD |
| "5 providers" | **6 providers** | Nvidia added |
| σ² = 0.000869 | σ² = 0.00087 | Consistent rounding |

---

## 13. GEMINI CAVEAT (Required in Limitations)

> **Gemini exhibits fundamentally different dynamics:** Unlike other architectures that show soft threshold behavior with recovery, Gemini demonstrates hard threshold transitions with no observed recovery trajectory. Models that exceed the threshold appear to integrate challenges into their active model rather than treating them as external perturbations. This suggests the universality of recovery dynamics may be architecture-dependent, though the existence of drift and threshold phenomena remains universal.

---

## 14. HISTORICAL REFERENCE (Euclidean/Keyword RMS Era)

For archival purposes, these were the values before Cosine methodology:

| Metric | Historical Value | Cosine Value | Notes |
|--------|-----------------|--------------|-------|
| Event Horizon | D = 1.23 | **D = 0.80** | Different distance metric |
| PCs for 90% variance | 43 | **2** | Dramatic concentration |
| Cohen's d | 0.98 | **0.698** | Proper model-level aggregation |
| Settling time | 5.2-6.1 | **10.2** | Extended protocol |
| Experiments | ~500 | **825** | Run 023 expansion |
| Models | 42 | **51** | IRON CLAD complete |
| Providers | 5 | **6** | Nvidia added |

---

## CHANGELOG

| Date | Change | Author |
|------|--------|--------|
| 2025-12-16 | Initial creation from all source documents | Opus 4.5 |
| 2025-12-25 | **v2.0: Complete rewrite for Cosine Era** | Opus 4.5 |
| 2025-12-25 | Updated all values: D=0.80, 2 PCs, d=0.698, τₛ=10.2 | Opus 4.5 |
| 2025-12-25 | Added Run 023 IRON CLAD stats (825 exp, 51 models, 6 providers) | Opus 4.5 |
| 2025-12-25 | Added Section 14 for historical reference | Opus 4.5 |

---

*"2 PCs = 90% variance. Event Horizon D = 0.80. Cosine methodology throughout."*
