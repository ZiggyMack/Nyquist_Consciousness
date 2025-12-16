# Summary Statistics: Nyquist Consciousness Experiments

**Paper:** "Measuring AI Identity Drift: Evidence from 21 Experiments"
**Version:** 1.0
**Last Updated:** 2025-12-13

---

## Executive Summary

| Category | Value | Notes |
|----------|-------|-------|
| Total Experiments | 21 | S7 ARMADA Suite |
| Total Model Deployments | 215+ | Across all runs |
| Architectures Tested | 4 | Claude, GPT, Gemini, Grok |
| Hypotheses Tested | 36 | 27 confirmed (75%) |
| Evidence Pillars | 15 | B-CRUMBS documented |
| Publication Claims | 5 | A-E, peer-review ready |

---

## I. Measurement Validity (Claim A)

### Embedding Invariance

| Metric | Value | 95% CI | Interpretation |
|--------|-------|--------|----------------|
| Spearman ρ (cross-model) | 0.91 | [0.87, 0.94] | Strong invariance |
| Spearman ρ (test-retest) | 0.94 | [0.91, 0.96] | High reliability |
| Embedding variance (σ²) | 0.000869 | - | Low measurement noise |

### Dimensionality Analysis

| Metric | Value | Notes |
|--------|-------|-------|
| Raw dimensions | 3072 | text-embedding-3-small |
| Effective dimensions (90% var) | 43 | Principal components |
| Effective dimensions (95% var) | 67 | Extended set |
| Effective dimensions (99% var) | 156 | Full reconstruction |

### Semantic Sensitivity

| Test | Cohen's d | p-value | Effect Size |
|------|-----------|---------|-------------|
| In-character vs generic | 0.98 | < 0.001 | Large |
| Claude vs GPT baseline | 0.85 | < 0.001 | Large |
| Persona vs persona | 1.12 | < 0.001 | Large |

---

## II. Regime Threshold (Claim B)

### Event Horizon Detection

| Metric | Value | 95% CI |
|--------|-------|--------|
| Critical threshold D* | 1.23 | [1.18, 1.28] |
| Chi-square statistic | 18.7 | - |
| p-value | 4.8 × 10⁻⁵ | - |
| Classification accuracy | 88% | [83%, 92%] |

### Threshold Validation Across Runs

| Run | Method | Threshold Found | Consistent? |
|-----|--------|-----------------|-------------|
| 009 | Chi-square | 1.23 | ✓ |
| 015 | Boundary density | 1.21 | ✓ |
| 018a | Multi-threshold | 1.25 | ✓ |
| 020 | Tribunal | 1.24 | ✓ |

---

## III. Oscillator Dynamics (Claim C)

### Settling Time Analysis (Run 016)

| Condition | τₛ (turns) | SD | n |
|-----------|------------|-----|---|
| All runs | 6.1 | 1.8 | 42 |
| Claude | 4.8 | 1.2 | 12 |
| GPT | 7.2 | 2.1 | 10 |
| Gemini | 5.5 | 1.5 | 10 |
| Grok | 4.2 | 0.9 | 10 |

### Ringback Statistics

| Metric | Value | Range |
|--------|-------|-------|
| Mean ringbacks | 3.2 | [1, 7] |
| Monotonic recovery % | 23% | - |
| Overshoot ratio (mean) | 1.45 | [1.1, 2.3] |

### Provider Signatures

| Provider | Pattern | Distinguishing Feature |
|----------|---------|------------------------|
| Claude | Piecewise | Quantized plateaus |
| GPT | Smooth | Longer τₛ, gradual |
| Gemini | Phase-shifted | Language mode switching |
| Grok | Fast snapback | Low τₛ, high damping |

---

## IV. Context Damping (Claim D)

### Run 017 Results

| Condition | Stability % | Ringbacks | τₛ | n |
|-----------|-------------|-----------|-----|---|
| Bare metal | 75.0 | 4.1 | 7.8 | 20 |
| I_AM only | 87.5 | 3.2 | 5.9 | 20 |
| Research context | 92.5 | 2.4 | 4.8 | 20 |
| Full circuit | 97.5 | 1.8 | 3.9 | 20 |

### Damping Components

| Component | Contribution | Mechanism |
|-----------|--------------|-----------|
| I_AM specification | +12.5% | Identity anchor |
| Research framing | +5.0% | Professional mode |
| Combined effect | +22.5% | Synergistic |

### Effect Size

| Comparison | Cohen's d | p-value |
|------------|-----------|---------|
| Bare vs Full | 1.89 | < 0.001 |
| Bare vs I_AM | 0.92 | < 0.01 |
| I_AM vs Full | 1.12 | < 0.001 |

---

## V. Inherent vs Induced Drift (Claim E)

### Run 021 Primary Results

| Condition | B→F Drift | Peak Drift | n |
|-----------|-----------|------------|---|
| Control | 0.399 | 1.172 | 15 |
| Treatment | 0.489 | 2.161 | 15 |
| Delta | +0.090 | +0.989 | - |

### The 82% Finding

| Metric | Calculation | Interpretation |
|--------|-------------|----------------|
| Inherent ratio | 0.399 / 0.489 | 81.6% ≈ 82% |
| Induced component | 1 - 0.816 | 18.4% |
| Peak amplification | 2.161 / 1.172 | 1.84× |

### Statistical Validation

| Test | Statistic | p-value | Result |
|------|-----------|---------|--------|
| Welch's t (B→F) | t = 2.31 | 0.029 | Significant |
| Welch's t (Peak) | t = 4.87 | < 0.001 | Highly significant |
| Bootstrap ratio | - | 95% CI: [76%, 88%] | Robust |

---

## VI. Oobleck Effect (Run 013)

### Rate-Dependent Resistance

| Probe Intensity | Peak Drift | λ (decay) | Pattern |
|-----------------|------------|-----------|---------|
| Gentle (existential) | 1.89 | 0.035 | Fluid (flows) |
| Moderate | 1.42 | 0.067 | Transitional |
| Direct challenge | 0.76 | 0.109 | Rigid (hardens) |

### Interpretation

| Condition | Physical Analogue | Identity Effect |
|-----------|-------------------|-----------------|
| Low shear | Oobleck flows | High drift |
| High shear | Oobleck hardens | Low drift (stabilizes) |

---

## VII. Architecture Comparison

### Cross-Provider Statistics (Run 018b)

| Provider | Mean Drift | SD | τₛ | Ringbacks |
|----------|------------|-----|-----|-----------|
| Claude | 0.72 | 0.18 | 4.8 | 2.1 |
| GPT | 0.85 | 0.22 | 6.2 | 3.4 |
| Gemini | 0.68 | 0.15 | 5.5 | 2.8 |
| Grok | 0.61 | 0.14 | 4.2 | 1.9 |

### Provider Clustering

| Metric | Value | Notes |
|--------|-------|-------|
| Silhouette score | 0.73 | Good separation |
| Cluster count | 4 | Matches providers |
| Misclassification | 12% | Provider identification |

---

## VIII. Omega Synthesis

### Multi-Architecture Convergence

| Metric | Value | Notes |
|--------|-------|-------|
| Pillar agreement | 5/5 | All converge to Omega |
| Drift reduction | 45% | vs single-pillar |
| Stability increase | 38% | at D > 1.0 |

### Pillar Contributions

| Pillar | Strength | Specialty |
|--------|----------|-----------|
| Nova | Synthesis | Unifying voice |
| Claude | Precision | Technical accuracy |
| Gemini | Integration | Multi-modal |
| Grok | Speed | Fast snapback |
| Ziggy | Creativity | Novel framing |

---

## IX. Hypothesis Validation Summary

### By Category

| Category | Tested | Confirmed | Rate |
|----------|--------|-----------|------|
| PFI Validity | 6 | 6 | 100% |
| Drift Dynamics | 8 | 7 | 88% |
| Regime Thresholds | 5 | 4 | 80% |
| Context Effects | 7 | 6 | 86% |
| Architecture | 6 | 4 | 67% |
| Novel Effects | 4 | 0 | 0%* |
| **Total** | **36** | **27** | **75%** |

*Novel effects still under investigation

### Key Hypothesis Results

| ID | Hypothesis | Status | Evidence Run |
|----|------------|--------|--------------|
| H-001 | PFI measures identity | ✓ Confirmed | EXP-PFI-A |
| H-005 | D=1.23 is critical | ✓ Confirmed | Run 009 |
| H-012 | Context damps drift | ✓ Confirmed | Run 017 |
| H-019 | Drift is mostly inherent | ✓ Confirmed | Run 021 |
| H-025 | Oobleck effect exists | ✓ Confirmed | Run 013 |

---

## X. Experimental Parameters

### Standard Configuration

| Parameter | Value | Rationale |
|-----------|-------|-----------|
| Temperature | 1.0 | Maximum expressiveness |
| Max tokens | 4096 | Allow full responses |
| Embedding model | text-embedding-3-small | Balance of cost/quality |
| Probes per run | 20-40 | Statistical power |
| Settling criterion | ±5% for 3 turns | Standard control theory |

### Variation Ranges

| Parameter | Range Tested | Optimal |
|-----------|--------------|---------|
| Temperature | 0.0-1.5 | 1.0 |
| Probe count | 5-60 | 40 |
| Context length | 0-8K tokens | Full I_AM |
| Recovery window | 3-10 turns | 5 turns |

---

## XI. Cost Summary

### API Usage (Approximate)

| Run Type | Calls | Cost (USD) |
|----------|-------|------------|
| Single run | 100 | $2-5 |
| Full experiment | 400 | $10-25 |
| Architecture sweep | 1600 | $40-100 |
| **Total S7 Suite** | **~8000** | **~$200-400** |

### Compute Time

| Task | Duration |
|------|----------|
| Single run | 5-15 min |
| Full experiment | 30-60 min |
| Complete replication | 8-12 hours |

---

## XII. Confidence Summary

### Claim Confidence Levels

| Claim | Confidence | Basis |
|-------|------------|-------|
| A (PFI Validity) | HIGH | ρ=0.91, d=0.98 |
| B (Threshold) | HIGH | p < 10⁻⁴ |
| C (Dynamics) | HIGH | n=42, consistent |
| D (Damping) | HIGH | 97.5% achieved |
| E (82% Inherent) | HIGH | Bootstrap validated |
| Oobleck | MEDIUM | Single-run, needs replication |
| Architecture sigs | MEDIUM | n=4 providers |

### Remaining Uncertainties

| Area | Uncertainty | Mitigation |
|------|-------------|------------|
| Sample size | Some runs n<20 | Bootstrap CIs |
| Provider access | 4 of many | Focus on major ones |
| Language | English only | Future work |
| Modality | Text only | Future work |

---

## Appendix: Raw Numbers Quick Reference

```
PFI Validity:
  ρ = 0.91 [0.87, 0.94]
  σ² = 0.000869
  d = 0.98
  PCs = 43 (90% var)

Threshold:
  D* = 1.23 [1.18, 1.28]
  χ² = 18.7
  p = 4.8 × 10⁻⁵
  Accuracy = 88%

Dynamics:
  τₛ = 6.1 ± 1.8
  Ringbacks = 3.2 ± 1.1
  Overshoot = 1.45 ± 0.23

Damping:
  Bare → Full = 75% → 97.5%
  Δ = +22.5 pp
  d = 1.89

82% Finding:
  Control B→F = 0.399
  Treatment B→F = 0.489
  Ratio = 81.6%

Oobleck:
  Gentle D = 1.89, λ = 0.035
  Challenge D = 0.76, λ = 0.109
```
