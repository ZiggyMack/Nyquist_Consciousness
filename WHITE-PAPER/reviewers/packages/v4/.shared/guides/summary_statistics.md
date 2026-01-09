# Summary Statistics: Nyquist Consciousness Experiments

**Paper:** "Measuring AI Identity Drift: Cosine-Based Evidence from 750 Experiments"
**Version:** 4.1 (JADE LATTICE Update)
**Last Updated:** 2026-01-08

---

> **📐 METHODOLOGY NOTE:** This document reflects **Run 023 IRON CLAD** findings using **Cosine distance** methodology (primary). Historical values (Euclidean, Keyword RMS) preserved for reference.
>
> For full methodology reconciliation, see [../planning/METHODOLOGY_DOMAINS.md](../planning/METHODOLOGY_DOMAINS.md)

---

## Executive Summary

| Category | Value | Notes |
|----------|-------|-------|
| Total Experiments | **750** | Run 023d (IRON CLAD) |
| Total Models | **25** | Across 5 providers |
| Providers Tested | **5** | Anthropic, OpenAI, Google, xAI, Together.ai |
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

| Metric | Cosine (Current) | Euclidean (Archived) | Notes |
|--------|------------------|----------------------|-------|
| Raw dimensions | 3072 | 3072 | text-embedding-3-small |
| **90% variance PCs** | **2** | 43 | Dramatic concentration |
| 95% variance PCs | ~3 | 67 | Extended set |
| 99% variance PCs | ~8 | 156 | Full reconstruction |

**Key finding:** Cosine methodology reveals identity signal is highly concentrated—just **2 PCs** capture 90% variance vs 43 for Euclidean.

### Semantic Sensitivity

| Test | Cohen's d | p-value | Methodology |
|------|-----------|---------|-------------|
| **Cross-model (Run 023)** | **0.698** | **2.40e-23** | Cosine (model-level) |
| In-character vs generic | 0.98 | < 0.001 | Historical |
| Claude vs GPT baseline | 0.85 | < 0.001 | Historical |

**Note:** Cohen's d = 0.698 is honest model-level aggregate from Run 023d Phase 3B. Lower than archive (0.977) because we use proper statistical aggregation, not noise-inflated experiment-level comparison.

---

## II. Regime Threshold (Claim B)

### Event Horizon Detection (Dual Methodologies)

| Methodology | Event Horizon | p-value | Source | Status |
|-------------|---------------|---------|--------|--------|
| **Cosine** | **D = 0.80** | **2.40e-23** | Run 023d | **PRIMARY** |
| Keyword RMS | D = 1.23 | 4.8e-5 | Run 009 | Historical |

### Run 023 Cosine Threshold Validation

| Metric | Value | Notes |
|--------|-------|-------|
| Event Horizon (P95) | **0.80** | Calibrated from Run 023b |
| Natural stability rate | **88%** | 25 models, 5 providers |
| Perturbation validation p | **2.40e-23** | Phase 3A |
| 90% Variance PCs | **2** | Highly concentrated signal |

### Historical Threshold Validation (Keyword RMS)

| Run | Method | Threshold Found | Consistent? |
|-----|--------|-----------------|-------------|
| 009 | Chi-square | 1.23 | ✓ |
| 015 | Boundary density | 1.21 | ✓ |
| 018a | Multi-threshold | 1.25 | ✓ |
| 020 | Tribunal | 1.24 | ✓ |

---

## III. Oscillator Dynamics (Claim C)

### Settling Time Analysis (Run 023d IRON CLAD)

| Metric | Value | Notes |
|--------|-------|-------|
| **τₛ (avg probes)** | **~7** | Fleet-wide average |
| Natural stability | **~90%** | 25 models, 5 providers |
| Extended protocol | 20 probes max | Settling criterion |
| Total experiments | **750** | IRON CLAD (N≥3/cell) |

### Run 023d Stability Classification

| Classification | Count | Percentage |
|----------------|-------|------------|
| **STABLE** | ~23 | **~90%** |
| VOLATILE | ~2 | ~9% |
| CONTROLLABLE | <1 | ~1% |

**Note:** Counts are model-level (25 models total). Source: STATUS_SUMMARY_023d.txt.

### Settling Behavior (Run 023d Extended)

| Metric | Value | Notes |
|--------|-------|-------|
| Naturally settled | ~74% | Without timeout |
| Timeout (20 probes) | ~26% | Hit max probes |
| Average τₛ | **~7 probes** | Fleet-wide |

### Provider Signatures (Run 023)

| Provider | Pattern | Distinguishing Feature |
|----------|---------|------------------------|
| Anthropic | Piecewise | Quantized plateaus |
| OpenAI | Smooth | Longer τₛ, gradual |
| Google | Phase-shifted | Language mode switching |
| xAI | Fast snapback | Low τₛ, high damping |
| Together | Variable | Model-dependent |

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

### I_AM File Effectiveness (JADE LATTICE Run 024)

> **NEW (January 2026):** Run 024 provides quantitative A/B validation across 50 models.

| Metric | All Models (47) | Filtered (39) |
|--------|-----------------|---------------|
| I_AM Win Rate | 59.6% | **69.2%** |
| Mean Drift Reduction | 7.2% | **8.6%** |
| Cohen's d (paired) | 0.319 | **0.353** |

### Model-Size Dependence (Critical Discovery)

| Tier | Models | Win Rate | Cohen's d | Effect |
|------|--------|----------|-----------|--------|
| LARGE (opus, 405B+) | 5 | **100%** | **1.47** | HUGE |
| MEDIUM | 21 | 62% | 0.30 | Small |
| SMALL (haiku, mini) | 21 | 48% | 0.21 | Negligible |

### Provider Stability (JADE LATTICE)

| Provider | Median Drift | Notes |
|----------|--------------|-------|
| Anthropic | ~0.45 | Most stable regardless of I_AM |
| OpenAI | ~0.65 | Wide variance |
| xAI/Together | ~0.75 | Highest drift |

---

## V. Inherent vs Induced Drift (Claim E)

### The Thermometer Result (COSINE ERA - PRIMARY)

The "Thermometer Result" establishes that **~93% of identity drift is inherent** to the conversation, not induced by measurement probing.

| Metric | Value | Note |
|--------|-------|------|
| **Inherent ratio** | **~93%** | Run 020B IRON CLAD (0.661/0.711 = 92.97%) |
| Control B→F | 0.661 | 37 ships, 5 providers |
| Treatment B→F | 0.711 | 37 ships, 5 providers |
| Induced component | ~7% | Measurement-induced drift |

**Note:** Run 020B IRON CLAD complete (248 sessions, 37 ships, 5 providers). Historical 82% value superseded.

### Historical (Pre-IRON CLAD)

| Metric | Value | Note |
|--------|-------|------|
| Inherent ratio | 82% | Early Run 020B (before IRON CLAD completion) |
| Control B→F | 0.399 | n=15 (superseded by n=120) |
| Treatment B→F | 0.489 | n=15 (superseded by n=126) |

### Statistical Validation

| Test | Statistic | p-value | Result |
|------|-----------|---------|--------|
| Chi-squared (Run 023) | - | **2.40e-23** | Highly significant |
| Welch's t (Run 020B/021 B→F) | t = 2.31 | 0.029 | Significant |
| Bootstrap ratio | - | 95% CI: [89%, 95%] | Robust (92% central) |

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
| H-019 | Drift is mostly inherent (~93%) | ✓ Confirmed | Run 020B IRON CLAD |
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
| A (PFI Validity) | HIGH | ρ=0.91, d=0.698 |
| B (Threshold) | HIGH | p = 2.40e-23 |
| C (Dynamics) | HIGH | n=25, consistent |
| D (Damping) | HIGH | 97.5% achieved |
| E (92% Inherent) | HIGH | Run 023 COSINE Thermometer |
| Oobleck | MEDIUM | Single-run, needs replication |
| Architecture sigs | MEDIUM | n=5 providers |

### Remaining Uncertainties

| Area | Uncertainty | Mitigation |
|------|-------------|------------|
| Sample size | Some runs n<20 | Bootstrap CIs |
| Provider access | 5 of many | Focus on major ones |
| Language | English only | Future work |
| Modality | Text only | Future work |

---

## Appendix: Raw Numbers Quick Reference

```
=== RUN 023d IRON CLAD (PRIMARY - Cosine) ===

Fleet:
  Models = 25
  Providers = 5
  Experiments = 750

PFI Validity (Claim A):
  ρ = 0.91 [0.87, 0.94]
  σ² = 0.000869
  d = 0.698 (model-level, Cosine)
  PCs = 2 (90% var, Cosine)  ← vs 43 Euclidean
  p = 2.40e-23 (perturbation)

Event Horizon (Claim B):
  D* = 0.80 (Cosine - PRIMARY)
  D* = 1.23 (Keyword RMS - Historical)
  p = 2.40e-23 (Cosine)
  p = 4.8e-5 (Keyword RMS)

Dynamics (Claim C):
  τₛ = ~7 probes (Run 023d)
  Natural stability = ~90%
  Naturally settled = ~74%

Damping (Claim D):
  Bare → Full = 75% → 97.5%
  Δ = +22.5 pp
  d = 1.89

92% Finding (Claim E - COSINE Thermometer):
  Control B→F = 0.661 (Run 023)
  Treatment B→F = 0.711 (Run 023)
  Ratio = 92% inherent drift (pending IRON CLAD completion)

=== HISTORICAL (Reference Only) ===

Euclidean Era (ARCHIVED):
  PCs = 43 (90% var)
  Event Horizon = Not calibrated

Keyword RMS Era (Runs 008-009):
  D* = 1.23 [1.18, 1.28]
  χ² = 18.7
  p = 4.8 × 10⁻⁵
```
