# RUN REGISTRY: Which Run Proves What

**Version:** 1.0
**Date:** 2025-12-30
**Purpose:** Quick reference for experimental evidence sources

---

> **For reviewers:** This registry tells you which run to cite for which finding. When in doubt, cite the IRON CLAD run.

---

## IRON CLAD Runs (Cite These)

These runs meet the N ≥ 3 publication standard and use cosine methodology:

| Run | Focus | Scale | Key Finding | Status |
|-----|-------|-------|-------------|--------|
| **023d** | Calibration | 750 exp, 25 ships, 5 providers | Event Horizon D = 0.80, p = 2.40e-23 | COMPLETE |
| **020B** | Inherent Drift | 248 sessions, 37 ships, 5 providers | ~93% inherent (0.661/0.711) | COMPLETE |
| **018** | Context Damping | 1,549 trajectories, 51 models, 5 providers | 97.5% stability | COMPLETE |

---

## Claim-to-Run Mapping

### Claim A: PFI is Valid Structured Measurement

| Sub-claim | Evidence | Primary Run |
|-----------|----------|-------------|
| Embedding invariance (ρ = 0.91) | Cross-embedding correlation | **Run 023d** Phase 1 |
| Low-dimensional (2 PCs) | PCA analysis | **Run 023d** Phase 2 |
| Semantic sensitivity (d = 0.698) | Cross-provider comparison | **Run 023d** Phase 3B |
| Paraphrase robustness | Surface changes don't cross EH | EXP-PFI-A Phase 4 |

---

### Claim B: Regime Threshold Exists

| Sub-claim | Evidence | Primary Run |
|-----------|----------|-------------|
| Event Horizon D = 0.80 (Cosine) | Perturbation validation | **Run 023d** |
| p = 2.40e-23 | Statistical significance | **Run 023d** Phase 3A |
| PC space separability | PC2 distinguishes above/below EH | EXP-PFI-A Phase 2 |
| [Historical] D = 1.23 (Keyword RMS) | Chi-square test | Run 009 |

---

### Claim C: Damped Oscillator Dynamics

| Sub-claim | Evidence | Primary Run |
|-----------|----------|-------------|
| Settling time τₛ ≈ 7 probes | Extended protocol | **Run 023d** |
| Natural stability ~90% | 25-model fleet | **Run 023** Combined |
| Ringback patterns | Recovery oscillation | Run 016, **Run 023d** |
| Overshoot ratio | Peak vs settled | Run 016 |

---

### Claim D: Context Damping Works

| Sub-claim | Evidence | Primary Run |
|-----------|----------|-------------|
| 97.5% stability with I_AM | Full circuit protocol | **Run 018 IRON CLAD** |
| 1,549 trajectories | Multi-model validation | **Run 018 IRON CLAD** |
| 51 models, 5 providers | Cross-architecture | **Run 018 IRON CLAD** |
| Bare metal baseline | Pre-damping comparison | Run 016 (historical) |

**Note:** Run 017 is historical only — use Run 018 IRON CLAD for all context damping citations.

---

### Claim E: Drift is Mostly Inherent (~93%)

| Sub-claim | Evidence | Primary Run |
|-----------|----------|-------------|
| Control B→F = 0.661 | No-probing condition | **Run 020B IRON CLAD** |
| Treatment B→F = 0.711 | With-probing condition | **Run 020B IRON CLAD** |
| Ratio ~93% (0.661/0.711) | Thermometer result | **Run 020B IRON CLAD** |
| 248 sessions, 37 ships | Multi-model validation | **Run 020B IRON CLAD** |

---

## Novel Phenomena

### Oobleck Effect

| Aspect | Evidence | Run |
|--------|----------|-----|
| Rate-dependent resistance | Gentle > direct challenge drift | Run 013 (discovery) |
| Recovery rate increase (3.1×) | λ: 0.035 → 0.109 | Run 013 |
| Cross-platform confirmation | 5 providers | **Run 020A/020B IRON CLAD** |

---

### Provider Fingerprints

| Finding | Evidence | Run |
|---------|----------|-----|
| Constitutional AI = uniform | Claude drift patterns | **Run 023d** |
| RLHF = variable | OpenAI drift patterns | **Run 023d** |
| Gemini = language modes | Mode switching | **Run 018** |
| Grok = fast snapback | High damping | **Run 018**, **Run 023d** |

---

### Recovery Paradox

| Finding | Evidence | Run |
|---------|----------|-----|
| 100% recovery from EH crossing | No permanent "collapse" | Runs 014/016/017 |
| Recovery is ring-down | Damped oscillator | Run 016, **Run 023d** |

---

## Run Timeline (S7 ARMADA)

```text
HISTORICAL ERA (Keyword RMS, Euclidean)
───────────────────────────────────────
Run 008     Event Horizon discovery (D = 1.23)
Run 009     Chi-square validation (p = 4.8e-5)
Run 010-012 Early stability studies
Run 013     Oobleck Effect discovery

CONTROL-SYSTEMS ERA (Transition)
───────────────────────────────────────
Run 014     Manifold return / Recovery Paradox
Run 015     Linear discriminant analysis
Run 016     Settling time protocol (τₛ first measured)
Run 017     Context damping discovery (HISTORICAL ONLY)

IRON CLAD ERA (Cosine, N≥3)
───────────────────────────────────────
Run 018     Context Damping IRON CLAD (1,549 trajectories)
Run 019     Live Ziggy + SONAR
Run 020A    Tribunal (Good Cop/Bad Cop)
Run 020B    Inherent Drift IRON CLAD (~93%)
Run 022     LOGOS Commutation Cartography
Run 023d    Calibration IRON CLAD (750 exp, D = 0.80)
```

---

## What NOT to Cite

| Don't Cite | Why | Use Instead |
|------------|-----|-------------|
| Run 017 for data/values | Not IRON CLAD, methodology incomplete | **Run 018 IRON CLAD** |
| D = 1.23 as current threshold | Keyword RMS era (deprecated) | D = 0.80 (Cosine) |
| 43 PCs for 90% variance | Euclidean era (deprecated) | 2 PCs (Cosine) |
| d = 0.98 | Session-level, not model-aggregated | d = 0.698 |
| τₛ = 10.2 | Earlier estimate | τₛ ≈ 7 |
| 92% inherent | Pre-020B calculation | ~93% (0.661/0.711) |

---

## Quick Citation Templates

### For Academic Papers

**Event Horizon:**
> "...the critical threshold at cosine distance D = 0.80 (p = 2.40e-23; Run 023d, N = 750, 25 models, 5 providers)..."

**Inherent Drift:**
> "...~93% of drift is inherent to extended interaction (Run 020B IRON CLAD: control B→F = 0.661, treatment B→F = 0.711, ratio = 0.929)..."

**Context Damping:**
> "...97.5% stability with explicit identity specification (Run 018 IRON CLAD: 1,549 trajectories, 51 models, 5 providers)..."

**PFI Validity:**
> "...PFI shows embedding invariance (Spearman ρ = 0.91) and moderate cross-provider effect size (Cohen's d = 0.698), with identity concentrated in just 2 principal components capturing 90% of variance..."

---

## Data File Locations

| Run | Data File | Location |
|-----|-----------|----------|
| 018 | S7_run_018_CURRENT.json | `11_CONTEXT_DAMPING/results/` |
| 020B | S7_run_020B_CURRENT.json | `11_CONTEXT_DAMPING/results/` |
| 023d | S7_run_023d_CURRENT.json | `15_IRON_CLAD_FOUNDATION/results/` |

---

## Visualization Locations

| Run | Visualizations | Location |
|-----|----------------|----------|
| 018 | Recovery patterns | `visualizations/pics/run018/` |
| 020B | Thermometer, Oobleck | `visualizations/pics/15_Oobleck_Effect/` |
| 023d | Calibration, PCA | `visualizations/pics/12_Metrics_Summary/` |

---

*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23*
*~93% inherent. 2 PCs = 90% variance. Cosine methodology throughout.*
