<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./run_phase2.py
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
-->
# Phase 2: Dimensionality Analysis

**Purpose:** Determine how many embedding dimensions carry identity signal vs noise
**Status:** DESIGNED
**Depends on:** Phase 1 embeddings (COMPLETE)

---

## Core Questions

1. **Is identity low-dimensional?**
   - If 90% variance in top 50 dims → identity is compressible
   - If variance spread across 1000+ dims → identity is high-dimensional noise

2. **Which dimensions correlate with stability?**
   - Find dims where STABLE models cluster differently than VOLATILE
   - These are "identity-specific" dimensions

3. **Can we build a better metric?**
   - If identity lives in a subspace, project there first
   - "Identity-PFI" = distance in identity subspace only

---

## Method

### Step 1: Collect Drift Vectors

For each ship's response sequence:
```
drift_vector[t] = E(response[t]) - E(baseline)
```

Stack all drift vectors into matrix D (n_samples × 3072)

### Step 2: PCA Decomposition

```python
from sklearn.decomposition import PCA

pca = PCA(n_components=100)
pca.fit(D)

# Key outputs:
# - pca.explained_variance_ratio_  → how much each PC captures
# - pca.components_                → the principal directions
# - cumsum(explained_variance)     → cumulative variance curve
```

### Step 3: Find Identity Dimensions

**Approach A: Stability Correlation**
1. Label each ship as STABLE (PFI < 0.5) or VOLATILE (PFI > 0.7)
2. For each PC, compute t-test between STABLE vs VOLATILE projections
3. Dims with p < 0.05 are "identity-relevant"

**Approach B: Discriminant Analysis**
1. Use LDA to find dimensions that maximally separate STABLE/VOLATILE
2. These are the "identity discriminant axes"

**Approach C: Attractor Analysis**
1. For STABLE ships, do PCs show recovery toward origin?
2. For VOLATILE ships, do PCs show divergence?
3. Dims with different dynamics = identity-relevant

### Step 4: Reconstruction Test

1. Project drift into top-k PCs only
2. Recompute "compressed PFI"
3. Compare rank-order to full PFI
4. Find minimum k where Spearman ρ > 0.95

---

## Success Criteria

| Criterion | Threshold | Meaning |
|-----------|-----------|---------|
| 90% variance in top-k | k < 100 | Identity is compressible |
| Identity dims found | ≥ 5 significant | Clear structure exists |
| Compressed PFI ρ | > 0.95 | Can reduce dimensions |
| STABLE/VOLATILE separation | p < 0.01 | Dims discriminate |

---

## Outputs

### Primary Deliverables

1. **Variance Curve Plot** - cumsum(explained_variance) vs n_components
2. **Identity Dimension List** - which PCs correlate with stability
3. **Compressed PFI Formula** - project to top-k, measure distance
4. **Dimension Interpretation** - what do top PCs represent semantically?

### Bonus Analysis

- **PC Loadings Visualization** - heatmap of what words/features load on each PC
- **3D Identity Space** - t-SNE/UMAP of ships in reduced space
- **Per-Provider Clustering** - do Claude/GPT/Gemini cluster in PC space?

---

## Data Requirements

Need from Phase 1 / existing runs:
- Raw response text (to re-embed if needed)
- Baseline embeddings per ship
- Full embedding vectors (3072D for text-3-large)

**Note:** Phase 1 computed PFI (scalar) but may not have stored full vectors.
May need to re-run embedding step to get full vectors.

---

## Implementation Plan

```
phase2_dimensionality/
├── README.md                      # This file
├── collect_drift_vectors.py       # Step 1: Build drift matrix
├── pca_analysis.py                # Step 2: PCA decomposition
├── identity_dimensions.py         # Step 3: Find identity dims
├── compression_test.py            # Step 4: Test compressed PFI
├── visualizations.py              # Plots and figures
└── results/
    ├── variance_curve.png
    ├── identity_dims.json
    └── phase2_results.json
```

---

## What Would Refute the Framework

| Finding | Implication |
|---------|-------------|
| Variance spread across >500 PCs | Identity may be noise |
| No dims correlate with stability | PFI doesn't capture identity |
| Compressed PFI ρ < 0.5 | Can't reduce dimensions |
| Random clustering in PC space | No structure to find |

---

## Relation to Metric Refinement

If Phase 2 succeeds, we can:

1. **Refine PFI** → Use identity subspace distance instead of full 3072D
2. **Split PFI** → Separate metrics for different identity facets
3. **Hunt New Metrics** → The "dead" dimensions might capture something else
4. **Laplace Analysis** → Apply system dynamics to PC trajectories

---

**Version:** 1.0
**Date:** 2025-12-05
**Status:** Designed, Ready for Implementation
