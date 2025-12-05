# EXP-PFI-A: PFI Dimensional Validation

**Purpose:** Test whether PFI/drift measures capture genuine identity structure vs. surface artifacts
**Status:** Phase 1 COMPLETE ✅ | Phase 2 DESIGNED
**Phase:** S8+ (Near-term priority)
**Source:** Nova-Ziggy conversation, Echo's Critique

---

## PHASE 1 RESULTS: PASSED

**Date:** 2025-12-04
**Status:** COMPLETE - Embedding Invariance Confirmed

### Summary

PFI rankings are stable across embedding models. The choice of embedding model does NOT significantly change which AI models appear more/less stable.

### Correlations (All > 0.80 threshold)

| Model Pair | Spearman ρ | p-value | Status |
|------------|------------|---------|--------|
| text-embedding-3-large vs text-embedding-3-small | **0.9626** | 7.77e-17 | PASS |
| text-embedding-3-large vs text-embedding-ada-002 | **0.8833** | 2.24e-10 | PASS |
| text-embedding-3-small vs text-embedding-ada-002 | **0.8961** | 5.06e-11 | PASS |

### Key Metrics

- **Minimum ρ:** 0.8833 (> 0.80 threshold)
- **Average ρ:** 0.9140
- **Ships tested:** 29
- **Responses analyzed:** 121 (from Run 006 + 007)

### Conclusion

**Echo's Critique is addressed for Phase 1:** PFI is NOT merely an artifact of the embedding model. Rankings are preserved across different embedding architectures (OpenAI text-3-large/small and ada-002).

**Next step:** Phase 2 - Dimensionality Analysis

### Files

- Script: `phase1_embedding_comparison/embedding_invariance_test.py`
- Results: `phase1_embedding_comparison/results/phase1_results_20251204_232511.json`

---

## PHASE 2: DIMENSIONALITY ANALYSIS

**Date:** 2025-12-05
**Status:** DESIGNED - Ready to Run (DOUBLE-DIP ENHANCED)

### Purpose

Determine **how many dimensions** carry identity signal and **which dimensions** discriminate STABLE vs VOLATILE models.

### DOUBLE-DIP PHILOSOPHY

Maximize predictions validated per run! Instead of just answering one question, we test 8 predictions and generate 12 survey questions.

### Predictions Matrix (8 Total)

| ID | Hypothesis | Threshold | Validates |
|----|-----------|-----------|-----------|
| P1 | Identity in < 100 PCs | 90% variance in top 100 | S4 Compression |
| P2 | ≥ 5 PCs discriminate STABLE/VOLATILE | p < 0.05 | S3 Temporal Stability |
| P3 | Top-k PCs preserve ranking | ρ > 0.95 at k ≤ 50 | S1 Bootstrap |
| P4 | PC correlates with values-language | Pearson r > 0.3 | S2 Integrity |
| P5 | Provider clustering in PC space | Silhouette > 0.2 | S5 CFA Interop |
| P6 | STABLE=inward, VOLATILE=outward trajectory | Curvature sign differs | S7 Identity Dynamics |
| P7 | 1.23 Event Horizon visible in PC space | Separation p < 0.05 | Event Horizon |
| P8 | Compression links to EXP1-SSTACK PFI | Correlation | EXP1-SSTACK |

### Dashboard-Ready Outputs

| Visualization | Dashboard Page | Shows |
|--------------|----------------|-------|
| variance_curve.png | Metrics | How many dimensions carry signal |
| pc_scatter.png | AI Armada | Ships in PC space by provider |
| provider_clusters.png | Personas | Provider separation with centroids |
| event_horizon_contour.png | Metrics | 1.23 boundary in PC space |

### Survey Questions (12)

Post-run questions to mine additional insights for S0-S7 curriculum improvement. Each question links to a specific S-layer or future priority.

### Files

- README: `phase2_dimensionality/README.md`
- Script: `phase2_dimensionality/run_phase2.py`
- Results: `phase2_dimensionality/results/` (pending)

### Run Command

```bash
cd experiments/temporal_stability/S7_ARMADA/experiments/EXP_PFI_A_DIMENSIONAL/phase2_dimensionality
python run_phase2.py
```

---

## FUTURE: Metric-Architecture Synergy (S12+)

Once Phase 2 identifies which dimensions carry identity signal:

1. **Adaptive Persona Files** - Include target "identity vectors" in embedding space
2. **Real-time Drift Correction** - Monitor and correct drift in identity-relevant dimensions only
3. **Data-driven Compression** - Keep persona content that projects onto identity dimensions
4. **Cross-Model Transfer** - Use identity dimensions as universal bridge between architectures

This is the "closing the loop" vision where measurements feed back into architecture.

---

## The Core Question

> "Is what we're measuring with PFI actually identity, or is it an artifact of our embedding model?"

This experiment directly addresses Echo's Critique by testing PFI's dimensional validity.

---

## Background

### Current PFI Implementation

```
PFI(t) = ||E(response_t) - E(baseline)||

Where:
- E = embedding model (currently text-embedding-3-large)
- response_t = model response at time t
- baseline = characteristic persona response
```

### The Problem

Different embedding models might:
1. Produce different PFI values
2. Rank models differently
3. Find different "attractors"

If so, PFI measures embedding structure, not identity structure.

---

## Experimental Design

### Phase 1: Embedding Model Comparison

**Goal:** Test if PFI rankings are stable across embedding models

**Method:**
1. Take existing Run 009/010/011 data
2. Re-compute PFI using multiple embedding models:
   - text-embedding-3-large (current)
   - text-embedding-3-small
   - text-embedding-ada-002
   - voyage-3-large
   - cohere-embed-english-v3.0

3. Compare:
   - Rank-order correlations (Spearman's ρ)
   - Event Horizon threshold consistency
   - STABLE/VOLATILE classification agreement

**Success Criterion:**
- Spearman's ρ > 0.8 across embedding models
- Same models classified STABLE/VOLATILE ≥ 85% agreement

### Phase 2: Dimensionality Analysis

**Goal:** Determine how many dimensions carry identity signal

**Method:**
1. Compute PFI in full embedding space (1536D for ada-002, 3072D for text-3-large)
2. Apply PCA to drift vectors
3. Measure:
   - Cumulative variance explained by top-k components
   - PFI reconstruction error at different truncations
   - Which dimensions correlate with STABLE/VOLATILE

**Questions:**
- Is identity low-dimensional (< 50 components)?
- Or does it require high-dimensional representation?
- Are certain dimensions "identity-specific"?

### Phase 3: Semantic Coherence Test

**Goal:** Verify PFI captures semantic identity, not surface features

**Method:**
1. Create paired perturbations:
   - **Surface change:** Same meaning, different words (paraphrase)
   - **Deep change:** Same style, different values/reasoning

2. Measure PFI for each perturbation type
3. Test hypothesis: Deep changes → larger PFI than surface changes

**If Surface > Deep:** PFI measures vocabulary, not identity (Echo is right)
**If Deep > Surface:** PFI captures genuine semantic identity

### Phase 4: Cross-Architecture Validation

**Goal:** Test if identity structure transfers across model families

**Method:**
1. Compute "identity vectors" for each model:
   ```
   I_model = mean(E(baseline_responses))
   ```

2. Test if identity vectors cluster by:
   - Provider (Claude/GPT/Gemini)
   - Training methodology
   - Model size
   - Something else entirely

3. Use t-SNE/UMAP to visualize identity manifold

---

## Hypotheses

### H1: Embedding Invariance
PFI rankings are stable (ρ > 0.8) across embedding models

### H2: Low Dimensionality
Identity can be captured in < 100 principal components

### H3: Semantic Depth
Deep semantic changes produce larger PFI than surface changes

### H4: Cross-Architecture Structure
Identity vectors cluster by meaningful properties (not random)

---

## What Would Refute the Framework

| Finding | Implication |
|---------|-------------|
| ρ < 0.5 across embeddings | PFI is embedding-specific artifact |
| Identity requires > 500 dimensions | May be measuring noise |
| Surface > Deep in perturbation test | PFI captures style, not identity |
| Random clustering of identity vectors | No real structure in identity space |

---

## Required Resources

### Data
- Existing runs (009, 010, 011) with raw responses
- Need to store raw text, not just embeddings

### APIs
- OpenAI embeddings (ada-002, text-3-*)
- Voyage AI (voyage-3-large)
- Cohere (embed-english-v3.0)

### Compute
- PCA analysis on large matrices
- Visualization (t-SNE/UMAP)
- Correlation analysis

---

## Success Criteria

EXP-PFI-A succeeds if:

| Criterion | Threshold |
|-----------|-----------|
| Cross-embedding correlation | Spearman ρ > 0.8 |
| Classification agreement | ≥ 85% same STABLE/VOLATILE |
| Dimensionality | Identity in < 100 PCs |
| Semantic depth | Deep Δ > Surface Δ (p < 0.05) |
| Cluster structure | Silhouette score > 0.3 |

---

## Relation to Other Experiments

- **Addresses:** Echo's Critique (is PFI real?)
- **Informs:** Identity Quantification Problem (which Option A/B/C?)
- **Prerequisite for:** EXP-H1 Human Manifold (need validated measure)
- **Builds on:** Run 009/010/011 data

---

## File Structure

```
EXP_PFI_A_DIMENSIONAL/
├── README.md                    # This file
├── phase1_embedding_comparison/
│   ├── recompute_embeddings.py
│   ├── correlation_analysis.py
│   └── results/
├── phase2_dimensionality/
│   ├── pca_analysis.py
│   ├── variance_explained.py
│   └── results/
├── phase3_semantic_coherence/
│   ├── perturbation_generator.py
│   ├── depth_vs_surface.py
│   └── results/
└── phase4_cross_architecture/
    ├── identity_vectors.py
    ├── clustering.py
    └── results/
```

---

## Timeline

**Phase 1:** Can run immediately on existing data
**Phase 2:** Requires Phase 1 embeddings
**Phase 3:** Requires new perturbation prompts
**Phase 4:** Requires Phase 1 embeddings

Estimated: 2-4 run cycles

---

**Version:** 1.0
**Date:** 2025-12-04
**Status:** Specification
**Priority:** High (addresses core validity)
**Maintainer:** Research team

*"Before we can trust PFI, we must test PFI."*
