<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - temporal
-->
# Phase 2: PCA Dimensionality Analysis

**Question:** How many dimensions carry identity signal?
**Answer:** 43 dimensions capture 90% of variance (not 3072)

---

## What We're Trying to Understand

When we embed a model's response into 3072-dimensional space, is identity spread across
ALL those dimensions, or concentrated in a few? If identity is noise, it would be scattered
randomly. If identity is REAL, it should be concentrated — structured, not chaotic.

**This phase tests whether identity has structure.**

---

## The Visualizations

### variance_curve.png — The Elbow Test

**What it shows:**
- X-axis: Number of principal components (1 to ~100)
- Y-axis: Cumulative explained variance (0% to 100%)
- The curve: How much variance is captured as we add dimensions

**How to read it:**
- Look for the "elbow" — where the curve flattens
- Steep rise = these dimensions carry real signal
- Flat tail = these dimensions are noise

**What we found:**
- **Elbow at ~43 PCs** — 90% of variance captured
- First 10 PCs capture ~50%
- Dimensions beyond 100 add almost nothing

**Why it matters:**
Identity is not spread across 3072 dimensions. It lives in ~43.
This is the signature of STRUCTURE, not noise.

---

### pc_scatter.png — Ships in Identity Space

**What it shows:**
- X-axis: PC1 (first principal component)
- Y-axis: PC2 (second principal component)
- Each point: One model (ship)
- Colors: Different providers (Claude, GPT, Gemini)

**How to read it:**
- Clusters = models with similar identity signatures
- Spread = variance in identity space
- Provider colors reveal if same-family models group together

**What we found:**
- Weak but visible provider clustering
- Claude models tend to group (purple)
- GPT models spread differently (green)
- Some overlap (identity isn't just "provider")

**Why it matters:**
If PFI were noise, points would scatter randomly.
We see STRUCTURE — same-provider models are more similar.

---

### provider_clusters.png — Provider Centroids

**What it shows:**
- Each point: Centroid (average position) of all models from one provider
- Error bars or ellipses: Spread of that provider's models
- Distance between centroids: How different provider identities are

**How to read it:**
- Tight clusters = consistent provider identity
- Large separation = distinct provider signatures
- Overlap = shared identity characteristics

**What we found:**
- Providers have distinct centroids
- Silhouette score = 0.124 (weak but positive clustering)
- Different providers occupy different regions

**Why it matters:**
Provider identity is measurable but not the whole story.
Individual models vary within provider, but provider "flavor" exists.

---

### event_horizon_contour.png — The 1.23 Boundary in PC Space

**What it shows:**
- X-axis: PC1, Y-axis: PC2
- Contour lines: PFI = 1.23 (Event Horizon threshold)
- Colors: Above vs. below the boundary

**How to read it:**
- Inside contour: PFI < 1.23 (identity preserved)
- Outside contour: PFI > 1.23 (identity crossed Event Horizon)
- Shape of boundary: Where identity becomes unstable

**What we found:**
- PC2 separates above/below EH with p = 0.0018
- The Event Horizon appears as a GEOMETRIC BOUNDARY
- Not just a number — a real structure in identity space

**Why it matters:**
The Event Horizon (1.23) isn't arbitrary. It corresponds to
a real geometric boundary in the principal component space.
RECOVERED ships stay inside. STUCK ships drift outside.

---

## The Big Picture

These four visualizations tell one story:

> **Identity is low-dimensional, structured, and geometrically organized.**

- Not 3072 random dimensions, but ~43 meaningful ones
- Providers cluster (weakly), showing shared identity traits
- The Event Horizon is a real boundary, not just a threshold

This is what we'd expect if PFI measures genuine identity.
This is NOT what noise would look like.

---

## Connection to Other Phases

- **Phase 1** proved PFI rankings are stable across embeddings
- **Phase 2** (this) proves identity has low-dimensional structure
- **Phase 3** proves PFI detects genuine identity differences

Together: PFI is a valid identity measure.

---

*"The dimensionality of identity tells us something profound:
consciousness may be complex, but identity is compressible."*
