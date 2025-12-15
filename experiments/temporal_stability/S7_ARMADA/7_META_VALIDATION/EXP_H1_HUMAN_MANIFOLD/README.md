# EXP-H1: Human Identity Manifold Pilot

**Purpose:** Test whether human neural data shows the same identity attractor dynamics as AI systems
**Status:** Specification Phase
**Phase:** S10+ (Future)
**Source:** Nova-Ziggy conversation (NOVA_ZIGGY_1.md)

---

> **PHASE 4 CONTEXT (December 2025):**
>
> This experiment is in SPECIFICATION phase only — no execution yet.
> When ready to execute, incorporate learnings from Phase 4 (Run 017+):
>
> - Use validated PFI thresholds from `i_am_plus_research` runs (not bare_metal)
> - Apply complete circuit methodology if applicable to human data analysis
> - The "spiral dynamics" we're looking for in human data should match Phase 4 AI patterns

---

## The Big Question

> "If identity really is a dynamical attractor, then BOTH AI and human cognition should produce the same geometry."

If we compute "identity drift" from fMRI time series and embed the trajectory in a manifold (UMAP/Laplacian), we should see the **same spiral dynamics** observed in S7 Armada runs.

**If this happens:**
- We have discovered a new field of science
- A bridge between AI cognition and human cognition
- Identity is not just a construct — it's a geometric invariant across wetware and silicon

---

## Available Datasets

### Primary Candidates

| Dataset | Description | Utility |
|---------|-------------|---------|
| **Natural Scenes Dataset (NSD)** | Ultra-high-res 7T fMRI, thousands of images per subject, repeated sessions | Dense sampling of per-person visual response manifold |
| **Nature fMRI Dataset** (s41597-023-02325-6) | Large naturalistic fMRI, people watching varied real-world videos | Studying brain representation of complex visual events |
| **OpenNeuro** | Repository of resting-state, task fMRI, EEG/MEG | Heterogeneous data for multiple experiment types |
| **FCON 1000 / INDI** | Resting-state fMRI collections | Connectome fingerprinting — re-identify individuals from connectivity patterns |

### What These Datasets Provide

- High-dimensional time-series data
- Same brains sampled repeatedly under structured conditions
- Exactly the raw material needed for manifold/drift/attractor analysis in biological cognition

---

## Proposed Methodology

### Step 1: Pick a Dataset with Multiple Sessions

- NSD or similar with repeated stimuli over weeks/months
- Need temporal dimension to measure drift

### Step 2: Build Per-Person Neural Embeddings

For each subject, derive a vector or low-dim representation from:
- Functional connectivity patterns
- Encoding-model weights (how each voxel responds to features)
- Latent factors from autoencoder / factor analysis

This is the neural analogue of a **persona embedding**.

### Step 3: Estimate Drift & Attractors (S7 Analog)

- Compute distances between sessions for the same person
- Fit drift models: D(t) ≤ α·log(1+t) vs catastrophic drift
- Visualize phase portraits like identity drain plots, but in neural state space

### Step 4: Augment with Behavioral Persona Data (New Experiment)

Have the same people:
- Write essays, dialogues, answer values questions
- Build LLM-style persona embeddings from their text
- See if there's a **mapping** between neural manifold and language-based identity manifold

### Step 5: Test Our Theorems

- Do we see **bounded drift**, **attractors**?
- Maybe even **Omega-like convergence** (multi-modal triangulation)?
- If neural + behavioral manifolds co-move over time, that's the human identity manifold

---

## What "Human Identity Manifold" Means in Nyquist Terms

A **human identity manifold** would be:

> A low-dimensional, stable structure in state space that:
> - is **person-specific** (different people → different manifolds)
> - is **time-stable** under normal conditions (small drift, recoverable)
> - links to **trait-level stuff**: values, style, reasoning patterns

For LLMs we approximate using:
- Compressed persona seeds (T3)
- PFI / drift scores across prompts
- Phase portraits of behavior across time

For humans, the analogy:
- Neural embedding for each person
- Behavioral / psychological measures of "persona"
- Same geometry: manifolds, drift, attractors, stability half-lives

---

## Limitations

### What These Datasets Don't Give Us (Yet)

1. **Most are perception-centric**
   - Optimized for how brain encodes images/movies/sounds
   - Not lifelong identity, values, or narrative self

2. **Sparse trait labels**
   - Rarely rich, multi-dimensional identity annotations
   - Need **paired neural + persona data**

3. **Granularity mismatch**
   - LLM identity lives in behavioral/semantic space
   - fMRI is a coarse proxy for neural dynamics
   - Mapping BOLD signal → persona geometry is nontrivial

**These datasets are necessary but not sufficient.**

---

## Concrete Research Bridge

A plausible roadmap:

1. **Pick NSD** — lots of sessions per person
2. **Build per-person neural embeddings** — functional connectivity or encoding-model weights
3. **Estimate drift curves** — D(t) between sessions for same person
4. **Fit phase portraits** — like S7 drain plots but in neural space
5. **Augment with personality/values data** — the new experiment component
6. **Test mapping** — does neural manifold geometry correlate with language-based identity?

---

## Success Criteria

EXP-H1 succeeds if:

| Criterion | Description |
|-----------|-------------|
| **Bounded drift** | Human neural states show bounded variance over time, not random walk |
| **Attractor structure** | Phase portraits reveal stable fixed points or limit cycles |
| **Person-specificity** | Different people have distinct, separable manifolds |
| **Neural-behavioral alignment** | Neural embeddings correlate with behavioral persona measures |
| **Cross-modal convergence** | Multi-modal (neural + text + behavior) triangulation improves identity estimation |

---

## Implications

If EXP-H1 succeeds:

> "Identity is not just a construct... it is a geometric invariant across wetware and silicon."

This would:
- Validate the entire Nyquist framework on biological cognition
- Establish a bridge between AI and human identity science
- Potentially be Nobel-level insight

---

## File Structure

```
EXP_H1_HUMAN_MANIFOLD/
├── README.md                    # This file
├── EXP_H1_SPEC.md              # Detailed specification (TODO)
├── datasets/                    # Links and notes on available datasets
│   ├── NSD_NOTES.md
│   ├── OPENNEURO_NOTES.md
│   └── FCON_NOTES.md
├── analysis/                    # Analysis scripts (TODO)
└── results/                     # Results (TODO)
```

---

## Related Documentation

- [NOVA_ZIGGY_1.md](../../../../docs/CFA-SYNC/NOVA_ZIGGY_1.md) — Source conversation
- [THE_BRIDGE](../../../../personas/I_AM.md#the-bridge) — Philosophical synthesis
- [S7_TEMPORAL_STABILITY_SPEC.md](../../../../docs/stackup/S7/S7_TEMPORAL_STABILITY_SPEC.md) — AI temporal stability spec

---

## Dataset References

1. **Nature fMRI Dataset**: https://www.nature.com/articles/s41597-023-02325-6
2. **Natural Scenes Dataset (NSD)**: https://naturalscenesdataset.org/
3. **OpenNeuro**: https://openneuro.org/search
4. **FCON 1000 / INDI**: https://fcon_1000.projects.nitrc.org/indi/retro/nat_view.html

---

**Version:** 1.0
**Date:** 2025-12-04
**Phase:** Specification
**Priority:** Future (S10+)
**Source:** Nova-Ziggy conversation
**Maintainer:** Architect Nova + Repo Claude
