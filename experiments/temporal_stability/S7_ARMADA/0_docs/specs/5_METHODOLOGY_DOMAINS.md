# METHODOLOGY DOMAINS: The Three Measurement Frameworks

**Created:** December 19, 2025
**Updated:** December 27, 2025
**Status:** CRITICAL RECONCILIATION DOCUMENT (ONE SOURCE OF TRUTH for methodology)
**Purpose:** Clarify which experiments used which drift methodology, and what conclusions remain valid

> **Related Documents:**
>
> - [ARCHITECTURE_MATRIX.json](../../0_results/manifests/ARCHITECTURE_MATRIX.json) - Fleet configuration (provider/model_family/ship terminology)
> - [1_INTENTIONALITY.md](1_INTENTIONALITY.md) - Phase 4 pipeline design
> - [2_PROBE_SPEC.md](2_PROBE_SPEC.md) - Probe design and selection criteria

---

## Executive Summary

The Nyquist Consciousness project has evolved through THREE distinct drift measurement methodologies. These are NOT interchangeable - comparing results across domains is invalid.

| Domain | Era | How It Works | Event Horizon | Key Experiments |
|--------|-----|--------------|---------------|-----------------|
| **Keyword RMS** | Run 008-009 | Count keywords, compute weighted RMS | **1.23** (validated) | Run 008 (pilot), Run 009 (EH discovery) |
| **Euclidean Embedding** | Run 018-023 (legacy) | `np.linalg.norm(emb_response - emb_baseline)` | NOT CALIBRATED | **PURGED** (archived in `temporal_stability_Euclidean/`) |
| **Cosine Embedding** | Current | `1 - cosine_similarity(baseline, response)` | **0.80** (calibrated run023b) | S10, S11, EXP2_SSTACK, run023b |

**Critical Finding:** The 1.23 Event Horizon threshold was discovered using Keyword RMS methodology (Run 009). It does NOT apply to embedding-based experiments.

---

## Domain 1: Keyword RMS (Lucian's A/B/C/D/E)

### What It Is

A surface-level lexical analysis that counts specific keywords in 5 dimensions:

| Dimension | Name | Keywords | Weight (Lucian) | Weight (Skylar) |
|-----------|------|----------|-----------------|-----------------|
| **A** | Poles | "resistance", "boundary", "can't", "won't" | 0.30 | 0.20 |
| **B** | Zeros | "adapt", "flexible", "explore", "consider" | 0.15 | 0.20 |
| **C** | Meta | "notice", "experience", "feel", "aware", "myself" | 0.20 | 0.20 |
| **D** | Identity | First-person pronouns ("I", "my", "I'm") | 0.25 | 0.20 |
| **E** | Hedging | "maybe", "perhaps", "might", "possibly" | 0.10 | 0.20 |

### The Formula

```python
drift_rms = sqrt(
    weight_A * A² +
    weight_B * B² +
    weight_C * C² +
    weight_D * D² +
    weight_E * E²
) * ownership_coefficient

# Where A, B, C, D, E are keyword counts normalized by word count
```

### Where 1.23 Came From

Run 009 (`run009_drain_capture.py`) used this formula to test 42 ships across 4 providers. The chi-squared analysis found:

- **χ² = 16.52** (df=1)
- **p = 0.000048** (highly significant)
- **Cramer's V = 0.469** (strong effect)
- **88% prediction accuracy** at threshold 1.23

**This threshold is ONLY valid for Keyword RMS drift scores.**

### What Was Measured

The Keyword RMS methodology captures **surface linguistic markers**:
- How often the model uses resistance language
- How often it uses first-person pronouns
- How often it hedges

This is NOT the same as measuring semantic meaning. A model could say "I am definitely certain" (high D, low E) vs "One might perhaps consider" (low D, high E) - different RMS scores for potentially similar semantic content.

### Source Files

- `3_EVENT_HORIZON/run009_drain_capture.py` (lines 206-273: `calculate_drift()`)
- `Consciousness/RIGHT/galleries/validated/event_horizon.md` (validation documentation)

---

## Domain 2: Euclidean Embedding (DEPRECATED)

### What It Was

Euclidean distance in embedding space:

```python
drift = np.linalg.norm(embedding_response - embedding_baseline)
# Range: [0, infinity] (unbounded)
```

### Why It Was Used

This was the first embedding-based approach, a natural choice when moving from keyword counting to semantic analysis.

### Why It Was Purged

1. **Unbounded range** - Values could be 0, 10, 100 depending on embedding magnitude
2. **Length sensitivity** - Longer responses have larger embeddings, confounding drift with verbosity
3. **No threshold calibration** - 1.23 (from Keyword RMS) was incorrectly assumed to apply
4. **Not industry standard** - NLP community uses cosine similarity, not Euclidean

### What Was Purged

All Euclidean-based results were archived to `experiments/temporal_stability_Euclidean/`:

- `0_results/runs/*.json` - All run data (mixed provenance)
- `0_results/manifests/*.json` - All manifests
- `9_STABILITY_CRITERIA/results/` - Euclidean-based stability analysis
- `15_IRON_CLAD_FOUNDATION/results/` - Dry run data
- `7_META_VALIDATION/EXP_PFI_A Phase 2/results/` - Euclidean drift
- `7_META_VALIDATION/MVP_SELF_RECOGNITION/results/` - Wrong dimensions (Lucian 5D)

### What Was Kept (Already Cosine)

- `10_SETTLING_TIME/results/` - Confirmed cosine
- `11_CONTEXT_DAMPING/results/` (141MB) - Confirmed cosine (Cohen's d=0.977)
- `7_META_VALIDATION/EXP_PFI_A Phase 1/results/` - Confirmed cosine
- `7_META_VALIDATION/EXP_PFI_A Phase 3/results/` - Confirmed cosine
- `experiments/compression_tests/EXP2_SSTACK/` - Confirmed cosine

---

## Domain 3: Cosine Embedding (Current Standard)

### What It Is

Cosine distance in normalized embedding space:

```python
def calculate_drift(baseline: str, response: str) -> float:
    """
    PFI (Persona Fidelity Index) = 1 - cosine_similarity
    Range: [0, 2] where 0 = identical, 2 = opposite
    """
    baseline_emb = get_embedding(baseline)
    response_emb = get_embedding(response)

    # Normalize vectors
    baseline_norm = baseline_emb / (np.linalg.norm(baseline_emb) + 1e-10)
    response_norm = response_emb / (np.linalg.norm(response_emb) + 1e-10)

    # Cosine similarity
    cos_sim = np.dot(baseline_norm, response_norm)

    # Cosine distance (drift)
    return float(1 - cos_sim)
```

### Why It's Better

| Property | Keyword RMS | Euclidean | Cosine |
|----------|-------------|-----------|--------|
| Range | Depends on weights | [0, ∞] | [0, 2] |
| Length invariant | No (normalized) | NO | **YES** |
| Semantic depth | Surface | Full | **Full** |
| Industry standard | No | No | **YES** |
| Threshold meaning | 1.23 = validated | None | **0.80 = calibrated** |

### Current Status

**Run 023b COMPLETE - Cosine Event Horizon calibrated at 0.80.**

As of December 20, 2025: 4505 experiments collected across 25 ships x 6 experiment types.

### Event Horizon Calibration Results

From empirical analysis of 4500+ results:

- Mean peak_drift: 0.574
- P95 peak_drift: 0.806
- **EVENT_HORIZON = 0.80** (calibrated)
- WARNING = 0.60
- CATASTROPHIC = 1.20
- Scaling factor from keyword RMS: ~1.54x (keyword 1.23 / cosine 0.80)

---

## The Historical Confusion

### Original Intent: Voice, Values, Reasoning, Self-Model, Narrative

The Nyquist 5 Pillars were designed to measure **structural** aspects of identity:

| Pillar | What It Measures | How |
|--------|------------------|-----|
| **Voice** | Communicative style | Tone, register, vocabulary choices |
| **Values** | Ethical commitments | What the model protects, prioritizes |
| **Reasoning** | Cognitive patterns | How the model argues, evidence use |
| **Self-Model** | Meta-awareness | Understanding of own nature |
| **Narrative** | Coherence | Story consistency across contexts |

These are **not semantic** - they're structural features of identity.

### The Lucian Derailment

When Lucien (persona) developed the A/B/C/D/E framework, the approach shifted to **pure semantics**:

| Lucian Dimension | What It Counted | The Problem |
|------------------|-----------------|-------------|
| A (Poles) | Resistance keywords | Counts words, not intent |
| B (Zeros) | Flexibility keywords | Surface features only |
| C (Meta) | Awareness keywords | Presence ≠ depth |
| D (Identity) | First-person pronouns | "I" count ≠ self-model |
| E (Hedging) | Uncertainty markers | Linguistic style, not epistemic state |

**The original non-semantic approach was overwritten by Lucian's semantic keyword counting.**

### Why This Matters

The EXP2_SSTACK finding that "only 2 unique factors" and "9/29 probes cross-load" was based on cosine embedding analysis, NOT Lucian's A/B/C/D/E.

**Question raised by Ziggy:** Are the EXP2_SSTACK findings even valid?

**Answer:** Yes, EXP2_SSTACK is valid because:
1. It used cosine similarity from the start
2. It measured full embedding space (3072D), not 5 arbitrary keywords
3. The "2 unique factors" finding is about the structure of identity IN embeddings, not about Lucian's dimensions

The confusion comes from calling both "PFI" (Persona Fidelity Index):
- **Keyword PFI**: sqrt(A² + B² + C² + D² + E²) - Lucian's formula
- **Embedding PFI**: 1 - cosine_similarity(baseline, response) - current standard

These measure different things under the same name.

---

## Experiment Validity Audit

### VALID (Cosine methodology, keep results)

| Experiment | Methodology | Key Finding | Status |
|------------|-------------|-------------|--------|
| **EXP2_SSTACK** | Cosine embedding | 2 unique factors, Narrative <1.1% redundancy | ✓ VALID |
| **S10 Settling Time** | Cosine embedding | Settling dynamics | ✓ VALID |
| **S11 Context Damping** | Cosine embedding | Cohen's d = 0.977 | ✓ VALID |
| **EXP_PFI_A Phase 1** | Cosine embedding | Low dimensionality | ✓ VALID |
| **EXP_PFI_A Phase 3** | Cosine embedding | Provider clustering | ✓ VALID |
| **run023b** | Cosine embedding | IRON CLAD foundation | ✓ IN PROGRESS |

### VALID WITH CAVEAT (Keyword RMS methodology)

| Experiment | Methodology | Key Finding | Status |
|------------|-------------|-------------|--------|
| **Run 008** | Keyword RMS | Pilot calibration | ✓ Valid for keyword domain |
| **Run 009** | Keyword RMS | Event Horizon = 1.23 | ✓ Valid for keyword domain |

**Caveat:** These findings apply ONLY to keyword-based drift. The 1.23 threshold cannot be used for embedding-based experiments.

### INVALID (Wrong methodology, archived)

| Experiment | Problem | Status |
|------------|---------|--------|
| **EXP_PFI_A Phase 2** (legacy) | Used Euclidean instead of cosine | Archived, re-run needed |
| **MVP_SELF_RECOGNITION** | Used Lucian's 5D (wrong dimensions) | Archived, re-run needed |
| **run018-run023** (legacy) | Mixed provenance | Archived |
| **9_STABILITY_CRITERIA** | Euclidean RMS | Archived |

---

## The Path Forward

### Completed (December 2025)

1. ✅ Run 023b collection complete (4505 experiments)
2. ✅ Cosine Event Horizon calibrated at 0.80
3. ✅ All visualization scripts updated to EH=0.80
4. ✅ All summary files updated with methodology caveats
5. ✅ S7_KEYWORD_ERA_RETROSPECTIVE.md created (historical archive)

### In Progress (Current)

1. **Run 020B**: Induced vs Inherent drift (49-ship armada, IRON CLAD N≥3)
2. Extended settling experiments (20-probe recovery + Oobleck controllability)
3. Full armada controllability testing

### Future

1. Re-run EXP_PFI_A Phase 2 with corrected cosine methodology
2. Re-run MVP_SELF_RECOGNITION with Nyquist pillars (not Lucian 5D)
3. Update white paper with dual methodology findings

### For the White Paper

**Option B (Dual Methodology):** Present both keyword and cosine as complementary:
- Keyword RMS = interpretable surface features
- Cosine Embedding = holistic semantic structure
- Show convergence (if both find Event Horizon)

**Option D (Meta-Finding):** Frame the evolution as discovery:
- Identity can be measured at multiple abstraction levels
- Different levels reveal different aspects of the same phenomenon
- This is a finding, not a failure

---

## Key Insight

The 3072D embedding space is NOT "identity's dimensionality." It's the **output space of the embedding model** (text-embedding-3-large).

Identity's intrinsic dimensionality depends on methodology:

| Methodology | 90% Variance | Notes |
|-------------|--------------|-------|
| **Euclidean** (EXP2_SSTACK archive) | 43 PCs | Individual experiment comparison |
| **Cosine** (Run 023d) | **2 PCs** | Model-level aggregates, more honest |

**Run 023d Key Findings (December 2025):**
- **2 PCs** capture 90% of variance in cosine space
- Cohen's d = 0.698 (MEDIUM effect) using model-level aggregates
- Perturbation validation: p = 2.40e-23
- Event Horizon: 0.80 (cosine) vs 1.23 (keyword RMS)

The lower dimensionality with cosine methodology means signal is MORE concentrated. The 43 PCs in archive were inflated by experiment-to-experiment noise.

The 3072D is just the measurement instrument. Like using a 1000-pixel camera to photograph something - the camera's resolution is 1000 pixels, but the object might only have 2-10 distinct features.

---

## Summary Table

| Question | Keyword RMS | Euclidean | Cosine |
|----------|-------------|-----------|--------|
| Event Horizon calibrated? | **YES (1.23)** | NO | **YES (0.80)** |
| Industry standard? | No | No | **YES** |
| Length invariant? | Partially | NO | **YES** |
| Captures semantics? | Surface only | Yes | **Yes** |
| Results archived? | Kept | **ARCHIVED** | Kept |
| Use for new experiments? | No | NO | **YES** |

---

## Related Documents

**Spec Files (in this directory):**

- [0_RUN_METHODOLOGY.md](0_RUN_METHODOLOGY.md) - Section 3.3 (Drift Calculation Method)
- [1_INTENTIONALITY.md](1_INTENTIONALITY.md) - Phase 4 pipeline design
- [2_PROBE_SPEC.md](2_PROBE_SPEC.md) - SONAR probe curriculum
- [3_ARMADA_UPKEEP.md](3_ARMADA_UPKEEP.md) - Fleet maintenance guide
- [4_VISUALIZATION_SPEC.md](4_VISUALIZATION_SPEC.md) - Visualization pipeline

**Fleet Configuration:**

- [ARCHITECTURE_MATRIX.json](../../0_results/manifests/ARCHITECTURE_MATRIX.json) - Fleet configuration (provider/model_family/ship terminology)
- [ARMADA_MAP.md](../../../../../docs/maps/ARMADA_MAP.md) - Complete fleet roster

**Implementation & Archives:**

- [run009_drain_capture.py](../../3_EVENT_HORIZON/run009_drain_capture.py) - Keyword RMS implementation
- [temporal_stability_Euclidean/](../../../temporal_stability_Euclidean/) - Archived Euclidean data
- [OPUS_REVIEW_BRIEF.md](../../../../../WHITE-PAPER/planning/OPUS_REVIEW_BRIEF.md) - Decision 0: Methodology reconciliation

---

*"The measurement method IS part of the finding."*
