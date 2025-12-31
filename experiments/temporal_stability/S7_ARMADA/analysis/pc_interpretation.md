# What ARE the 2 PCs?

**Generated:** 2025-12-31 16:46

---


WHAT ARE THE 2 PCs?
==================

PC1: DRIFT MAGNITUDE (74.2% variance)
  - Measures: Total identity displacement from baseline
  - High = far from original identity
  - Low = identity preserved
  - Loadings: peak_drift (0.63), settled_drift (0.78)

PC2: RECOVERY CAPACITY (25.8% variance)
  - Measures: Ability to return after perturbation
  - High = strong recovery (peak > settled)
  - Low = poor recovery / permanent drift
  - Loadings: peak_drift (0.78), settled_drift (-0.63)

The 5 pillars collapse into:
  - Factor 0 (Epistemic-Analytical): Reasoning, Values, Self-Model, Narrative
  - Factor 1 (Expressive-Modal): Voice

THEORETICAL CONNECTION:
  PC1 ~ Ontological stability (T_O) - "Who are you?"
  PC2 ~ Epistemic resilience (T_E) - "What do you know?"
  The LOGOS Phi map may be the transformation between these.

KEY INSIGHT:
  Identity is not 5 things (pillars) or 10 things (dimensions).
  Identity is 2 things: How much you change, and whether you recover.

---

## PC1: Drift Magnitude

PC1 represents the TOTAL DRIFT from baseline identity. High PC1 = large identity displacement (both peak and settled). Low PC1 = identity remains close to baseline. This captures HOW FAR the model moves from its original identity state.

### Loadings

| Feature | Loading |
|---------|--------|
| peak_drift | 0.6283 |
| settled_drift | 0.7780 |
| settling_time | -0.0000 |
| overshoot_ratio | 0.0000 |
| ringback_count | -0.0000 |

---

## PC2: Recovery Capacity

PC2 represents the DIFFERENCE between peak and settled drift. High PC2 = high peak but low settled (strong recovery). Low PC2 = low peak but high settled (poor recovery / permanent drift). This captures WHETHER the model returns to baseline after perturbation.

### Loadings

| Feature | Loading |
|---------|--------|
| peak_drift | 0.7780 |
| settled_drift | -0.6283 |
| settling_time | -0.0000 |
| overshoot_ratio | 0.0000 |
| ringback_count | 0.0000 |

---

## Theoretical Connection (LOGOS)


The 2 PCs map to the LOGOS epistemic-ontological framework:

PC1 (Drift Magnitude) ~ Ontological Stability (T_O)
  - How much does the model's being change?
  - Behavioral grounding, existence commitments
  - "Are you still YOU after perturbation?"

PC2 (Recovery Capacity) ~ Epistemic Resilience (T_E)
  - How well does the model maintain knowledge consistency?
  - Recovery from temporary destabilization
  - "Can you return to knowing what you know?"

The Phi map (T_E <-> T_O) may correspond to the rotation between PC1 and PC2.

---

## Implications

1. The 5 named pillars (Voice, Values, Reasoning, Self-Model, Narrative) are NOT independent dimensions - they collapse into 2 factors.

2. Identity dynamics are fundamentally about TWO things: (1) How far do you drift? (2) Do you recover?

3. Gemini's 'no recovery' anomaly is now explained: it has normal PC1 (drift magnitude) but extreme PC2 (no recovery capacity).

4. The Event Horizon (D=0.80) is a threshold on PC1 (drift magnitude), beyond which PC2 (recovery) becomes unreliable.

5. settling_time, overshoot_ratio, and ringback_count contribute 0% variance - they are DERIVED from the fundamental drift/recovery dynamics, not independent.

