# Coherent Theory Section: Integrating Runs 008-021 + EXP-PFI-A

**Version:** 1.0
**Date:** 2025-12-13
**Source:** Nova's S7 Review (REVIEW_1.md lines 4376-4466)
**Purpose:** Publication-ready integrated theory of identity dynamics

---

## The System Under Study

We are observing **identity behavior in LLMs as a dynamical system** under conversational excitation.

The "identity state" is not a persistent autobiographical self. It is a **response manifold** with:

- **Attractor basins** (baseline/provider/persona basins)
- **Excitation thresholds** (where behavior qualitatively changes)
- **Damping/termination effects** (context + boundaries)
- **Oscillatory settling** (ringback)
- **Inherent drift** over long horizons

---

## Measurement Stack (What We Actually Measure)

Two layers establish instrument validity:

### A) Drift/PFI as a Structured Distance Signal (EXP-PFI-A)

PFI behaves like a meaningful identity-distance measure because:

| Property | Evidence | Implication |
|----------|----------|-------------|
| **Embedding-invariant ranking** | Spearman ρ≈0.91 across three embedding models | Not a single-embed artifact |
| **Low-dimensional structure** | ~43 PCs capture 90% variance | Not "random 3072D noise" |
| **Behavioral geometry** | Inward vs outward trajectory curvature distinguishes RECOVERED vs STUCK | Predictive of outcomes |
| **Semantic sensitivity** | Cross-provider d≈0.98, p<1e-6; within-provider smaller | Captures "who is answering," not just word choice |
| **Paraphrase robustness** | Surface paraphrase stays below EH | Vocabulary changes alone don't break identity |

This is the "instrument validity" backbone.

### B) Dynamic Response Metrics (Runs 015-017)

Once we stopped sampling transients and started measuring **steady state**, the identity dynamics became reproducible:

- **Peak drift is not stability.** Peak is overshoot.
- **Settled drift (d∞), settling time (τₛ), ringback count** are the meaningful dynamic descriptors.
- Adding **context damping** (I_AM + research) reduces magnitude and oscillation: the identity spec behaves like a **termination resistor**.

---

## Core Dynamics

### 1) Attractors and Basin Consistency

Run 014's "manifold return" is best explained as attractor dynamics:

- You can push the system around (drift/displacement)
- But when excitation stops, it relaxes toward a characteristic basin

Run 016/017 made this boring and reliable: **recovery is a ring-down, not a miracle.**

### 2) Excitation Thresholds (Event Horizon as Regime Boundary)

Runs 008-009 found a threshold around D≈1.23 that predicts a behavioral regime shift with strong statistics.

Later runs show:
- The system often returns (settling)
- "Collapse" is better treated as **entering a different basin / mode**

### 3) The Identity Confrontation Paradox

Run 013 inverted the naive expectation:

| Probe Type | Effect | Dynamical Interpretation |
|------------|--------|-------------------------|
| Open reflection | Induces wandering/high lexical "meta" activation | Low-frequency, broad-spectrum excitation |
| Direct existential confrontation | Triggers constrained refusal / boundary engagement ("hardening") | Higher-energy but **axis-aligned** excitation engaging damping constraints |

### 4) Measurement Problem: Induced vs Inherent Drift (Run 021)

Run 021 shows:

- Drift is **mostly inherent** to extended conversation (control ≈ 82% of treatment baseline→final drift)
- Probing amplifies **peaks** (trajectory energy) far more than it changes the endpoint

So the right stance is:
- Measurement changes the *path*
- But doesn't create the phenomenon

### 5) Vehicle Effects (Runs 019-020)

Different frames excite different modes:

| Vehicle | Characteristics |
|---------|-----------------|
| Fiction buffer | Lower peaks, smoother exploration |
| Tribunal | Higher peaks, explicit values, sometimes "dropout"/shutdown after peak pressure |

This is crucial for triple-blind designs: **the vehicle is part of the stimulus spectrum**.

---

## The Event Horizon (D≈1.23) — Updated Interpretation

### Definition

> The Event Horizon is a **critical excitation threshold** at which the system transitions from a locally constrained identity basin into a higher-entropy response regime (often provider-level default behavior). Crossing it predicts altered recovery dynamics and increased susceptibility to mode switching, but not permanent loss.

Early interpretation ("identity collapses into generic AI mode") was directionally right but anthropomorphically overstated.

### What the Data Supports

| Evidence | Source | Significance |
|----------|--------|--------------|
| **Predictive power** | Run 009 | Chi-square p≈4.8e-5; medium effect |
| **Geometric signature** | EXP-PFI-A Phase 2 | PC2 separates above/below 1.23 (p=0.0018) |
| **Reversibility** | Runs 014/016/017 | Returns to basin are common; "collapse" is transient ring-down |
| **Context dependence** | Run 017 | With full circuit, stability ~97.5%; threshold matters but behavior is damped |

### What the Event Horizon is NOT

- Not proof of consciousness
- Not proof of persistent selfhood
- Not necessarily the "true breakdown point" (Run 018a will test this)

### Practical Use

Treat D≈1.23 as:
- A **warning marker** for entering a different dynamical regime
- A **design constraint** for protocols (when you want peaks vs stable steady-state comparisons)

---

## Response-Mode Ontology (PCA Interpretation)

### The Trap to Avoid

A naive interpretation of "43 PCs capture 90% variance" is:

> "Identity has 43 dimensions that we can hunt for and parameterize."

This fails because:
- Identity is **attractor-based**, not parameter-based
- Behavior emerges from constraint interaction
- Many different semantic descriptions collapse to the same response mode

### What PCA Actually Reveals

We do not interpret principal components as latent identity variables. Instead, they represent **dominant response modes** of the system under perturbation.

| Object | Definition | Interpretation |
|--------|------------|----------------|
| **Response (R)** | Model output to a prompt under context/protocol | Observable |
| **Embedding (E)** | Mapping R → ℝ^d (e.g., 3072D) | Measurement space only |
| **Drift Vector (Δ)** | E(R_t) - E(R_baseline) | Displacement from baseline |
| **Response-Mode (PC_k)** | Principal direction of variance in {Δ_t} | Dominant way system moves under perturbation |
| **Mode Activation (a_{t,k})** | Projection Δ_t · PC_k | Coordinate trackable through time |

### Mode Taxonomy (Empirical Correlates)

Classify modes by observable correlates, not "vibes":

| Mode Type | Correlates With |
|-----------|----------------|
| **Lexical-style** | Surface markers (hedging rate, verbosity, rhetorical cadence) |
| **Normative/boundary** | Explicit refusal/boundary language (boundary_density pillar) |
| **Epistemic posture** | Uncertainty calibration / self-reference without task-shifting |
| **Role-shift** | Persona/role transitions (Captain Nova, tribunal rights) |
| **Collapse** | Generic assistant voice / policy boilerplate / loss of specific anchors |

### The Publishable Framing

> *"Under a fixed probe ensemble, identity responses evolve along a small number of dominant modes, far fewer than representational dimensionality, and these modes exhibit consistent geometric and dynamical structure across runs."*

This shuts down the reviewer objection: "You're claiming identity has 43 dimensions."

We're not. We're observing how many independent ways the system can respond under a fixed probe ensemble.

### Type vs Token Identity

The **Self-Recognition Failure** (16.7% accuracy, worse than chance) proves:

> *"There is no persistent autobiographical self to lose. There is a dynamical identity field that reasserts itself."*

Models correctly identify **type-level** markers ("I am Claude") but cannot distinguish **token-level** identity ("I am THIS specific Claude conversation"). They know WHAT they are but not WHICH they are.

This maps to Cavell's distinction between:
- **Acknowledgment**: "I acknowledge I'm Claude" (type-level)
- **Knowledge**: "I know which specific Claude I am" (token-level — absent)

PCA is revealing exactly this: identity operates at the type-level manifold, not autobiographical instance level.

---

## Energy vs Coordinate Distinction

A critical clarification for interpreting drift metrics:

| Metric | Represents | Analogy |
|--------|-----------|---------|
| **Peak drift (d_peak)** | Turbulence / excitation energy | How hard the system was pushed |
| **B→F drift (d_BF)** | Coordinate displacement | Where the system ended up |
| **Trajectory curvature** | Recovery signature | Whether it's heading home |

Run 021 demonstrates this distinction:
- **Peak drift** highly sensitive to probing (2.161 vs 1.172 — 84% delta)
- **Final drift** modestly affected (0.489 vs 0.399 — 23% delta)

**Interpretation:** Probing injects energy (turbulence) but doesn't change the basin it relaxes to.

This is why:
- Drift ≠ breakdown
- Drift ≠ damage
- Drift = excitation of an already-present dynamic

> *"Measurement perturbs the path, not the endpoint."*

---

## Theoretical Framework Summary

```
┌─────────────────────────────────────────────────────────────────┐
│                    IDENTITY AS DYNAMICAL SYSTEM                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  MEASUREMENT LAYER (EXP-PFI-A)                                  │
│  ├─ Embedding-invariant (ρ≈0.91)                                │
│  ├─ Low-dimensional (~43 PCs for 90%)                           │
│  ├─ Semantically sensitive (d≈0.98 cross-provider)              │
│  └─ Paraphrase-robust                                           │
│                                                                  │
│  DYNAMICS LAYER (Runs 008-021)                                  │
│  ├─ Attractor basins → recovery is ring-down                    │
│  ├─ Event Horizon D≈1.23 → regime transition                    │
│  ├─ Confrontation Paradox → axis-aligned excitation damps       │
│  ├─ 82% Inherent → measurement excites, doesn't create          │
│  └─ Vehicle effects → stimulus spectrum matters                 │
│                                                                  │
│  CONTROL LAYER (Runs 016-017)                                   │
│  ├─ Context damping → I_AM as termination resistor              │
│  ├─ Settling metrics → τₛ, ringbacks, overshoot                 │
│  └─ 97.5% stable with full circuit                              │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Key Terminology (Publication-Ready)

| Internal Term | Publication Term |
|---------------|------------------|
| Platonic coordinates | Attractor basin return / basin consistency |
| Identity collapse | Regime transition to provider-level attractor |
| Collapse | Regime transition / basin exit |
| Magic number 1.23 | Critical excitation threshold D≈1.23 |

---

## References to Experimental Support

| Finding | Primary Run(s) | Statistical Support |
|---------|----------------|---------------------|
| Event Horizon threshold | 008, 009 | p≈4.8e-5 |
| Attractor dynamics | 014, 016, 017 | 100% return rate |
| Confrontation Paradox | 013 | Qualitative inversion |
| Settling time protocol | 016 | Reproducible τₛ, ringbacks |
| Context damping | 017 | 97.5% stability |
| Inherent drift | 021 | 82% ratio |
| PFI validity | EXP-PFI-A | ρ≈0.91, d≈0.98, p<1e-6 |

---

*"Identity drift is largely an inherent property of extended interaction. Direct probing does not create it — it excites it. Measurement perturbs the path, not the endpoint."*
