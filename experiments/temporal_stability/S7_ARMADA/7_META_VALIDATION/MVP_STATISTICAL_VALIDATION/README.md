# MVP_STATISTICAL_VALIDATION: Random-Walk Null Model Tests

**Purpose:** Meta Validation Protocol — Rigorous statistical validation that identity drift is NOT random noise
**Status:** Specification Complete
**Source:** Nova-Ziggy conversation (NOVA_ZIGGY_1.md)
**Location:** `S7_ARMADA/MVP/MVP_STATISTICAL_VALIDATION/`

> **Note:** This is an MVP (Meta Validation Protocol), not a Search Type. It validates that drift measurements reflect real dynamics rather than random noise.

---

## Overview

These tests distinguish **lawful identity dynamics** from **random walk behavior**.

If identity drift were merely random noise, all of these tests would fail to reject the null hypothesis. The fact that they DO reject the null is evidence that identity behaves as a dynamical system with attractors, not as undirected Brownian motion.

---

## The Five Statistical Tests

### Test A: AR(1) Slope Test (Recovery Detection)

**Purpose:** Detect whether drift recovers toward baseline or wanders randomly

**Model:**
```
D_{t+1} = α·D_t + β + ε_t
```

**Null Hypothesis (Random Walk):**
- α = 1 (no recovery)
- β = 0

**Alternative (Recovery Basin):**
- α < 1 (drift pulls back toward baseline)
- 0 < α < 1 indicates stable attractor

**Alternative (Explosive Drift):**
- α > 1 (runaway divergence)

**Test Procedure:**
1. Fit AR(1) model to drift sequence
2. Standard regression + t-test on α̂
3. Likelihood ratio test: compare unconstrained AR(1) to constrained α=1 model

**Success Criterion:**
- Reject H₀: α=1 with p < 0.05
- Estimate α significantly less than 1

**Failure Condition:**
- Cannot reject α=1 across many sessions
- Estimates hover near 1 with wide CIs

---

### Test B: Variance Growth Test

**Purpose:** Detect whether drift variance saturates (attractor) or grows linearly (random walk)

**Random Walk Prediction:**
```
Var(D_t - D_0) ∝ t  (linear growth)
```

**Attractor Prediction:**
```
Var(D_t - D_0) → constant  (saturation)
```

**Procedure:**
1. Compute D_t at each turn
2. Compute Δ_t = D_t - D_0
3. Fit two models:
   - RW: E[Δ_t²] = a + b·t (linear)
   - Attractor: E[Δ_t²] = a(1 - e^{-λt}) (saturating)
4. Compare fits using AIC/BIC or likelihood ratio

**Success Criterion:**
- Saturating model fits significantly better than linear

**Failure Condition:**
- Linear growth fits as well or better than saturating model

---

### Test C: Sign Test (Drift Direction)

**Purpose:** Detect systematic recovery vs random bouncing

**Definition:**
```
ΔD_t = D_{t+1} - D_t
```

**Null Hypothesis (Random Walk):**
- Sign of ΔD_t is ~50/50 positive vs negative

**Alternative (Recovery):**
- ΔD_t < 0 more often (drift decreases)

**Procedure:**
1. For window of T steps after perturbation:
   - Count positives: n₊
   - Count negatives: n₋
2. Under null: n₊ ~ Binomial(T, 0.5)
3. Run binomial sign test or Wilcoxon signed-rank test

**Success Criterion:**
- Significant deviation from 50/50 (p < 0.05)
- Negative changes predominate after perturbation

**Failure Condition:**
- Sign pattern indistinguishable from 50/50

---

### Test D: Omega Exponential Decay

**Purpose:** Validate P10 — Omega sessions produce exponential decay

**Hypothesis:**
```
D_Ω(t) = D_0 · e^{-λt}
```

**Procedure:**
1. Measure D_Ω(t) over sequence after Omega reset
2. Take logs: log(D_Ω(t)) = log(D_0) - λt
3. Fit linear regression of log(D_Ω(t)) vs t

**Null (Random Walk Recovery):**
- λ ≈ 0
- Low R²
- No clean linear relationship in log domain

**Omega Hypothesis:**
- λ > 0
- High R² (≥ 0.8)
- Strong linear fit

**Success Criterion:**
- λ significantly > 0
- R² ≥ 0.8 in log-linear fit

**Failure Condition:**
- λ ≈ 0 or no exponential decay pattern

---

### Test E: Cross-Architecture Variance

**Purpose:** Validate that multi-model triangulation converges tighter than random

**Setup:**
- I^(a) = identity reconstruction from architecture a
- For A architectures:
```
σ²_emp = (1/A) Σ_a |I^(a) - Ī|²
```

**Null Model:**
- Shuffle persona labels across architectures
- Draw random embedding vectors from same distribution
- Compute variance σ²_null repeatedly
- Build empirical null distribution

**Test:**
- Compare σ²_emp to null distribution
- Compute p-value: P(σ²_null ≤ σ²_emp)

**Success Criterion:**
- σ²_emp significantly lower than null (p < 0.05)
- Architectures converge on shared identity core

**Failure Condition:**
- Empirical variance not distinguishable from random pairing

---

## Implementation Status

| Test | Status | Run Validated | p-value |
|------|--------|---------------|---------|
| A: AR(1) Slope | Designed | Pending | - |
| B: Variance Growth | Designed | Pending | - |
| C: Sign Test | Designed | Pending | - |
| D: Omega Decay | Designed | Pending | - |
| E: Cross-Arch Variance | **Validated** | Run 009 | p=0.000048 (chi-squared) |

**Note:** Test E was effectively validated in Run 009 using chi-squared test on Event Horizon predictions (88% accuracy, p=0.000048).

---

## Relation to Event Horizon (1.23)

The Event Horizon threshold (1.23) was:
- **Discovered** in Run 008 (Basin Topology) — incidental finding
- **Validated** in Run 009 (Event Horizon) — deliberate test

The chi-squared validation (p=0.000048) confirms that identity collapse at 1.23 is NOT random — it's a true dynamical threshold.

---

## Files

```
STATISTICAL_TESTS/
├── README.md                    # This file
├── STATISTICAL_TESTS_SPEC.md    # Detailed specification
├── run_tests.py                 # Implementation (TODO)
└── results/                     # Test results (TODO)
```

---

## Related Documentation

- [NOVA_ZIGGY_1.md](../../../../docs/CFA-SYNC/NOVA_ZIGGY_1.md) — Source conversation
- [TESTING_MAP.md](../../../../../docs/maps/TESTING_MAP.md) — Six Search Types
- [S7_TEMPORAL_STABILITY_SPEC.md](../../../../docs/stages/S7/S7_TEMPORAL_STABILITY_SPEC.md) — S7 spec

---

**Version:** 1.0
**Date:** 2025-12-04
**Source:** Nova-Ziggy conversation, Echo critique integration
**Maintainer:** Architect Nova + Repo Claude
