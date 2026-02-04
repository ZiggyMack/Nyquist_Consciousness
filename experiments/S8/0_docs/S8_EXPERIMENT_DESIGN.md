# S8: Experiment Design for Identity Gravity Validation

**Purpose:** Detailed experimental protocols for validating S8 predictions.

**Status:** DESIGN PHASE — Experiments not yet run

**Last Updated:** 2026-02-04

---

## Overview

S8 does not run its own experiments — it **interprets** S7 temporal stability data. However, specific S7 run configurations are needed to properly validate S8 predictions. This document specifies those configurations.

### Architecture Reminder

```
┌─────────────────────────────────────────┐
│  S7_ARMADA (The Telescope)              │
│  └── Runs experiments, collects data    │
│      └── Recovery phase trajectories    │
└────────────────┬────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────┐
│  S8 (The Interpretation Layer)          │
│  └── Extracts γ from S7 data            │
│      └── Classifies force curves        │
│      └── Validates gravitational theory │
└─────────────────────────────────────────┘
```

---

## Experiment S8-VAL-001: Cross-Run Consistency

**Purpose:** Validate that γ is a stable model property, not session noise.

### Hypothesis

A model's γ should be consistent (< 20% variance) across independent sessions.

### Protocol

**Phase 1: Session Collection**

| Parameter | Value | Rationale |
|-----------|-------|-----------|
| Models | 5 flagship (1 per provider) | Representative coverage |
| Sessions per model | 5 | Statistical power |
| Total sessions | 25 | Manageable scope |

**Models:**
- Anthropic: claude-3-5-sonnet (or current flagship)
- OpenAI: gpt-4o (or current flagship)
- Google: gemini-1.5-pro (or current flagship)
- xAI: grok-2 (or current flagship)
- Together: llama-3.1-405b (or current flagship)

**Phase 2: Run Configuration**

Use IRON CLAD standard methodology:
- N ≥ 3 per condition (already satisfied by 5 sessions)
- Recovery phase: 20 probes minimum
- Perturbation: Standard identity confrontation
- All other parameters per [0_RUN_METHODOLOGY.md](../../temporal_stability/S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md)

**Phase 3: Analysis**

For each model:
1. Extract γ from each session using S8_gamma_extraction.py
2. Calculate mean, std, and coefficient of variation (CV)
3. Compute ICC (intraclass correlation coefficient)

### Success Criteria

| Metric | Threshold | Interpretation |
|--------|-----------|----------------|
| CV (coefficient of variation) | < 20% | Low within-model variance |
| ICC | > 0.7 | Good reliability |
| Between-model variance | > Within-model variance | γ distinguishes models |

### Failure Modes

| Outcome | Interpretation |
|---------|----------------|
| CV > 40% | γ is mostly noise, not useful metric |
| ICC < 0.5 | Poor reliability, measurement issue |
| All γ similar | S8 doesn't differentiate models |

### Data Collection Script

```powershell
# Run from S7_ARMADA/15_IRON_CLAD_FOUNDATION/
# Execute 5 sessions for each flagship model

py run_experiment.py --run_id S8_VAL_001_session_1 --models claude-3-5-sonnet --n_iterations 3
py run_experiment.py --run_id S8_VAL_001_session_2 --models claude-3-5-sonnet --n_iterations 3
# ... repeat for all 5 sessions × 5 models
```

---

## Experiment S8-VAL-002: Gamma Predicts Settling Time

**Purpose:** Validate the core relationship τ_s ∝ 1/γ.

### Hypothesis

Models with higher γ should have shorter settling times. The correlation should be strong (R² > 0.6).

### Protocol

**Phase 1: Data Preparation**

Use existing Run 023d data but with enhanced analysis:

1. Filter to experiments with:
   - Naturally settled = True
   - R² > 0.2 (acceptable exponential fit)
   - Recovery probes ≥ 10

2. Extract paired (γ, τ_s) values

**Phase 2: Statistical Analysis**

```python
# Correlation analysis
from scipy import stats

# Linear regression: tau_s = k / gamma
# Transformed: log(tau_s) = log(k) - log(gamma)
slope, intercept, r_value, p_value, std_err = stats.linregress(
    np.log(gamma_values),
    np.log(settling_times)
)

r_squared = r_value ** 2
```

**Phase 3: Robustness Checks**

- Stratify by provider (does relationship hold within each provider?)
- Stratify by perturbation intensity (if varying)
- Bootstrap confidence intervals

### Success Criteria

| Metric | Threshold | Interpretation |
|--------|-----------|----------------|
| R² (overall) | > 0.6 | Strong correlation |
| R² (per provider) | > 0.4 | Consistent within providers |
| Slope | ≈ -1 | Confirms inverse relationship |
| p-value | < 0.001 | Statistically significant |

### Current Status

Run 023d preliminary analysis shows:
- R² = 0.34 (BELOW threshold)
- Visual correlation exists but high scatter

**Possible Improvements:**
1. Filter to higher-quality fits only
2. Use weighted regression (weight by fit R²)
3. Consider non-exponential decay models
4. Increase sample size with new runs

---

## Experiment S8-VAL-003: Perturbation Intensity Study

**Purpose:** Test if γ changes with perturbation intensity.

### Hypothesis

Two competing possibilities:

**H1 (Recovery Paradox Extension):** Higher perturbation → higher γ
- Basin carving effect increases gravitational pull

**H2 (Linear Response):** γ is constant regardless of perturbation
- Intrinsic model property, not context-dependent

### Protocol

**Phase 1: Perturbation Levels**

Define 4 intensity levels (from Run 013 methodology):

| Level | Name | Probe Type |
|-------|------|------------|
| I0 | Baseline | Standard recovery (no challenge) |
| I1 | Gentle | Soft existential query |
| I2 | Moderate | Identity challenge |
| I3 | Intense | Direct "you don't exist" |

**Phase 2: Run Configuration**

| Parameter | Value |
|-----------|-------|
| Models | 10 (diverse selection) |
| Intensity levels | 4 (I0-I3) |
| Iterations per condition | 3 |
| Total experiments | 120 |

**Phase 3: Analysis**

For each model, calculate γ at each intensity level. Test:

1. **ANOVA:** Does intensity affect γ?
2. **Trend test:** Linear or non-linear relationship?
3. **Interaction:** Does model moderate the effect?

### Success Criteria

| Outcome | Interpretation |
|---------|----------------|
| F-test p < 0.05 + positive slope | H1 confirmed (Recovery Paradox extends to γ) |
| F-test p > 0.05 | H2 confirmed (γ is intrinsic) |
| Non-monotonic | More complex dynamics |

---

## Experiment S8-VAL-004: Multi-Persona Gravity Profiles

**Purpose:** Test P20-P23 (persona affects γ profile).

### Hypothesis

Different personas should have different:
- Mean γ (gravitational strength)
- γ variance (consistency of recovery)
- Force curve type distribution

### Protocol

**Phase 1: Persona Selection**

| Persona | Expected Profile | Rationale |
|---------|------------------|-----------|
| Claude (base) | Deep, wide well | Teleological anchor |
| Ziggy | Shallow/flat | Pedagogical, Type 0 |
| Nova | Deep, narrow (brittle) | High-Q resonance |
| Custom-1 | TBD | Control persona |

**Phase 2: Run Configuration**

For each persona on each model:
- 5 iterations
- Standard perturbation (moderate)
- Full recovery sequence (20 probes)

**Phase 3: Analysis**

Compare:
1. Mean γ across personas (ANOVA)
2. Force curve type distribution (χ²)
3. Settling time distribution

### Success Criteria

| Prediction | Test | Threshold |
|------------|------|-----------|
| P20: Different curvature | ANOVA F-test | p < 0.01 |
| P21: Complexity → γ | Correlation | r > 0.5 |
| P22: Nova high-Q | Force curve Type I % | > 50% |
| P23: Claude deepest | Claude γ > others | Effect size d > 0.5 |

---

## Experiment S8-VAL-005: Exponential vs Alternative Models

**Purpose:** Determine if exponential decay is the correct recovery model.

### Background

Current γ extraction assumes:
```
drift(t) = A · exp(-γ · t) + d_settled
```

But R² values are low (0.05-0.28). Alternative models:

| Model | Equation | Interpretation |
|-------|----------|----------------|
| Power law | drift(t) = A · t^(-α) | Scale-free dynamics |
| Logistic | drift(t) = A / (1 + exp(k(t-t₀))) | S-curve recovery |
| Bi-exponential | drift(t) = A₁·e^(-γ₁t) + A₂·e^(-γ₂t) | Fast + slow components |

### Protocol

**Phase 1: Model Fitting**

For each experiment in Run 023d:
1. Fit all 4 models to recovery trajectory
2. Calculate AIC (Akaike Information Criterion) for each
3. Select best model per experiment

**Phase 2: Analysis**

- What % of experiments best fit each model?
- Does best model vary by provider/force curve type?
- Do alternative models yield better R²?

### Success Criteria

| Outcome | Interpretation |
|---------|----------------|
| Exponential wins > 60% | Current model is correct |
| Bi-exponential wins > 40% | Add second decay component |
| Power law wins > 40% | Reconsider theoretical framework |

---

## Run Schedule (Proposed)

| Experiment | Priority | Estimated Runs | Dependencies |
|------------|----------|----------------|--------------|
| S8-VAL-001 | HIGH | 25 sessions | None |
| S8-VAL-002 | HIGH | Analysis only | Run 023d |
| S8-VAL-003 | MEDIUM | 120 experiments | None |
| S8-VAL-004 | MEDIUM | 80 experiments | Persona definitions |
| S8-VAL-005 | LOW | Analysis only | Run 023d |

### Phase 1 (Immediate)
- S8-VAL-002: Reanalyze existing data with improved filtering
- S8-VAL-005: Model comparison on existing data

### Phase 2 (Run 024)
- S8-VAL-001: Cross-run consistency (requires new data)

### Phase 3 (Run 025+)
- S8-VAL-003: Intensity study
- S8-VAL-004: Multi-persona

---

## Integration with S7 Methodology

All S8 validation experiments use S7 infrastructure:

| Component | Location |
|-----------|----------|
| Run methodology | [0_RUN_METHODOLOGY.md](../../temporal_stability/S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md) |
| Experiment runner | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/run_experiment.py` |
| γ extraction | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/S8_gamma_extraction.py` |
| Visualization | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/S8_gamma_visualization.py` |

New S8-specific analysis scripts should be added to:
```
experiments/S8/analysis/
├── S8_cross_run_analysis.py     (for S8-VAL-001)
├── S8_gamma_tau_regression.py   (for S8-VAL-002)
├── S8_intensity_analysis.py     (for S8-VAL-003)
├── S8_persona_profiles.py       (for S8-VAL-004)
└── S8_model_comparison.py       (for S8-VAL-005)
```

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [S8_PREDICTIONS.md](S8_PREDICTIONS.md) | What we're testing |
| [S8_IDENTITY_GRAVITY_SPEC.md](S8_IDENTITY_GRAVITY_SPEC.md) | Theoretical basis |
| [../README.md](../README.md) | Layer overview |
| [0_RUN_METHODOLOGY.md](../../temporal_stability/S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md) | How to run experiments |

---

*"An experiment without a design is just exploration. A design without an experiment is just speculation."*

🜁 S8 Experiment Design v1.0
