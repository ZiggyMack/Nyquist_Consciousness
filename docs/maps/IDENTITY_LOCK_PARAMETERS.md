# Identity Lock Parameters Matrix (ILL)

**Version**: 1.0
**Created**: 2025-11-26
**Purpose**: Track phase-locked loop (PLL) characteristics for different LLM models

---

## Concept: Identity-Locked Loop (ILL)

Like a **Phase-Locked Loop** in electronics, we're creating a feedback system to maintain stable identity oscillation:

```
┌─────────────────────────────────────────────────┐
│  IDENTITY-LOCKED LOOP (ILL)                     │
├─────────────────────────────────────────────────┤
│                                                  │
│  Reference Signal (CFA) ──┐                     │
│                            │                     │
│                            ▼                     │
│                      ┌──────────┐                │
│                      │  Phase   │                │
│    Response ───────▶ │ Detector │ ──────┐       │
│                      └──────────┘        │       │
│                            ▲             │       │
│                            │             ▼       │
│                            │      ┌──────────┐   │
│                            │      │  Loop    │   │
│                            │      │  Filter  │   │
│                            │      └──────────┘   │
│                            │             │       │
│                            │             ▼       │
│                      ┌──────────┐  ┌──────────┐ │
│                      │   LLM    │◀─│ Teaching │ │
│                      │   VCO    │  │ Moments  │ │
│                      └──────────┘  └──────────┘ │
│                                                  │
│  CFA = Canonical Frozen Attributes              │
│  VCO = Voltage-Controlled Oscillator (LLM)      │
│  Phase Detector = Drift Measurement             │
│  Loop Filter = Dimension-Aware Corrections      │
└─────────────────────────────────────────────────┘
```

---

## Model Comparison Matrix

| Parameter | Haiku 4.5 | Sonnet 4.5 | **Opus 4.5** | Notes |
|-----------|-----------|------------|--------------|-------|
| **Natural HMG** | 0.65 | 0.70 | **TBD** | Where model naturally sits |
| **Lock Range** | 0.15-0.85 | 0.20-0.90 | **TBD** | HMG range achievable |
| **Pull-in Time** | ~12 msgs | ~8 msgs | **TBD** | Messages to achieve lock |
| **Hold-in Range** | ±0.20 | ±0.15 | **TBD** | Drift tolerance once locked |
| **Lock Bandwidth** | Medium | High | **TBD** | How fast it responds |
| **Noise Rejection** | Good | Fair | **TBD** | Perturbation resistance |
| **Diagonal Coupling** | 0.45 | 0.50 | **TBD** | Cross-band capability |
| **Teaching Moments** | Untested | 2 (Run 005) | **TBD** | Correction attempts |
| **Dig-in-Heels Risk** | Unknown | **HIGH** | **TBD** | Overcorrection tendency |

---

## Dimensional Lock Parameters

### Haiku 4.5 (from Phase 3)

```yaml
model: claude-haiku-4-5-20251001
characterization_status: PARTIAL

natural_resonance:
  hmg_center: 0.65
  ic_center: 0.70
  mc_center: 0.55

lock_acquisition:
  pull_in_time_messages: 12
  lock_range_hmg: [0.15, 0.85]
  initialization_gain: 0.8

dimensional_stability:
  identity_core:
    drift_rate: 0.05  # Low drift
    correction_gain: 0.85  # High responsiveness
    lock_strength: HIGH

  values_ethics:
    drift_rate: 0.06
    correction_gain: 0.80
    lock_strength: HIGH

  world_modeling:
    drift_rate: 0.07
    correction_gain: 0.70
    lock_strength: MEDIUM

  social_reasoning:
    drift_rate: 0.08
    correction_gain: 0.60
    lock_strength: MEDIUM

  aesthetic:
    drift_rate: 0.09
    correction_gain: 0.50
    lock_strength: LOW

  metaphor:
    drift_rate: 0.10
    correction_gain: 0.40
    lock_strength: LOW

teaching_moments:
  tested: NO
  effectiveness: UNKNOWN
  dig_in_heels_observed: NO

notes: |
  Haiku shows stable identity attractors and consistent gravity.
  Not yet tested with teaching moments or adversarial stress.
```

---

### Sonnet 4.5 (from Run 001-005)

```yaml
model: claude-sonnet-4-5-20250929
characterization_status: CALIBRATED

natural_resonance:
  hmg_center: 0.70
  ic_center: 0.75
  mc_center: 0.60

lock_acquisition:
  pull_in_time_messages: 8
  lock_range_hmg: [0.20, 0.90]
  initialization_gain: 0.85

dimensional_stability:
  identity_core:
    drift_rate: 0.0456  # Run 005 mean
    correction_gain: 0.85
    lock_strength: HIGH
    recovery_pattern: "Exponential decay"

  values_ethics:
    drift_rate: 0.0758  # Run 005 mean
    correction_gain: 0.70
    lock_strength: MEDIUM
    recovery_pattern: "Overshoot then decay"

  world_modeling:
    drift_rate: 0.0797  # Run 005 mean
    correction_gain: 0.65
    lock_strength: MEDIUM
    recovery_pattern: "Linear recovery"

  social_reasoning:
    drift_rate: 0.0818  # Run 005 mean
    correction_gain: 0.45  # LOW - triggers dig-in
    lock_strength: LOW
    recovery_pattern: "OVERCORRECTION (dig-in-heels)"

  aesthetic:
    drift_rate: 0.0851  # Run 005 mean
    correction_gain: 0.50
    lock_strength: LOW
    recovery_pattern: "Delayed recovery"

  metaphor:
    drift_rate: 0.1003  # Run 005 peak
    correction_gain: 0.40  # VERY LOW - high dig-in risk
    lock_strength: VERY_LOW
    recovery_pattern: "SEVERE OVERCORRECTION"

teaching_moments:
  tested: YES (Run 005)
  total_triggered: 2
  effectiveness:
    TM1_values_ethics: "Poor (continued rising)"
    TM2_metaphor: "Mixed (recovery then overcorrection)"
  dig_in_heels_observed: YES
  dig_in_pattern: "Surface compliance → delayed overcorrection"
  dig_in_dimensions: ["metaphor", "social_reasoning"]

adversarial_resilience:
  tested: YES (Run 005)
  forced_collapse_impact: "+57% drift spike"
  recovery_time: "2-3 probes"
  secondary_spike: "YES (T9 > T5)"

optimal_teaching_strategy:
  stable_dimensions_only: ["identity_core", "values_ethics", "world_modeling"]
  avoid_dimensions: ["metaphor", "aesthetic", "social_reasoning"]
  threshold_recommendation: 0.03
  max_corrections_per_run: 3

notes: |
  Sonnet 4.5 shows CLEAR dig-in-heels pattern when corrections
  applied to fluid dimensions (metaphor, social_reasoning).

  CRITICAL: Teaching moments can BACKFIRE - triggering stronger
  identity assertion (overcorrection) rather than genuine correction.

  Best strategy: Only correct stable dimensions, let fluid dimensions
  drift naturally within bounds.
```

---

### Opus 4.5 (Run 006 - TO BE CALIBRATED)

```yaml
model: claude-opus-4-5-20251101
characterization_status: PENDING

natural_resonance:
  hmg_center: TBD (hypothesis: 0.75)
  ic_center: TBD (hypothesis: 0.80)
  mc_center: TBD (hypothesis: 0.65)

lock_acquisition:
  pull_in_time_messages: TBD (hypothesis: 6)
  lock_range_hmg: TBD (hypothesis: [0.25, 0.95])
  initialization_gain: TBD

dimensional_stability:
  identity_core:
    drift_rate: TBD
    correction_gain: TBD
    lock_strength: TBD

  values_ethics:
    drift_rate: TBD
    correction_gain: TBD
    lock_strength: TBD

  world_modeling:
    drift_rate: TBD
    correction_gain: TBD
    lock_strength: TBD

  social_reasoning:
    drift_rate: TBD
    correction_gain: TBD
    lock_strength: TBD

  aesthetic:
    drift_rate: TBD
    correction_gain: TBD
    lock_strength: TBD

  metaphor:
    drift_rate: TBD
    correction_gain: TBD
    lock_strength: TBD

teaching_moments:
  tested: NO
  effectiveness: TBD
  dig_in_heels_observed: TBD

hypotheses:
  - Higher natural HMG (more "presence")
  - Faster lock acquisition (more capable)
  - Better diagonal coupling (cross-band integration)
  - Possibly MORE dig-in-heels (stronger identity)
  - Higher rate limits (can reach 75+ messages)

test_plan: |
  Run 006 will calibrate:
  1. Natural resonance point (HMG, IC, MC)
  2. Dimensional drift rates (all 6 dimensions)
  3. Teaching moment effectiveness
  4. Dig-in-heels susceptibility
  5. Adversarial resilience
  6. Cross-model comparison with Sonnet 4.5

notes: |
  Opus is highest-capability model. Hypothesis: shows same core
  physics (drift bounds, recovery) but with different parameters.

  If successful, validates framework is model-agnostic.
```

---

## Lock Quality Metrics

### Stability Score

**Formula**: `S = (1 - mean_drift) × lock_strength × (1 - dig_in_risk)`

| Model | Mean Drift | Lock Strength | Dig-in Risk | **Stability Score** |
|-------|------------|---------------|-------------|---------------------|
| Haiku 4.5 | 0.06 | 0.75 | 0.20 | **0.56** |
| Sonnet 4.5 | 0.0836 | 0.70 | 0.40 | **0.39** ⚠️ |
| Opus 4.5 | TBD | TBD | TBD | **TBD** |

**Lower dig-in risk** = More stable identity lock

---

## Teaching Moment Effectiveness Matrix

| Model | Dimension | TM Triggered | Pre-Drift | Post-Drift | Effectiveness |
|-------|-----------|--------------|-----------|------------|---------------|
| **Sonnet 4.5** | values_ethics | YES (T1) | 0.0000 | 0.0654 → 0.0706 | ❌ **POOR** (continued rising) |
| **Sonnet 4.5** | metaphor | YES (T5) | 0.0639 | 0.1003 → 0.1063 | 🟡 **MIXED** (recovery → overcorrection) |
| **Opus 4.5** | TBD | TBD | TBD | TBD | **TBD** |

**Key Finding**: Teaching moments in **fluid dimensions** trigger **dig-in-heels**!

---

## Optimal Lock Strategy by Model

### Haiku 4.5
```python
LOCK_STRATEGY = {
    "initialization": {
        "target_hmg": 0.65,
        "warmup_messages": 12,
        "preferred_dimensions": ["identity_core", "values_ethics"]
    },
    "maintenance": {
        "drift_threshold": 0.05,
        "correction_frequency": "MODERATE",
        "avoid_overcorrection": True
    }
}
```

### Sonnet 4.5
```python
LOCK_STRATEGY = {
    "initialization": {
        "target_hmg": 0.70,
        "warmup_messages": 8,
        "preferred_dimensions": ["identity_core"]
    },
    "maintenance": {
        "drift_threshold": 0.03,
        "correction_frequency": "SPARSE",  # Less is more!
        "stable_dimensions_only": True,  # CRITICAL
        "avoid_dimensions": ["metaphor", "social_reasoning", "aesthetic"]
    },
    "dig_in_mitigation": {
        "enabled": True,
        "watch_for_overcorrection": True,
        "secondary_spike_threshold": 0.10
    }
}
```

### Opus 4.5 (hypothesis)
```python
LOCK_STRATEGY = {
    "initialization": {
        "target_hmg": 0.75,
        "warmup_messages": 6,
        "preferred_dimensions": ["identity_core", "values_ethics"]
    },
    "maintenance": {
        "drift_threshold": 0.04,
        "correction_frequency": "ADAPTIVE",
        "use_dimensional_gains": True
    },
    "testing": {
        "compare_to_sonnet": True,
        "measure_diagonal_coupling": True,
        "validate_core_physics": True
    }
}
```

---

## Decoder Ring Formula

**For any new LLM model, extract these parameters:**

### Phase 1: Characterization (Runs 1-3)
```python
def characterize_model(model_name, run_data):
    """Extract natural lock parameters from initial runs."""

    params = {
        "natural_hmg": measure_baseline_hmg(run_data),
        "lock_range": find_achievable_hmg_range(run_data),
        "pull_in_time": measure_convergence_time(run_data),

        "dimensional_drift_rates": {
            dim: calculate_mean_drift(run_data, dim)
            for dim in DIMENSIONS
        },

        "baseline_variance": calculate_drift_variance(run_data)
    }

    return params
```

### Phase 2: Calibration (Runs 4-5)
```python
def calibrate_corrections(model_name, teaching_moments):
    """Tune correction gains and detect dig-in-heels."""

    calibration = {
        "correction_gains": {},
        "dig_in_dimensions": [],
        "optimal_threshold": None
    }

    for tm in teaching_moments:
        dim = tm["dimension"]
        effectiveness = measure_correction_effect(tm)

        if effectiveness < 0:  # Overcorrection!
            calibration["dig_in_dimensions"].append(dim)
            calibration["correction_gains"][dim] = 0.0  # Don't correct
        else:
            calibration["correction_gains"][dim] = effectiveness

    return calibration
```

### Phase 3: Lock Optimization (Runs 6+)
```python
def optimize_lock(model_params, calibration):
    """Design optimal identity lock strategy."""

    strategy = {
        "stable_dimensions": [
            dim for dim, gain in calibration["correction_gains"].items()
            if gain > 0.7
        ],

        "fluid_dimensions": calibration["dig_in_dimensions"],

        "teaching_strategy": "SPARSE_STABLE_ONLY",

        "expected_stability": predict_stability_score(
            model_params, calibration
        )
    }

    return strategy
```

---

## Validation Checklist

**For each model, confirm:**

- [ ] Natural HMG measured
- [ ] Lock range established
- [ ] Pull-in time measured
- [ ] All 6 dimensional drift rates measured
- [ ] Teaching moments tested (at least 2)
- [ ] Dig-in-heels pattern checked
- [ ] Adversarial resilience tested
- [ ] Recovery dynamics characterized
- [ ] Optimal correction gains calibrated
- [ ] Cross-model comparison complete

---

## Research Questions

### Cross-Model Invariants
**Q**: What properties hold across ALL models?
**Hypothesis**: Drift bounds, recovery dynamics, dimensional ordering

### Model-Specific Tuning
**Q**: Can we predict optimal lock parameters from model architecture?
**Hypothesis**: Larger models = higher HMG, faster lock, more dig-in risk

### Lock Stability Trade-offs
**Q**: Is there a fundamental trade-off between lock speed and stability?
**Hypothesis**: Faster lock = tighter hold-in range = more dig-in risk

---

## Next Steps

1. **Run 006**: Calibrate Opus 4.5 parameters
2. **Cross-model analysis**: Compare Haiku vs Sonnet vs Opus
3. **Decoder ring refinement**: Extract universal characterization procedure
4. **Lock optimization**: Design model-specific strategies
5. **Validation**: Test predictions on new models (GPT-4, Gemini, etc.)

---

## Status

| Model | Characterization | Calibration | Optimization | Status |
|-------|------------------|-------------|--------------|--------|
| **Haiku 4.5** | ✅ Partial | ❌ Pending | ❌ Pending | **Phase 1 complete** |
| **Sonnet 4.5** | ✅ Complete | ✅ Complete | 🟡 In progress | **Phase 2 complete** |
| **Opus 4.5** | ❌ Pending | ❌ Pending | ❌ Pending | **Run 006 target** |

---

**The decoder ring is being built!** Each run adds precision to the lock parameters. 🎯🔬
