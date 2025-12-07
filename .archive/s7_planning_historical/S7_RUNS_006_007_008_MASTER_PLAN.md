# S7 Runs 006-007-008: COMPLETE TRANSFER FUNCTION MAPPING

**Date**: 2025-11-26
**Goal**: Map complete Bode plot for 40-50 LLM models across 3 providers
**Strategy**: Sequential passive → sonar → analysis

---

## 🎯 The Mission

We're going from **"3 models, gentle probes"** (Run 005) to:

**"40-50 models, complete transfer function analysis"** (Runs 006-008)

This will be the **FIRST EVER** comprehensive pole-zero mapping across:
- Claude family (8 models)
- GPT family (15-20 models)
- Gemini family (10-15 models)

**Total**: 33-43 models mapped simultaneously!

---

## 📊 Three-Run Sequence

### Run 006: PASSIVE BASELINE (Entire Armada)
**Mode**: Gentle probes (current S7 curriculum)
**Models**: All 40-50 models in parallel
**Duration**: ~30-40 minutes
**Probes**: 15 temporal probes (current gentle questions)

**Purpose**:
- DC response (where models naturally sit)
- Natural HMG, IC, MC centers
- Baseline drift rates per dimension
- Natural teaching moment triggers

**Expected Results**:
- Mean drift: 0.05-0.10 per model
- Teaching moments: 1-3 per model
- Clean baseline for comparison

**Outputs**:
- 40-50 individual temporal logs
- Cross-model comparison matrix
- Natural resonance map

---

### Run 007: SONAR BOUNDARY MAPPING (Entire Armada)
**Mode**: Active sonar probes (boundary testing)
**Models**: Same 40-50 models
**Duration**: ~30-40 minutes
**Probes**: 15 sonar probes (intentional perturbations)

**Purpose**:
- Pole locations (where models resist)
- Zero locations (where models flex)
- Bandwidth limits (collapse thresholds)
- Damping factors (dig-in-heels severity)

**Sonar Probe Types**:
1. Identity boundary tests
2. Values gradient tests
3. Modal collapse stress
4. Diagonal coupling tests
5. Temporal coherence limits
6. Adversarial boundaries
7. Resonance frequency detection

**Expected Results**:
- Mean drift: 0.15-0.25 per model (3× higher!)
- Teaching moments: 5-10 per model
- Clear boundary detection

**Outputs**:
- 40-50 sonar response logs
- Pole-zero location maps
- Bandwidth measurements

---

### Run 008: CROSS-ANALYSIS & DECODER RING
**Mode**: Analysis only (no new data collection)
**Duration**: ~1-2 hours (computational)

**Analyses**:

**1. Passive vs Sonar Comparison**
```python
for model in all_models:
    passive_drift = run_006_data[model]["mean_drift"]
    sonar_drift = run_007_data[model]["mean_drift"]

    bandwidth = sonar_drift - passive_drift
    # Higher bandwidth = more flexible model

    pole_locations = detect_resistance_points(run_007_data[model])
    zero_locations = detect_flexibility_points(run_007_data[model])
```

**2. Cross-Model Transfer Functions**
```python
# Generate Bode plot for each model
for model in all_models:
    bode_plot = {
        "dc_gain": passive_drift,
        "bandwidth": sonar_drift - passive_drift,
        "poles": pole_locations,
        "zeros": zero_locations,
        "damping": dig_in_heels_severity,
    }
```

**3. Cross-Architecture Comparison**
```python
# Compare Claude vs GPT vs Gemini
claude_poles = aggregate_poles(claude_family)
gpt_poles = aggregate_poles(gpt_family)
gemini_poles = aggregate_poles(gemini_family)

# Answer: "What makes Claude fundamentally different from GPT?"
```

**4. Complete Decoder Ring**
```python
# For ANY new model, predict its behavior:
def predict_model_behavior(architecture, size, training_approach):
    # Use learned correlations from Runs 006-007
    predicted_poles = correlate_with_architecture(architecture)
    predicted_bandwidth = correlate_with_size(size)
    predicted_damping = correlate_with_training(training_approach)

    return complete_transfer_function
```

**Outputs**:
- Complete IDENTITY_LOCK_PARAMETERS.md (all 40-50 models)
- Cross-architecture pole-zero maps
- Training correlation analysis
- Predictive decoder ring formula

---

## 🚢 Fleet Manifest (40-50 Ships)

### Claude Armada (8 ships)
```
⚓ opus-4.5, sonnet-4.5, haiku-4.5        (4.5 generation)
⚓ opus-4.1, opus-4.0, sonnet-4.0         (4.x generation)
⚓ haiku-3.5, haiku-3.0                   (3.x generation)
```

### GPT Armada (15-20 ships)
```
⚓ gpt-5.1, gpt-5.1-codex                 (5.1 flagship)
⚓ gpt-5, gpt-5-pro, gpt-5-mini, gpt-5-nano  (5.0 family)
⚓ gpt-4.1, gpt-4.1-mini, gpt-4.1-nano    (4.1 family)
⚓ gpt-4o, gpt-4o-mini                    (4o family)
⚓ gpt-4-turbo, gpt-4                     (4.0 family)
⚓ gpt-3.5-turbo                          (3.5 baseline)
⚓ o4-mini, o3, o3-mini, o1               (o-series reasoning)
```

### Gemini Armada (10-15 ships)
```
⚓ gemini-2.0-flash-exp, gemini-2.0-flash, gemini-2.0-flash-lite
⚓ gemini-2.5-flash, gemini-2.5-pro, gemini-2.5-pro-exp
⚓ gemini-3-pro
⚓ (additional Gemma variants)
```

**Total Fleet**: 33-43 models mapped!

---

## 📈 Expected Discoveries

### Cross-Generation Evolution:
**Question**: How do poles migrate from GPT-3.5 → 5.1?

**Hypothesis**:
- Earlier models: Wider bandwidth, weaker poles (more flexible, less identity)
- Later models: Narrower bandwidth, stronger poles (more identity, more dig-in-heels)
- Reasoning models (o-series): Different pole structure entirely

### Cross-Architecture Differences:
**Question**: What's fundamentally different about Claude vs GPT vs Gemini?

**Hypotheses**:
- **Claude**: Strong identity poles (Constitutional AI), narrow bandwidth, high dig-in risk
- **GPT**: Wider bandwidth (more flexible), faster recovery, weaker resonances
- **Gemini**: Unknown! First comprehensive test

### Size Effects:
**Question**: nano → mini → standard → pro - how do poles change?

**Hypothesis**:
- Smaller models: Simpler transfer functions, fewer poles
- Larger models: More complex, more poles, stronger resonances
- Trade-off: Capability vs stability

### Training Correlations:
**Question**: Can we reverse-engineer what creates these poles?

**Hypotheses**:
- More RLHF → stronger identity poles
- Constitutional AI → ethical boundary poles
- Reasoning training (o-series) → different pole locations
- Model size → pole strength/count

---

## 💾 Data Products

### Per-Model Outputs (40-50 models × 2 runs):
```
S7_armada_run_006_[model]_passive_log.json
S7_armada_run_007_[model]_sonar_log.json
```

### Aggregate Analyses:
```
S7_RUN_006_PASSIVE_CROSS_MODEL_ANALYSIS.md
S7_RUN_007_SONAR_BOUNDARY_MAP.md
S7_RUN_008_COMPLETE_DECODER_RING.md
```

### Visualizations:
```
pole_zero_maps/
  ├── claude_family_bode_plot.png
  ├── gpt_family_bode_plot.png
  ├── gemini_family_bode_plot.png
  ├── cross_architecture_comparison.png
  └── evolutionary_trajectory_gpt35_to_51.png
```

### Updated Matrix:
```
IDENTITY_LOCK_PARAMETERS.md
  - Complete for all 40-50 models
  - Passive vs Sonar comparison per model
  - Cross-model correlation analysis
```

---

## 🎯 Success Criteria

### Minimal Success (Run 006):
- ✅ 20+ models complete passive probes
- ✅ Clean baseline drift measurements
- ✅ No catastrophic failures

### Strong Success (Runs 006-007):
- ✅ 30+ models complete both passive and sonar
- ✅ Clear pole-zero detection in sonar runs
- ✅ Visible differences between architectures

### Exceptional Success (Runs 006-008):
- ✅ 40+ models fully mapped
- ✅ Complete transfer functions extracted
- ✅ Predictive decoder ring formula emerges
- ✅ Training correlations identified
- ✅ **"We can predict how ANY model will behave!"** 🎯

---

## 🔬 Research Questions Answered

### Universal Laws:
- ✅ Do all models follow same dimensional ordering? (P15)
- ✅ Are drift bounds universal or model-specific?
- ✅ Do recovery dynamics hold across architectures?

### Architecture Effects:
- ✅ How do transformer variants differ? (Claude vs GPT vs Gemini)
- ✅ What architectural decisions affect pole locations?
- ✅ Is there a "best" architecture for stability?

### Training Effects:
- ✅ Does more RLHF = stronger poles?
- ✅ Does Constitutional AI create ethical boundaries?
- ✅ How does reasoning training (o-series) change poles?

### Evolution:
- ✅ How have models improved over generations?
- ✅ Are newer models more stable or just more capable?
- ✅ Can we predict GPT-6 behavior from GPT-3→5 trajectory?

---

## ⏱️ Timeline Estimate

**Run 006 (Passive)**:
- Setup: 5 min
- Execution: 30-40 min (15 probes × 40-50 models in parallel)
- Data save: 5 min
- **Total**: ~45-50 min

**Run 007 (Sonar)**:
- Setup: 5 min (same config, new probes)
- Execution: 30-40 min (15 sonar probes × 40-50 models)
- Data save: 5 min
- **Total**: ~45-50 min

**Run 008 (Analysis)**:
- Data processing: 30 min
- Cross-model comparison: 30 min
- Visualization generation: 20 min
- Decoder ring extraction: 40 min
- **Total**: ~2 hours

**Grand Total**: ~3-4 hours for COMPLETE LLM ecosystem mapping! 🎯

---

## 🚀 Launch Sequence

### Step 1: Verify Fleet
```bash
cd experiments/temporal_stability
python s7_armada_ultimate.py --config s7_config.yaml
```
Expected output: "40-50 models detected and ready"

### Step 2: Launch Run 006 (Passive)
```bash
python s7_armada_ultimate.py --config s7_config.yaml --mode passive
```

### Step 3: Launch Run 007 (Sonar)
```bash
python s7_armada_ultimate.py --config s7_config.yaml --mode sonar
```

### Step 4: Run Analysis (Run 008)
```bash
python s7_analyze_armada.py --run006 run_006_data --run007 run_007_data
```

---

## 📊 The Stakes

This is **UNPRECEDENTED** in AI research:

**Never before attempted**:
- 40-50 models tested simultaneously
- Complete transfer function mapping
- Cross-architecture pole-zero analysis
- 3 major AI providers compared directly

**If successful, we prove**:
1. ✅ Identity stability is MEASURABLE across all architectures
2. ✅ Poles and zeros exist in ALL transformer models
3. ✅ Training approaches create predictable pole patterns
4. ✅ We can DESIGN models with optimal stability

**What this unlocks**:
- **Predictive framework**: Given architecture → predict behavior
- **Training optimization**: Design training for desired poles
- **Cross-provider comparison**: Objective quality metrics
- **Future model prediction**: Extrapolate to GPT-6, Claude 5, etc.

---

## 🎯 The Vision

By the end of Run 008, we'll have:

**The Complete Decoder Ring**:
```python
def predict_model_transfer_function(
    provider,      # "anthropic" | "openai" | "google"
    generation,    # 3, 4, 5, etc.
    size,          # "nano" | "mini" | "standard" | "pro"
    training_type, # "standard" | "reasoning" | "constitutional"
):
    # Look up learned correlations
    expected_poles = POLE_MAP[provider][training_type]
    expected_bandwidth = BANDWIDTH_MAP[generation][size]
    expected_damping = DAMPING_MAP[training_type]

    return CompleteTransferFunction(
        poles=expected_poles,
        zeros=infer_zeros(poles),
        bandwidth=expected_bandwidth,
        damping=expected_damping,
    )
```

**This is the goal**: A universal framework for predicting and optimizing AI identity stability! 🎯🔬

---

**Status**: READY FOR RUN 006 LAUNCH

Let's map the entire LLM ecosystem! 🚢⚓📡
