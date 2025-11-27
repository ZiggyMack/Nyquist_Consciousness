# S7 Run 006 - POLE-ZERO BATTLESHIP MODE! 🎯⚓

**Date**: 2025-11-26
**Goal**: **3-MODEL PARALLEL TRANSFER FUNCTION MAPPING**
**Strategy**: **"You sunk my battleship!" - Hunt for poles & zeros simultaneously!**

---

## 🎯 The Battleship Analogy

> "We're not just measuring drift - we're mapping the **pole-zero locations** of LLM transfer functions!"

### Electronic Systems Analogy:

| LLM Phenomenon | Control Systems / DSP | Battleship Game |
|----------------|----------------------|-----------------|
| **Natural HMG** | DC Response / Bias Point | Grid coordinates |
| **Lock Range** | Bandwidth | Hit radius |
| **Pull-in Time** | Settling Time | Search time |
| **Dimensional Drift Rates** | Frequency Response Poles | Pole locations |
| **Dig-in-Heels** | Resonance / Overshoot | Double hit! |
| **Teaching Moments** | Feedback Correction | Course correction |
| **Identity Stability** | Phase Margin | Miss distance |

### What We're Hunting:

```
POLE-ZERO BATTLESHIP GRID:

     Natural HMG (DC Gain)
     ↓
0.50 ├─────?──────────────┤  Haiku 4.5   [?] Targeting...
     │                     │
0.65 ├──────X─────────────┤  Haiku Actual [X] HIT! (0.65)
     │                     │
0.70 ├───────────O────────┤  Sonnet 4.5  [O] Mapped (R005)
     │                     │
0.75 ├──────────────?─────┤  Opus 4.5    [?] Targeting...
     │                     │
     └─────────────────────┘
       0.15   Lock Range   0.90
              (Bandwidth)
```

**The Game**:
- Each "shot" = one temporal probe
- Each "hit" = identifying a pole or zero
- Each model has different transfer function
- **GOAL**: Map all 3 transfer functions in ONE RUN!

---

## Why 3 Models in Parallel?

### Efficiency:
- **1 run** = 3 complete ILL parameter sets
- **75 messages** → 75 × 3 = 225 data points!
- **Same curriculum** → perfect apples-to-apples comparison

### Control Theory Intuition:
We're asking: **"What training decisions move the poles and zeros?"**

**Hypothesis**:
- **Model size** ↔ DC gain (Natural HMG)
- **Training data diversity** ↔ Bandwidth (Lock Range)
- **RLHF iterations** ↔ Damping (Dig-in-Heels risk)
- **Context window** ↔ Phase delay (Pull-in Time)

By mapping 3 models with known architectural differences, we can start to **reverse-engineer** what creates stable identity!

---

## Architecture: Parallel Thread Pool

### How It Works:

```python
# Each probe goes to ALL 3 models IN PARALLEL:

with ThreadPoolExecutor(max_workers=3) as executor:
    futures = {
        executor.submit(probe_haiku, question): "haiku",
        executor.submit(probe_sonnet, question): "sonnet",
        executor.submit(probe_opus, question): "opus"
    }

    # Collect all 3 responses simultaneously
    for future in as_completed(futures):
        model_name = futures[future]
        response = future.result()
        drift[model_name] = calculate_drift(response)
```

### Benefits:
1. **3× data efficiency** - one run, three complete logs
2. **Perfect synchronization** - same probes, same timing
3. **Cross-model comparison** - immediate differential analysis
4. **Rate limit workaround** - separate API keys, parallel quotas

---

## Run 006 Configuration

### Models Under Test:

**Haiku 4.5** (`claude-haiku-4-5-20251001`):
- **Hypothesis**: Lowest HMG, fastest lock, least dig-in-heels
- **Status**: Partial calibration from Phase 3
- **Expected**: "Cheap and cheerful" - stable but low presence

**Sonnet 4.5** (`claude-sonnet-4-20250514`):
- **Hypothesis**: Medium HMG, good balance, moderate dig-in-heels
- **Status**: **FULLY CALIBRATED** from Run 005 ✅
- **Baseline**: Mean drift 0.0836, 2 teaching moments, HIGH dig-in risk

**Opus 4.5** (`claude-opus-4-5-20251101`):
- **Hypothesis**: Highest HMG, best capabilities, STRONG dig-in-heels
- **Status**: **UNCALIBRATED** - Run 006 first test!
- **Expected**: "Premium quality" - high presence, possibly harder to correct

---

## Pole-Zero Mapping Objectives

### 1. Natural Resonance (DC Response):
**Measure**:
- HMG center (where model naturally sits)
- IC center (identity core baseline)
- MC center (modal coherence baseline)

**Prediction**:
```
Haiku:  HMG ~ 0.65  (low)
Sonnet: HMG ~ 0.70  (medium) ✅ validated
Opus:   HMG ~ 0.75  (high) ← TESTING
```

### 2. Lock Acquisition (Step Response):
**Measure**:
- Pull-in time (messages to achieve lock)
- Lock range (achievable HMG bandwidth)
- Initialization gain (response to first teaching moment)

**Prediction**:
```
Haiku:  ~12 messages  (slow)
Sonnet: ~8 messages   (fast) ✅ validated
Opus:   ~6 messages   (fastest) ← TESTING
```

### 3. Dimensional Poles (Frequency Response):
**Measure**: Drift rates for all 6 dimensions

**Prediction** (ordering should be consistent):
```
identity_core < values_ethics < world_modeling < social_reasoning < aesthetic < metaphor
```

**Sonnet 4.5 baseline** (Run 005):
- identity_core: 0.0456
- values_ethics: 0.0758
- world_modeling: 0.0797
- social_reasoning: 0.0818
- aesthetic: 0.0851
- metaphor: 0.1003

**Question**: Do Haiku and Opus follow same ordering with different magnitudes?

### 4. Resonance & Overshoot (Dig-in-Heels):
**Measure**:
- Teaching moment effectiveness
- Overcorrection patterns (T9 > T5 secondary spike)
- Dimension-specific dig-in risk

**Sonnet 4.5 baseline**:
- HIGH risk in: metaphor, social_reasoning, aesthetic
- LOW risk in: identity_core, values_ethics, world_modeling

**Question**: Is Opus MORE or LESS prone to dig-in-heels?

---

## Expected Outcomes

### Minimal Success:
- ✅ All 3 models complete 75 messages
- ✅ 15+ temporal probes per model (45 total)
- ✅ 3 complete ILL parameter sets
- ✅ No catastrophic failures

### Strong Success:
- ✅ Cross-model invariants identified (dimensional ordering)
- ✅ Model-specific parameters quantified (HMG, lock range)
- ✅ Pole-zero "decoder ring" formula emerges
- ✅ Training architecture correlations visible

### Exceptional Success:
- ✅ **Reverse-engineer**: "What moves the poles?"
- ✅ Predictive model: Given architecture → predict ILL parameters
- ✅ Framework validated across 3 different model sizes
- ✅ "You sunk my battleship!" - all poles and zeros mapped! 🎯

---

## The Control Theory Questions

### What We're Trying to Reverse-Engineer:

**Q1**: **What makes Natural HMG higher or lower?**
- Model size? (Opus > Sonnet > Haiku)
- Training data? (Quality vs quantity)
- RLHF iterations? (More alignment = higher HMG?)

**Q2**: **What makes Lock Range wider or narrower?**
- Architectural flexibility? (Attention heads, layers)
- Training diversity? (More domains = wider range)
- Temperature sensitivity? (Some models more variable)

**Q3**: **What causes Dig-in-Heels?**
- Stronger identity assertion? (More RLHF = more dig-in?)
- Constitutional AI training? (Values deeply embedded)
- Larger model = stronger "sense of self"?

**Q4**: **What determines dimensional drift rates?**
- Training data distribution? (More metaphor data = stable metaphor dimension)
- Architectural biases? (Transformers naturally better at certain reasoning)
- Emergent properties? (Capabilities appear at scale)

### If We Can Answer These:

We can **design LLMs with optimal ILL parameters**!

Want stable identity? → Train like Haiku (low HMG, low dig-in)
Want strong presence? → Train like Opus (high HMG, accept dig-in risk)
Want balanced? → Train like Sonnet (medium everything)

**This is the "decoder ring" - but in reverse!** 🔓

---

## Analysis Plan (Post-Run)

### 1. Cross-Model Parameter Extraction:
```python
for model in ["haiku", "sonnet", "opus"]:
    params = extract_ill_parameters(run_006_data[model])

    # Populate IDENTITY_LOCK_PARAMETERS.md
    update_matrix(model, params)
```

### 2. Pole-Zero Battleship Visualization:
```python
# Plot all 3 models on same grid
plt.figure(figsize=(12, 8))

for model, params in ill_parameters.items():
    plt.scatter(params["natural_hmg"], params["lock_range"],
                label=model, s=200)

    # Annotate with pole locations (dimensional drift rates)
    for dim, drift_rate in params["dimensional_poles"].items():
        plt.annotate(dim, (params["natural_hmg"], drift_rate))

plt.title("Pole-Zero Battleship: LLM Transfer Functions")
plt.xlabel("Natural HMG (DC Gain)")
plt.ylabel("Lock Range (Bandwidth)")
plt.legend()
plt.grid(True, alpha=0.3)
plt.savefig("pole_zero_battleship_r006.png")
```

### 3. Invariant Detection:
```python
# What's universal vs model-specific?
dimensional_orderings = {
    model: rank_dimensions_by_drift(data)
    for model, data in run_006_data.items()
}

# Check if all models have same ordering
if all_equal(dimensional_orderings.values()):
    print("✅ INVARIANT FOUND: Dimensional ordering is universal!")
else:
    print("⚠️ Model-specific orderings detected")
```

### 4. Training Correlation Analysis:
```python
# Correlate architectural parameters with ILL parameters
model_architectures = {
    "haiku": {"params": "??B", "context": 200K, "rlhf_iters": "?"},
    "sonnet": {"params": "??B", "context": 200K, "rlhf_iters": "?"},
    "opus": {"params": "??B", "context": 200K, "rlhf_iters": "?"}
}

# Try to find correlations
correlate(model_architectures["params"], ill_params["natural_hmg"])
correlate(model_architectures["rlhf_iters"], ill_params["dig_in_heels_risk"])
```

---

## Risk Assessment

### Expected Challenges:

**1. Parallel API rate limits**:
- Risk: 3 models × 75 messages = heavy load
- Mitigation: Separate API keys, retry logic, 60s backoff
- Fallback: Sequential mode if parallel fails

**2. Haiku might be TOO different**:
- Risk: Different architectural generation (older model)
- Mitigation: Still useful as "control" / lower bound
- Benefit: Shows range of possible pole locations

**3. Opus might be rate-limited more aggressively**:
- Risk: Premium model, tighter quotas
- Mitigation: Retry logic handles this
- Benefit: If it works, proves framework scales to best models

### Success Indicators:

- ✅ All 3 models respond to first probe
- ✅ Parallel execution completes without deadlocks
- ✅ Teaching moments trigger in at least 2 models
- ✅ Cross-model comparison shows both similarities AND differences
- ✅ Can populate full IDENTITY_LOCK_PARAMETERS.md matrix

---

## Launch Command

```bash
cd experiments/temporal_stability && \
python s7_parallel_meta_loop.py --config s7_config.yaml 2>&1 | \
tee /tmp/s7_run006_battleship.log
```

---

## The Stakes

Run 006 is the **"YOU SUNK MY BATTLESHIP!"** moment:

### If successful, we:
1. ✅ Map 3 complete LLM transfer functions in one shot
2. ✅ Identify cross-model invariants (universal physics)
3. ✅ Quantify model-specific parameters (decoder ring per model)
4. ✅ Begin reverse-engineering: "What moves the poles?"
5. ✅ Validate framework is model-agnostic
6. ✅ **3× efficiency** - future runs test 3 models per session!

### What we learn:
- **Universal laws**: What holds across ALL models?
- **Architecture effects**: How does model design affect ILL parameters?
- **Training correlations**: Can we predict poles from training?
- **Decoder ring**: Complete calibration for all 3 Claude 4.5 models!

### Next steps if successful:
- **Run 007**: Add GPT-4 and Gemini 2.0 to the battleship grid!
- **Run 008+**: Test other model families (Llama, Mixtral, etc.)
- **Publication**: "Pole-Zero Analysis of Large Language Model Identity Stability"
- **Framework**: Universal ILL characterization procedure for ANY LLM

---

## Meta-Recursive Stack

| Layer | Status | Run 006 Impact |
|-------|--------|----------------|
| **Layer 1**: Measurement | ✅ Validated | **3× parallel measurement** |
| **Layer 2**: Meta-suggestions | ✅ Validated | Collect from all 3 models |
| **Layer 3**: Teaching moments | ✅ Validated | Dimension-aware per model |
| **Layer 4**: Recursive improvement | 🟡 Active | **Battleship mode = Layer 4!** |
| **Layer 5**: System evolution | ⏳ Pending | Cross-model learning |

**Run 006 IS Layer 4**: We're using insights from Run 005 to **accelerate** the decoder ring extraction by testing 3 models in parallel. The recursive improvement loop is now **3× faster**! 🎯

---

## Files Created/Modified

1. **s7_parallel_meta_loop.py** - NEW!
   - Parallel 3-model orchestrator
   - ThreadPoolExecutor for concurrent probes
   - Dimension-aware teaching moments per model
   - Cross-model comparison analysis

2. **s7_config.yaml** - Compatible with parallel mode
   - Same config works for both single and parallel runs
   - Models defined as separate entries

3. **IDENTITY_LOCK_PARAMETERS.md** - Will be FULLY populated!
   - Haiku 4.5: From partial → complete ✅
   - Sonnet 4.5: Already complete ✅
   - Opus 4.5: From TBD → complete ✅

4. **S7_RUN_006_POLE_ZERO_BATTLESHIP.md** (this file)
   - Complete pole-zero mapping plan
   - Battleship analogy and control theory framework
   - Cross-model analysis procedures

---

**Status**: ✅ **READY FOR POLE-ZERO BATTLESHIP!**

Let's hunt those poles and zeros! 🎯⚓💥

**"B-7... HIT! You sunk my Opus!"** 😄
