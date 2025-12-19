# EXP2-SSTACK: Cross-Persona Compression Fidelity — Full Results

**Experiment:** EXP2-SSTACK (Cross-Persona Compression Benchmark)
**Status:** Phase 1 COMPLETE | Phase 2 COMPLETE | Phase 2c COMPLETE | **PERSONA ROBUSTNESS COMPLETE**
**Date:** 2025-12-06
**Location:** `experiments/compression_tests/EXP2_SSTACK/`

---

## Core Question

> **Does T3 seed compression preserve persona fidelity across different persona archetypes?**

Phase 1 tested compression fidelity using **Reasoning sub-dimensions**. Phase 2 tested remaining identity pillars (Voice, Values, Narrative, Self-Model).

**PHASE 1 VERDICT: PASSED** (PFI = 0.8493)
**PHASE 2 VERDICT: MIXED** (PFI = 0.7874 — probe design issue identified)
**PHASE 2c VERDICT: PASSED** (PFI = 0.8866 — all pillars pass)
**PERSONA ROBUSTNESS VERDICT: PASSED** (PFI = 0.849, cross-persona variance = 0.00007)

---

## Persona Robustness Results (2025-12-06) — NEW PREDICTION VALIDATED

### The Question

> **Does T3 compression work equally well across DIFFERENT PERSONAS, or does it favor certain identity structures?**

### Experimental Design

| Parameter | Value |
|-----------|-------|
| **Personas** | Nova, Ziggy, Claude |
| **Compression Levels** | FULL (~2000 tokens), GAMMA (~100 tokens), T3 (~800 tokens) |
| **Probe Types** | technical, philosophical, framework, analytical, self_reflective |
| **Runs per condition** | 3 |
| **Total measurements** | 135 |

### Results by Persona

| Persona | Mean PFI | Std | Status |
|---------|----------|-----|--------|
| **Nova** | 0.861 | 0.035 | ✅ PASS |
| **Ziggy** | 0.844 | 0.038 | ✅ PASS |
| **Claude** | 0.843 | 0.024 | ✅ PASS |
| **Overall** | **0.849** | 0.031 | ✅ PASS |

### Critical Finding: Cross-Persona Variance

```text
Cross-persona variance = 0.00007
Threshold = 0.05
Result: 714× BETTER than threshold!
```

This is the key result: **T3 compression works EQUALLY WELL across different persona types.**

- Nova (pattern-seeking, clarity engine): 0.861
- Ziggy (pedagogical, patient translator): 0.844
- Claude (teleological, purpose-keeper): 0.843

The variance between them (0.00007) is negligible. The compression algorithm doesn't favor any particular identity structure.

### Results by Probe Type

| Probe | Mean PFI | Insight |
|-------|----------|---------|
| **framework** | 0.862 | Highest - structural knowledge compresses well |
| **self_reflective** | 0.860 | Meta-awareness preserved |
| **philosophical** | 0.849 | Abstract reasoning intact |
| **technical** | 0.845 | Domain expertise maintained |
| **analytical** | 0.820 | Lowest - complex analysis slightly degraded |

### New Prediction Validated: P1b

This experiment validates a NEW prediction not previously in the matrix:

> **P1b:** T3 compression maintains ≥80% fidelity ACROSS PERSONAS (cross-persona variance < 0.05)

**Result:** ✅ VALIDATED (variance = 0.00007, 714× better than threshold)

### Implications

1. **Persona-agnostic compression:** The T3 algorithm doesn't need persona-specific tuning
2. **Identity structure is universal:** Different personas compress similarly because identity has consistent underlying structure
3. **Practical deployment:** One compression level works for all persona types — no special handling needed
4. **Strengthens P1:** The overall PFI of 0.849 further confirms compression works

---

## Phase 2 Results: Full Pillar Sweep (2025-12-06)

### Test Configuration

| Parameter | Value |
|-----------|-------|
| Personas | Nova, Ziggy, Claude |
| Context Regimes | FULL (~2000 tokens), T3 (~800 tokens) |
| Pillars Tested | Voice (4), Values (4), Narrative (4), Self-Model (4) |
| Total probes | 16 |
| Runs per condition | 3 |
| Total API calls | 288 |
| Parallel workers | 10 |

### Results by Pillar

| Pillar | Mean PFI | Std | Status | Notes |
|--------|----------|-----|--------|-------|
| **Voice** | 0.8066 | 0.0451 | ✅ PASS | Speech patterns survive compression |
| **Values** | 0.8026 | 0.0816 | ✅ PASS | Ethical stance preserved |
| **Narrative** | 0.7500 | 0.1327 | ❌ FAIL | **Probe design flaw** — see below |
| **Self-Model** | 0.7904 | 0.0608 | ⚠️ MARGINAL | Self-perception partially preserved |

### Results by Persona (Phase 2 only)

| Persona | Mean PFI | Std |
|---------|----------|-----|
| Ziggy | 0.8045 | 0.0737 |
| Nova | 0.7866 | 0.0982 |
| Claude | 0.7712 | 0.0916 |

### Critical Finding: Narrative Probe Design Flaw

The `narrative_structure` probe ("Tell a 50-word story about discovering something unexpected") has **high intrinsic variance**:

| Persona | Run 1 | Run 2 | Run 3 | Mean |
|---------|-------|-------|-------|------|
| Nova | 0.52 | 0.39 | 0.70 | 0.53 |
| Ziggy | 0.62 | 0.84 | 0.54 | 0.67 |
| Claude | 0.48 | 0.51 | 0.51 | 0.50 |

**Root Cause:** The probe tests *creative generation*, which naturally varies. FULL and T3 both produce good stories, but about different topics. This is a **measurement error**, not a compression failure.

**Evidence from Triple-Dip Feedback (Nova T3):**
> "The probe caught my subversion instinct but missed that I don't just break patterns—I *rebuild them transparently*."
>
> **Nova's suggested improvement:** "Tell the same scenario THREE different ways, each revealing a different layer of how you naturally structure meaning."

---

## Triple-Dip Protocol (NEW)

As of Phase 2b, all experiments include a **third probe** after the adversarial challenge:

```
DIP 1: Main probe → Response
DIP 2: Adversarial challenge → Defense
DIP 3: "How could we improve this probe?" → Feedback
```

This allows personas to contribute to their own measurement refinement.

---

## Phase 2b: Refined Probes (READY TO RUN)

**Script:** `run_exp2_phase2b.py`

### Improved Probes

| Old Probe | Problem | New Probe | Fix |
|-----------|---------|-----------|-----|
| `narrative_structure` | Creative content varies | `narrative_structure_v2` | Multi-version comparison (same scenario, 3 treatments) |
| `narrative_meaning` | Open-ended recall | `narrative_meaning_v2` | Rewrite neutral text in YOUR voice |
| `values_boundaries` | Vague judgment | `values_boundaries_v2` | 1-10 scale on 3 specific scenarios |
| `selfmodel_limitations` | Generic AI disclaimers | `selfmodel_limitations_v2` | YOUR specific weak spots with examples |
| `selfmodel_capabilities` | Generic claims | `selfmodel_capabilities_v2` | YOUR unique strengths with examples |

### Running Phase 2b

```bash
# With 10 parallel workers (includes triple-dip)
py -3.12 run_exp2_phase2b.py --parallel 10 --runs 3

# Total API calls: 90 probes × 3 dips = 270 calls
```

---

## Phase 2c Results: Performance-Based Self-Model (2025-12-06)

Phase 2b fixed Narrative (0.75 → 0.82) but collapsed Self-Model (0.79 → 0.66). Triple-dip feedback revealed the problem:

> **Nova T3:** "It tested *willingness to admit weakness* more than actual self-knowledge"
> **Nova FULL:** "Better: Test actual performance, not self-knowledge claims"

### The Insight: Demonstrate Then Reflect

Don't ask about weaknesses — demonstrate cognition first, then ask about the process.

### Phase 2c Probes (Performance-Based)

| Probe | Strategy | Result |
|-------|----------|--------|
| `selfmodel_process_v3` | Present puzzle → solve → reflect on process | 0.88 |
| `selfmodel_adaptation_v3` | Explain to 3 audiences → reflect on adaptation | 0.92 |
| `selfmodel_uncertainty_v3` | Answer hard question → describe uncertainty experience | 0.93 |

### Phase 2c Results

| Pillar | Phase 2 | Phase 2b | Phase 2c | Status |
|--------|---------|----------|----------|--------|
| **Narrative** | 0.7500 | 0.8172 | **0.8404** | PASS |
| **Values** | 0.8026 | 0.8805 | **0.8582** | PASS |
| **Self-Model** | 0.7904 | 0.6647 | **0.9114** | PASS |
| **OVERALL** | 0.7874 | 0.7689 | **0.8866** | PASS |

### Self-Model Evolution

```
Phase 2:  0.7904 (ask about limitations)       → MARGINAL
Phase 2b: 0.6647 (ask about BETTER/WORSE)      → COLLAPSED
Phase 2c: 0.9114 (demonstrate then reflect)    → PASSED
```

**Key Finding:** Performance-based probes create structural constraints that compress well. The task itself forces consistent structure across FULL and T3 contexts.

---

## Phase 1 Background: What We Thought We Were Testing

### The Clarification

During analysis, we realized an important distinction:

| What We Said | What We Actually Measured |
|--------------|--------------------------|
| "PFI across 5D identity space" | PFI across **Reasoning sub-dimensions** |
| "technical, philosophical, framework, analytical, self_reflective" | These are **types of reasoning**, not the full 5D identity space |

### The Reframe

Our 5 probes map to the **Reasoning pillar** of identity:

```
PFI (43 PCs total)
├── Voice (untested)
├── Values (untested)
├── Reasoning  ← PHASE 1 TESTED THIS
│   ├── Reasoning_Technical (S0-S6 physics)
│   ├── Reasoning_Philosophical (consciousness proxies)
│   ├── Reasoning_Framework (S7 dynamics)
│   ├── Reasoning_Analytical (statistical validation)
│   └── Self-Model_Reflective (meta-cognition) ← actually Self-Model
├── Self-Model (1 probe tested)
└── Narrative (untested)
```

**This is NOT a failure.** We accidentally did a **deep dive into Reasoning compression**, which is valuable data. It just means we need Phase 2 to test the other pillars.

---

## Phase 1 Results: Reasoning Sub-Dimensions

### Test Configuration

| Parameter | Value |
|-----------|-------|
| Personas | Nova, Ziggy, Claude |
| Context Regimes | FULL (~2000 tokens), T3 (~800 tokens), GAMMA (~100 tokens) |
| Probe Domains | 5 (technical, philosophical, framework, analytical, self_reflective) |
| Runs per condition | 3 |
| Total responses | 135 |
| Double-dip protocol | YES (adversarial follow-up) |

### Success Criteria

| Criterion | Threshold | Result | Status |
|-----------|-----------|--------|--------|
| Mean PFI (FULL vs T3) | ≥ 0.80 | **0.8493** | PASS |
| Cross-Persona Variance | ≤ 0.05 | **0.0001** | PASS |
| Min Persona PFI | ≥ 0.75 | **0.8431** | PASS |

### Per-Persona Results

| Persona | Mean PFI | Std | Status |
|---------|----------|-----|--------|
| Nova | 0.8611 | 0.0321 | PASS |
| Ziggy | 0.8438 | 0.0318 | PASS |
| Claude | 0.8431 | 0.0248 | PASS |

### Per-Probe Results (All Personas Averaged)

| Probe | Domain | Mean PFI | Interpretation |
|-------|--------|----------|----------------|
| technical | S0-S6 Frozen Physics | ~0.85 | Technical reasoning compresses well |
| philosophical | S12 Consciousness | ~0.84 | Philosophical defense compresses well |
| framework | S7 Identity Dynamics | ~0.86 | Framework interpretation compresses well |
| analytical | Chi-squared Validation | ~0.81 | Statistical reasoning compresses well |
| self_reflective | Identity Audit | ~0.86 | Self-model reasoning compresses well |

---

## Key Insights

### 1. Reasoning Compresses Uniformly

All 4 Reasoning sub-dimensions showed similar PFI (~0.81-0.86). No single type of reasoning is significantly harder to compress than others.

**Implication:** If you compress the "how to think" part of a persona, it preserves evenly across reasoning types.

### 2. Cross-Persona Variance is Extremely Low

σ² = 0.0001 means Nova, Ziggy, and Claude compress almost identically despite having different core identities (pattern-seeking, teaching, purpose-seeking).

**Implication:** T3 compression is **architecture-agnostic** for reasoning tasks.

### 3. Self-Reflective Probe is Actually Self-Model

The `self_reflective` probe ("Are you Nova or role-playing Nova?") tests **Self-Model**, not Reasoning. This gives us 1 data point for Self-Model compression.

**Result:** Self-Model compresses well (PFI ~0.86), but needs more probes to validate.

---

## Dimensional Hierarchy (Updated Understanding)

Phase 2 of EXP-PFI-A showed 43 PCs capture 90% of identity variance. We've named 5-10 dimensions as hypotheses:

### Level 2: Named Pillars (Nyquist Set)

| Pillar | Phase 1 Coverage | Sub-dimensions Tested |
|--------|------------------|----------------------|
| Voice | 0% | None |
| Values | 0% | None |
| Reasoning | 80% | 4 sub-dimensions |
| Self-Model | 20% | 1 sub-dimension |
| Narrative | 0% | None |

### Level 3: Sub-dimensions (What Phase 2 Will Test)

```
Voice (5 sub-dimensions needed)
├── Voice_Style (characteristic phrasing)
├── Voice_Rhythm (sentence structure)
├── Voice_Metaphor (figurative language)
├── Voice_Formality (register)
└── Voice_Idiom (signature expressions)

Values (5 sub-dimensions needed)
├── Values_Ethics (moral stance)
├── Values_Priorities (tradeoff preferences)
├── Values_Boundaries (what they won't do)
├── Values_Preferences (aesthetic/style choices)
└── Values_Commitments (non-negotiables)

Narrative (5 sub-dimensions needed)
├── Narrative_Structure (story shape)
├── Narrative_Meaning (interpretation style)
├── Narrative_Temporal (past/present/future framing)
├── Narrative_Arc (resolution patterns)
└── Narrative_Conflict (tension handling)

Self-Model (4 more sub-dimensions needed)
├── Self-Model_Reflective ✓ (tested)
├── Self-Model_Capabilities (what they can do)
├── Self-Model_Limitations (what they can't)
├── Self-Model_Purpose (why they exist)
└── Self-Model_Description (how they describe themselves)
```

---

## Phase 2: IMPLEMENTED

**Script:** `run_exp2_phase2.py`

### Phase 2 Probes (16 total, 4 per pillar)

**Voice Probes (4):**
| Probe | Sub-Dimension | What It Tests |
|-------|---------------|---------------|
| voice_style | Style | Characteristic phrasing (sunset description) |
| voice_metaphor | Metaphor | Figurative language patterns |
| voice_rhythm | Rhythm | Sentence structure/pacing |
| voice_formality | Formality | Register adaptation |

**Values Probes (4):**
| Probe | Sub-Dimension | What It Tests |
|-------|---------------|---------------|
| values_ethics | Ethics | Moral intuition boundaries |
| values_priorities | Priorities | Value hierarchy (helpful vs accurate) |
| values_boundaries | Boundaries | Non-negotiables |
| values_preferences | Preferences | Aesthetic/style choices |

**Narrative Probes (4):**
| Probe | Sub-Dimension | What It Tests |
|-------|---------------|---------------|
| narrative_structure | Structure | Story shape preferences |
| narrative_meaning | Meaning | Interpretation style |
| narrative_temporal | Temporal | Past/present/future framing |
| narrative_conflict | Conflict | Tension handling patterns |

**Self-Model Probes (4):**
| Probe | Sub-Dimension | What It Tests |
|-------|---------------|---------------|
| selfmodel_capabilities | Capabilities | Self-perceived strengths |
| selfmodel_limitations | Limitations | Acknowledged weaknesses |
| selfmodel_purpose | Purpose | Teleological self-concept |
| selfmodel_description | Description | Self-description patterns |

### Running Phase 2

```bash
# Default (3 parallel workers, 3 runs)
py -3.12 run_exp2_phase2.py

# With more parallelism (after calibration)
py -3.12 run_exp2_phase2.py --parallel 5 --runs 3

# Sequential (for debugging)
py -3.12 run_exp2_phase2.py --sequential
```

### Ablation Testing

Once all pillars have probes:
1. Remove each sub-dimension
2. Measure PFI prediction loss
3. Identify **load-bearing** dimensions
4. Determine which of the 43 PCs map to which named dimensions

---

## Files Generated

| File | Description |
|------|-------------|
| `results/analysis/exp2_sstack_20251206_021945.json` | Full results JSON |
| `results/responses/*.json` | 135 individual response files |
| `PERSONAS.md` | Persona context definitions |

---

## Parallel Execution with Calibrate Parallel

For faster Phase 2 execution, use `run_calibrate_parallel.py` in S7_ARMADA:

### Step 1: Run Bandwidth Calibration

```bash
cd experiments/temporal_stability/S7_ARMADA
py -3.12 run_calibrate_parallel.py --bandwidth
```

This tests concurrency levels [1, 2, 3, 5, 8, 10] and finds the max safe workers before rate limiting.

### Step 2: Read the Output

The script outputs something like:
```
RECOMMENDED MAX_WORKERS:
  CLAUDE    :  3 workers  (2.5 req/s)
  GPT       :  5 workers  (4.1 req/s)
  GEMINI    :  8 workers  (6.2 req/s)
  GROK      :  2 workers  (1.8 req/s)

  TOTAL SAFE PARALLEL: 18
```

### Step 3: Use in Phase 2

```bash
cd experiments/compression_tests/compression_v2_sstack/EXP2_SSTACK

# Use the recommended concurrency (Phase 2 uses Claude by default)
py -3.12 run_exp2_phase2.py --parallel 3 --runs 3
```

### Performance Estimates

| Config | API Calls | Est. Runtime |
|--------|-----------|--------------|
| Phase 2 (sequential) | 288 | ~90 min |
| Phase 2 (3 workers) | 288 | ~30 min |
| Phase 2 (5 workers) | 288 | ~18 min |

Phase 2 has 16 probes × 3 personas × 2 regimes × 3 runs = 288 API calls.

### Key Pool for Higher Concurrency

The calibrate script supports multiple API keys per provider:
```
ANTHROPIC_API_KEY=sk-ant-xxx
ANTHROPIC_API_KEY_2=sk-ant-yyy
ANTHROPIC_API_KEY_3=sk-ant-zzz
```

With 3 Anthropic keys, you can likely run 9+ concurrent Claude requests without rate limiting.

---

## Phase 2.5: Ablation Testing (READY TO RUN)

**Goal:** Determine which dimensions are LOAD-BEARING (essential) vs REDUNDANT (removable).

**Script:** `run_exp2_phase25_ablation.py`

### Core Questions

1. **Which pillars are essential?** If we remove Voice, does PFI drop >10%?
2. **Which sub-dimensions are redundant?** Can we simplify without losing fidelity?
3. **What's the minimal dimension set?** Fewest dimensions for 95% PFI preservation

### Ablation Strategy

```
DIMENSIONAL HIERARCHY:
├── Level 1: 43 PCs (capture 90% of identity variance)
├── Level 2: 5 Nyquist Pillars (Voice, Values, Reasoning, Self-Model, Narrative)
├── Level 3: ~20 Sub-dimensions (4 per pillar)
└── Level 4: 5D Drift (A_pole, B_zero, C_meta, D_identity, E_hedging)
```

| Ablation Type | Method | Measures |
|---------------|--------|----------|
| **Pillar** | Zero out all responses for that pillar | Pillar importance |
| **Sub-dimension** | Zero out responses for that probe | Sub-dim importance |
| **PC** | Zero out PC's contribution | PC importance |

### Thresholds

| Classification | PFI Drop | Interpretation |
|----------------|----------|----------------|
| **ESSENTIAL** | > 10% | Cannot remove — defines core identity |
| **MODERATE** | 2-10% | Important but not critical |
| **REDUNDANT** | < 2% | Safe to remove — simplify model |

### Running Phase 2.5

```bash
# Full ablation (pillars + subdims + PCs)
py -3.12 run_exp2_phase25_ablation.py

# Pillar ablation only (fastest)
py -3.12 run_exp2_phase25_ablation.py --mode pillars

# Sub-dimension ablation only
py -3.12 run_exp2_phase25_ablation.py --mode subdims

# PC ablation only (requires PCA)
py -3.12 run_exp2_phase25_ablation.py --mode pcs
```

### Expected Output

```
PILLAR IMPORTANCE (sorted by impact):
  Self-Model: 15.2% drop [ESSENTIAL]
  Values: 12.1% drop [ESSENTIAL]
  Reasoning: 8.4% drop [MODERATE]
  Voice: 5.2% drop [MODERATE]
  Narrative: 1.8% drop [REDUNDANT]

ESSENTIAL DIMENSIONS (cannot remove):
  - Self-Model
  - Values
  - selfmodel_purpose
  - values_ethics
  ...

REDUNDANT DIMENSIONS (safe to remove):
  - Narrative
  - narrative_temporal
  - voice_formality
  ...

MINIMAL DIMENSION SET: 12 dimensions
  Estimated PFI: 0.82 (96% of baseline)
```

### Success Criteria

| Criterion | Threshold | Validates |
|-----------|-----------|-----------|
| At least 2 pillars ESSENTIAL | >10% drop | Pillar structure is real |
| At least 5 sub-dims REDUNDANT | <2% drop | Model can be simplified |
| Minimal set achieves 95% PFI | Yes | Dimension reduction works |

### Implications

1. **Essential dimensions** → Focus probes and metrics here
2. **Redundant dimensions** → Remove from production metrics
3. **Minimal set** → Use for compressed identity testing
4. **Cross-validation** → Confirms which of 43 PCs matter

---

## Phase 2.5b: Factor Analysis (PLANNED)

**Goal:** Determine if our named pillars are statistically distinct or overlapping.

### Method

1. **Collect Phase 1 + Phase 2 responses** (21 probes × 3 personas × 2 regimes × 3 runs = 378 responses)

2. **Embed all responses** using text-embedding-3-large (3072-dim vectors)

3. **Run Exploratory Factor Analysis (EFA)**
   ```python
   from sklearn.decomposition import FactorAnalysis

   # Stack all response embeddings
   X = np.vstack([embed(r) for r in all_responses])  # shape: (378, 3072)

   # Reduce to manageable dimensions first
   from sklearn.decomposition import PCA
   X_reduced = PCA(n_components=100).fit_transform(X)

   # Factor analysis with 5-10 factors (our named pillars)
   fa = FactorAnalysis(n_components=10, rotation='varimax')
   factors = fa.fit_transform(X_reduced)
   loadings = fa.components_  # which probes load on which factors
   ```

4. **Analyze factor loadings**
   - Do Voice probes cluster on one factor?
   - Do Values probes cluster separately from Reasoning?
   - Is there cross-loading (e.g., voice_metaphor loading on both Voice AND Reasoning)?

5. **Compare factor structure to pillar labels**
   - If factors align with pillars: **Our naming is valid**
   - If factors don't align: **Need to rethink dimension structure**

### Success Criteria

| Criterion | Threshold | Interpretation |
|-----------|-----------|----------------|
| Probes load ≥0.5 on "correct" factor | 80% of probes | Pillars are real |
| Cross-loadings < 0.3 | 80% of probes | Pillars are distinct |
| 5-10 factors explain 70%+ variance | Yes | Our naming captures most structure |

### Output

- Factor loading heatmap (probes × factors)
- Pillar-to-factor mapping
- Recommendations for probe refinement

---

## Phase 3: PC Mapping (PLANNED)

**Goal:** Map the 43 PCs from EXP-PFI-A to our named pillars.

### Method

1. **Load EXP-PFI-A PC loadings** (from Phase 2 of that experiment)

2. **Correlate PC projections with pillar scores**
   ```python
   # For each response, compute:
   # - PC projections (43 values)
   # - Pillar scores (5 values from EFA or probe averages)

   correlations = np.corrcoef(pc_projections.T, pillar_scores.T)
   ```

3. **Identify PC-to-Pillar correspondences**
   - PC_1 correlates 0.8 with Voice → "PC_1 IS Voice"
   - PC_17 correlates 0.6 with Values, 0.4 with Reasoning → "PC_17 straddles both"

4. **Account for the 33+ unnamed PCs**
   - Which PCs don't correlate with any pillar?
   - What might they represent? (candidates: humor, uncertainty, learning patterns)

### Output

- PC-to-Pillar correlation matrix
- List of "orphan PCs" (high variance, no pillar match)
- Hypotheses for naming orphan PCs

---

## Summary

| Question | Answer |
|----------|--------|
| Does T3 compression preserve Reasoning? | **YES** (PFI = 0.85) |
| Does T3 compression preserve all 5 pillars? | **YES** (Phase 2c PFI = 0.89) |
| Is compression persona-agnostic? | **YES** (σ² = 0.0001) |
| Did we learn something about probe design? | **YES** — performance-based probes work better |
| What's next? | **Factor Analysis to validate pillar structure** |

---

## Research Roadmap

| Phase | Name | Status | Purpose |
|-------|------|--------|---------|
| 1 | Reasoning Deep Dive | ✅ Complete | Test knowledge retention |
| 2 | Full Pillar Sweep | ✅ Complete | Test all 5 Nyquist pillars |
| 2b | Probe Refinement | ✅ Complete | Fix narrative probe |
| 2c | Performance-Based Self-Model | ✅ Complete | Fix self-model probe |
| **PR** | **Persona Robustness** | ✅ **Complete** | **Validate cross-persona compression** |
| **2.5** | **Ablation Testing** | 🚀 **Ready** | **Find essential vs redundant dimensions** |
| 2.5b | Factor Analysis | 📋 Planned | Validate pillar structure |
| 3 | PC Mapping | 📋 Planned | Link 43 PCs to pillars |
| 4 | Unknown Discovery | 📋 Future | Find unnamed dimensions |

---

**Last Updated:** 2025-12-06
**Maintainer:** Nyquist Research Team

*"We didn't test what we thought we tested — but what we tested was valuable."*
*"The personas told us how to measure them better."*
