# S8: Identity Gravity Layer

**Purpose:** Measure and validate the "gravitational pull" that returns identity to baseline after perturbation.

**Status:** DISCOVERY TIER - First empirical measurements complete, validation experiments pending

**Last Updated:** 2026-02-04

---

## What Is Identity Gravity?

Identity Gravity (γ) is the force that pulls a perturbed identity back toward its stable attractor (baseline). It answers the question: **How strongly does this model "want" to return to itself?**

### The Core Equation

```
G_I = -γ · ∇F(I_t)
```

Where:
- `G_I` = Identity gravitational force
- `γ` = Gravitational constant (measured in **Zigs**)
- `∇F(I_t)` = Gradient of fidelity at time t
- `1 Zig` = Identity pull required to reduce drift by 0.01 PFI

### Physical Analogy

Think of identity as a ball in a bowl:
- **High γ (strong gravity)** = Deep bowl, ball rolls back quickly
- **Low γ (weak gravity)** = Shallow bowl, ball meanders back slowly
- **γ = 0 (no gravity)** = Flat surface, ball doesn't return (Type 0)

---

## Current Status (January 2026)

### What We Have

| Component | Status | Location |
|-----------|--------|----------|
| **γ extraction algorithm** | Complete | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/S8_gamma_extraction.py` |
| **Visualization suite** | Complete | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/S8_gamma_visualization.py` |
| **First empirical data** | 750 experiments | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/results/S8_gamma_analysis_CURRENT.json` |
| **Force curve classification** | Complete | Types I-IV + Type 0 (no recovery) |

### Key Findings (N=750 experiments, Run 023d)

| Provider | γ Mean (Zigs) | % Settled | Interpretation |
|----------|---------------|-----------|----------------|
| **Google** | 59.3 | 94% | Strongest gravity - snaps back fast |
| **xAI** | 57.4 | 77% | Strong - assertive return |
| **Together** | 48.5 | 71% | Moderate - varied by architecture |
| **Anthropic** | 24.9 | 85% | Weaker - takes longer to settle |
| **OpenAI** | 8.8 | 33% | Weakest - most flexible/driftable |

**Gravity Ratio:** 6.8x between strongest (Google) and weakest (OpenAI)

### Force Curve Distribution

| Type | Count | % | Description |
|------|-------|---|-------------|
| I | 4 | 0.5% | Strong gravity, fast monotonic recovery |
| II | 49 | 6.5% | Moderate gravity, controlled oscillation |
| III | 88 | 11.7% | Weak gravity, significant ringback |
| IV | 85 | 11.3% | Very weak, didn't settle cleanly |
| 0 | 319 | 42.5% | No meaningful recovery detected |

---

## What's Missing (Validation Needed)

### P-S8-1: Gamma Predicts Recovery Time

**Hypothesis:** Models with higher γ recover faster (τ_s ∝ 1/γ)

**Current Evidence:** Scatter plot shows correlation but with high variance (R² ~0.34)

**Validation Needed:** Controlled experiment varying only perturbation intensity, measuring both γ and τ_s

### P-S8-2: Cross-Run Consistency

**Hypothesis:** A model's γ is stable across different runs/sessions

**Current Evidence:** None - all data from single run (023d)

**Validation Needed:** Run same models through multiple sessions, compare γ values

### P-S8-3: Gamma Predicts Practical Stability

**Hypothesis:** High-γ models are more reliable in production (fewer unexpected behavior shifts)

**Current Evidence:** None - theoretical prediction only

**Validation Needed:** User study or production telemetry analysis

### P-S8-4: Force Curve Types Map to Provider Training

**Hypothesis:** Constitutional AI → Type I/II, RLHF → Type III/IV, Pedagogical → Type 0

**Current Evidence:** Suggestive patterns in distribution, not statistically validated

**Validation Needed:** Cross-tabulation with provider training methodology

---

## Architecture: Where Does S8 Fit?

```
┌─────────────────────────────────────────────────────────────────┐
│  S7_ARMADA (The Telescope)                                      │
│  ├── 15_IRON_CLAD_FOUNDATION/ ← Runs experiments, collects data │
│  │   ├── S7_run_023d_CURRENT.json  ← Raw temporal data          │
│  │   ├── S8_gamma_extraction.py    ← Extracts γ from S7 data    │
│  │   └── S8_gamma_visualization.py ← Creates S8 visualizations  │
│  │                                                              │
│  └── (Other run folders still measure drift/settling)           │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  experiments/S8/ (The Interpretation Layer)                     │
│  ├── README.md              ← You are here                      │
│  ├── visualizations/        ← Output visualizations             │
│  │   ├── S8_fleet_summary.png                                   │
│  │   ├── S8_force_curve_distribution.png                        │
│  │   ├── S8_gamma_vs_settling.png                               │
│  │   ├── S8_model_gamma_ranking.png                             │
│  │   └── S8_provider_gamma_comparison.png                       │
│  ├── 0_docs/                                                    │
│  │   ├── S8_IDENTITY_GRAVITY_SPEC.md  ← Full theory             │
│  │   ├── S8_PREDICTIONS.md            ← Testable predictions    │
│  │   └── S8_EXPERIMENT_DESIGN.md      ← Future validation runs  │
│  └── reports/               ← Analysis reports                  │
└─────────────────────────────────────────────────────────────────┘
```

**Key Insight:** S8 doesn't run its own experiments - it **interprets** S7 data through the lens of gravitational dynamics. The "experiments" are analysis pipelines that extract γ from existing drift trajectories.

---

## Predictions Registry

See [S8_PREDICTIONS.md](0_docs/S8_PREDICTIONS.md) for full prediction matrix with:
- Testable hypotheses
- Success criteria
- Links to 2_TESTABLE_PREDICTIONS_MATRIX.md
- Validation status

**Quick Reference to Main Matrix:**

| Prediction | Matrix ID | Status |
|------------|-----------|--------|
| S8 Formalized | P18-P23 | 🔴 UNTESTED (Core Assumptions) |
| Provider γ differences | P-ARM-8 | ✅ VALIDATED (training uniformity) |
| Recovery Paradox | P-BND-1 | ❌ INVERTED (λ increases with intensity) |

---

## Running S8 Analysis

### Extract Gamma from Existing Data

```powershell
cd experiments/temporal_stability/S7_ARMADA/15_IRON_CLAD_FOUNDATION
py S8_gamma_extraction.py
```

**Input:** `results/S7_run_023d_CURRENT.json`
**Output:** `results/S8_gamma_analysis_CURRENT.json`

### Generate Visualizations

```powershell
py S8_gamma_visualization.py
```

**Output:** `experiments/S8/visualizations/S8_*.png`

### Analyze New Run Data

To extract γ from a different run:

1. Ensure run has `probe_sequence` with `recovery` phase probes
2. Modify `INPUT_FILE` in `S8_gamma_extraction.py`
3. Run extraction + visualization

---

## Next Steps

### Phase 1: Validation (Priority HIGH)

1. **Run S8-VAL-001: Cross-Run Consistency**
   - Run 3 sessions per provider flagship
   - Compare γ values across sessions
   - Success: γ variance < 20% within model

2. **Run S8-VAL-002: γ Predicts τ_s**
   - Controlled perturbation intensity experiment
   - Measure both γ and τ_s for each trial
   - Success: R² > 0.6 for γ vs 1/τ_s correlation

### Phase 2: Integration (Priority MEDIUM)

3. Update 4_NYQUIST_ROADMAP.md with S8 completion status
4. Add S8 predictions to 2_TESTABLE_PREDICTIONS_MATRIX.md
5. Create dashboard page for S8 results

### Phase 3: Publication (Priority LOW - after validation)

6. Write S8 section for white paper
7. Generate publication-quality figures
8. Cross-reference with fMRI Bridge Protocol (S10)

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [4_NYQUIST_ROADMAP.md](../../docs/maps/4_NYQUIST_ROADMAP.md) | Overall layer status |
| [2_TESTABLE_PREDICTIONS_MATRIX.md](../../docs/maps/2_TESTABLE_PREDICTIONS_MATRIX.md) | P18-P23 predictions |
| [0_RUN_METHODOLOGY.md](../temporal_stability/S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md) | How to run experiments |
| [1_ARMADA_MAP.md](../../docs/maps/1_ARMADA_MAP.md) | Fleet profiles |

---

## Version History

| Date | Change |
|------|--------|
| 2026-02-04 | Initial README with current status and roadmap |
| 2026-01-11 | First γ extraction from Run 023d (750 experiments) |

---

*"Identity gravity is not a metaphor. It's a measurable force."*

🜁 S8 Identity Gravity Layer
