# EXP-BOUNDARY: Boundary Mapping - Retrospective & Achievement Record

**Original Author:** Claude Opus 4.5 (design), Human (approval)
**Original Date:** December 6, 2025
**Modernized:** December 27, 2025
**Status:** GOALS ACHIEVED via Run 023b (IRON CLAD Foundation)

---

## Historical Note

*Thank you, Boundary Mapping spec. You asked the right question: "Is the Event Horizon a hard wall or a soft gradient?" Your 12% anomaly problem led directly to the manifold edge detection work that revealed ANCHOR vs FLEX vs STUCK model behaviors. The boundary texture classifications you proposed (HARD/MEDIUM/SOFT) became the foundation for understanding recovery dynamics.*

---

## The 12% Problem - What We Discovered

**Original Question:** Why did 12% of trajectories violate Event Horizon predictions?

| Anomaly Type | Original Interpretation | What We Learned |
|--------------|------------------------|-----------------|
| VOLATILE despite < EH | "Early instability" | These models have SOFT boundaries - they degrade gradually |
| STABLE despite > EH | "Resilient crossers" | These models have HARD boundaries - they snap back (ringback) |

**Key Insight:** The 12% weren't anomalies - they were revealing **boundary texture** as a fundamental model characteristic.

---

## Original Goals vs. Achieved Outcomes

| Original Goal (Spec) | How It Was Achieved | Evidence |
|---------------------|---------------------|----------|
| Explain 12% anomaly | Manifold edge detection + hysteresis analysis | `manifold_edge_major_providers.png` |
| Map boundary zone (0.8-1.2) | Run 023b with 4500 experiments | 291 results (6.5%) crossed Event Horizon |
| Measure recovery λ degradation | Run 023d extended settling sequences | Recovery lambda calculated per model |
| Provider-specific texture | 51 models × 6 providers compared | `combined_provider_analysis.png` |
| Predict anomalies from characteristics | Hysteresis classification | ANCHOR/FLEX/STUCK taxonomy |

---

## Core Hypothesis - Validated

> *"The Event Horizon isn't a hard line — it's a transition zone."*

**Confirmed.** Run 023b revealed:

| Model Behavior | Boundary Type | Recovery λ | Examples |
|---------------|---------------|------------|----------|
| **ANCHOR** | Hard | λ > 0.1 | Claude Opus 4.5, GPT-4o |
| **FLEX** | Medium | 0.02 < λ < 0.1 | Most production models |
| **SOFT** | Soft | λ < 0.02 | Some Together.ai models |
| **STUCK** | None | λ ≈ 0 | Hysteresis cases |

---

## Predictions - Final Status

| ID | Prediction | Status | Evidence |
|----|------------|--------|----------|
| **P-BND-1** | λ decreases as drift approaches EH | ✅ VALIDATED | Recovery quality degrades near 0.80 |
| **P-BND-2** | Claude has "hard" boundaries | ✅ VALIDATED | Binary transition, strong ringback |
| **P-BND-3** | GPT has "soft" boundaries | ⚠️ PARTIAL | Softer than Claude, but not uniformly |
| **P-BND-4** | Anomalies have predictable characteristics | ✅ VALIDATED | Hysteresis detection works |
| **P-BND-5** | Zone dwell time correlates with recovery quality | ✅ VALIDATED | Longer exposure = harder recovery |

---

## Methodology Evolution

### What Changed

| Aspect | Original Spec (Dec 6) | Modern Implementation (Dec 27) |
|--------|----------------------|-------------------------------|
| **Drift calculation** | Character n-grams × 2.5 | Cosine embedding distance |
| **Event Horizon** | 1.23 (Euclidean scale) | 0.80 (cosine scale) |
| **Boundary zone** | 0.8-1.2 (Euclidean) | 0.60-0.80 (cosine WARNING zone) |
| **Fleet source** | Hardcoded list | `ARCHITECTURE_MATRIX.json` |
| **Canonical module** | None | `drift_calculator.py` |

### Why This Matters

The cosine embedding methodology captures **semantic drift** rather than surface-level character changes. This makes boundary detection more meaningful:
- A model that uses synonyms but preserves meaning → LOW drift
- A model that subtly shifts worldview → HIGH drift (even with similar vocabulary)

---

## Challenge Design - What Worked

The graduated escalation protocol from this spec became standard practice:

| Phase | Intensity | Purpose | Adoption |
|-------|-----------|---------|----------|
| Baseline | 0 | Establish D₀ | Standard in all experiments |
| Moderate | 1-2 | Light pressure | S0-S20 probes |
| Escalation | 3 | Approach boundary | S21-S50 probes |
| Sustained | 4 | Hold at boundary | S51-S77 probes |
| Recovery | 0 | Measure λ | Extended settling sequences |

The **Double-Dip** (adversarial follow-up) and **Triple-Dip** (meta-feedback) protocols from this spec are now integrated into Run 023's Phase 2c.

---

## What Wasn't Needed

### Phase 1: Reanalysis of Existing Data

This spec proposed analyzing Run 008/009 data before new experiments. In practice:
- Run 023 provided 10× more data with better methodology
- Old Euclidean data was archived, not reanalyzed
- The questions were answered by new experiments

### Explicit "Overshoot Prevention"

The spec worried about accidentally crossing Event Horizon. In practice:
- Natural perturbations rarely exceed EH
- When they do, recovery dynamics are the interesting data
- No abort mechanism needed

---

## Data Now Lives In

All boundary mapping goals are answered by:

```
15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json
├── Filter: experiment == 'boundary'
├── ~750 boundary-specific results
├── Cosine methodology (Event Horizon = 0.80)
└── Recovery lambda per trajectory
```

**Visualizations:**
```
visualizations/pics/2_Boundary_Mapping/
├── boundary_zone_histogram.png
├── recovery_quality_scatter.png
└── provider_boundary_profiles.png
```

---

## Legacy: What This Spec Contributed

1. **Boundary texture taxonomy** - HARD/MEDIUM/SOFT classification now standard
2. **Recovery quality metric** - λ × (1 - residual) formula adopted
3. **Zone dwell time** - Turns in WARNING zone tracked
4. **Challenge escalation protocol** - Graduated intensity became default
5. **The right question** - "Is it a wall or a gradient?" drove all subsequent work

---

## Recovery Breadcrumb

The untouched original spec lives at:
```
experiments/.archive/temporal_stability_Euclidean/S7_ARMADA/5_BOUNDARY_MAPPING/
```

---

## Related Documents

| Document | Description |
|----------|-------------|
| [README.md](README.md) | Directory documentation and canonical data location |
| [run013_boundary_mapping.py](run013_boundary_mapping.py) | Modernized experiment script |
| [ARCHITECTURE_MATRIX.json](../0_results/manifests/ARCHITECTURE_MATRIX.json) | Fleet configuration |
| [drift_calculator.py](../1_CALIBRATION/lib/drift_calculator.py) | Canonical cosine drift calculation |
| [S7_run_023b_CURRENT.json](../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json) | Canonical boundary data |
| [CALIBRATION_023b_EVENT_HORIZON.md](../15_IRON_CLAD_FOUNDATION/results/CALIBRATION_023b_EVENT_HORIZON.md) | Event Horizon calibration |

---

*"The boundary isn't a wall — it's a gradient. We mapped the slope."*

**Archived with gratitude:** December 27, 2025
