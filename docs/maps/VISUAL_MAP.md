# VISUAL_MAP.md - Master Visualization Guide

**Purpose:** Canonical reference for which visualizations are appropriate for which experiment types and data structures.

**Last Updated:** December 17, 2025

---

## 1. Visualization Types Available

| Type | File Pattern | What It Shows | Data Requirements |
|------|-------------|---------------|-------------------|
| **Phase Portrait** | `run{ID}_phase_portrait.png` | drift[N] vs drift[N+1] correlation | `drifts[]` array with 3+ points |
| **Vortex** | `run{ID}_vortex.png` | Polar spiral trajectory | `drifts[]` array with 3+ points |
| **3D Basin** | `run{ID}_3d_basin.png` | Phase space with Event Horizon cylinder | `drifts[]` array with 3+ points |
| **Pillar Analysis** | `run{ID}_pillar_analysis.png` | Provider clustering in angular space | `drifts[]`, `provider`, `ship` |
| **Stability Basin** | `run{ID}_stability_basin.png` | Baseline vs max drift scatter + histogram | `baseline_drift`, `max_drift` (calculable) |
| **FFT Spectral** | `run{ID}_fft_spectral.png` | Frequency content of drift trajectory | `drifts[]` with 8+ points (embedding-based) |
| **Interactive 3D** | `run{ID}_interactive_3d.html` | Rotatable 3D basin | Same as 3D Basin |
| **Interactive Vortex** | `run{ID}_interactive_vortex.html` | Zoomable polar view | Same as Vortex |

---

## 2. Experiment Type to Visualization Mapping

### Run-Level Appropriateness

| Run | Type | Vortex | Phase | Basin 3D | Pillar | Stability | FFT | Notes |
|-----|------|--------|-------|----------|--------|-----------|-----|-------|
| **008** | Stress Test | Y | Y | Y | Y | Y* | N | *All VOLATILE (expected) |
| **009** | Event Horizon | Y | Y | Y | Y | Y | N | EH discovery run |
| **010** | Oscilloscope | Y | Y | Y | Y | **EXCLUDE** | **EXCLUDE** | Keyword-based drift 0-1.0 |
| **011** | Baseline | Y | Y | Y | Y | Y | N | |
| **012** | Revalidation | Y | Y | Y | Y | Y | N | |
| **013** | Boundary | Y | Y | Y | Y | Y | N | |
| **014** | Rescue | Y | Y | Y | Y | Y | N | |
| **015** | Criteria | Y | Y | Y | Y | Y | N | First pillar data |
| **016** | Settling | Y | Y | Y | Y | Y | N | |
| **017** | Context | Y | Y | Y | Y | Y | N | |
| **018** | Threshold | Y | Y | Y | Y | Y | Y | Full Iron Clad |
| **020** | Tribunal | Y | Y | Y | Y | Y | Y | Control A/B |

### Exclusion Rules (Implemented in `visualize_armada.py`)

```python
VISUALIZATION_EXCLUSIONS = {
    "010": {
        "stability": "Cognitive oscilloscope experiment - no stability data collected",
        "fft": "Keyword-based drift not suitable for spectral analysis"
    },
}
```

---

## 3. Data Requirements by Visualization

### Stability Basin Requirements
- **Baseline Drift:** First drift value in trajectory (`drifts[0]`)
- **Max Drift:** Maximum drift value in trajectory (`max(drifts)`)
- **Event Horizon:** 1.23 threshold for STABLE/VOLATILE classification

**NOT suitable when:**
- Drift values are keyword-based (0-1.0 range) instead of embedding-based
- Experiment didn't measure baseline→max trajectory relationship

### FFT Spectral Requirements
- **Minimum Points:** 8+ drift values for meaningful frequency analysis
- **Data Type:** Must be embedding-based (cosine distance) not keyword counts
- **Sampling:** Regular turn intervals

**NOT suitable when:**
- Drift is keyword-ratio based (discrete, not continuous)
- Less than 8 trajectory points

### Pillar Analysis Requirements
- Provider field (claude/gpt/gemini/grok)
- Ship field (model name)
- Drift trajectory for angular calculation

**Smart Labeling:** Labels auto-hide when points cluster too tightly (spread < 0.5)

---

## 4. Output Directory Structure

```
visualizations/pics/
├── 1_phase_portrait/      # drift[N] vs drift[N+1]
├── 2_vortex/              # Polar spiral trajectories
├── 3_basin_3d/            # 3D phase space
├── 4_pillar/              # Provider clustering
├── 5_stability/           # Baseline vs max drift
├── 6_fft/                 # Spectral analysis
├── 7_interactive/         # HTML exports
└── 8_pfi_dimensional/     # PFI validation visuals
```

---

## 5. Sample Size Recommendations for IRON CLAD Visualizations

### Minimum Runs for Statistical Validity

| Visualization | Minimum Total | Per Provider | Notes |
|--------------|---------------|--------------|-------|
| **Histogram** | 15-20 | 5-10 | Below this, distribution shape is unreliable |
| **Stability Scatter** | 10 | 3-5 | Shows trend but limited confidence |
| **Pillar Clustering** | 15 | 5 | Needs spread to differentiate providers |
| **FFT Spectral** | N/A | 8+ turns | Per trajectory, not per run |

### IRON CLAD Target Coverage

For publication-quality histograms:

| Level | Total Runs | Per Provider | Result |
|-------|-----------|--------------|--------|
| **Minimum** | 21 | 5-7 | Current state (Run 014 level) |
| **Recommended** | 50+ | 10-15 | Clear provider distributions |
| **IRON CLAD** | 100+ | 20+ | Statistical significance, small error bars |

### Why Run 014's Histogram Looks Sparse

Run 014 has only 6 trajectories total:
- Histogram bins spread data thin
- Cannot show meaningful distribution
- **Solution:** Run more models per provider for this experiment type

### Multi-Provider Requirements

To show meaningful provider comparison in a single visualization:
- **3 providers minimum** (Claude, GPT, Gemini)
- **5 providers ideal** (add Grok, Together.ai)
- **Per-provider count:** 5+ runs each to see patterns

---

## 6. Radar Plot Opportunities

Radar plots work well for multi-dimensional comparison. Current opportunities:

| Use Case | Dimensions | Where | Status |
|----------|------------|-------|--------|
| **Nyquist Pillars** | Voice, Values, Reasoning, Self-Model, Narrative | Run 015+ | Potential |
| **Provider Comparison** | Mean drift, Volatility rate, Recovery ratio | Any run | Potential |
| **PFI Components** | A_pole, B_zero, C_meta, D_identity, E_hedging | 8_pfi_dimensional | Exists |

---

## 6. Troubleshooting Common Issues

### Histogram Shows Wrong Count
**Symptom:** Legend says n=6 but histogram shows ~3 bars
**Cause:** Hardcoded bin range (0-3) cuts off high-drift data
**Fix:** (Implemented) Auto-scale bins based on actual data range

### Pillar Text Blob
**Symptom:** Individual model labels overlap in tight cluster
**Cause:** Low drift values cause all points to cluster near origin
**Fix:** (Implemented) Smart labeling hides labels when spread < 0.5

### All Points Show as VOLATILE
**Symptom:** Stability plot shows 100% volatile even below Event Horizon line
**Cause:** Status is calculated from max_drift, not baseline
**Resolution:** This is correct behavior. If max_drift > 1.23, trajectory is VOLATILE regardless of current position.

---

## 7. Adding New Exclusions

To exclude a visualization type for a specific run:

1. Edit `visualize_armada.py`
2. Add entry to `VISUALIZATION_EXCLUSIONS` dict:

```python
VISUALIZATION_EXCLUSIONS = {
    "010": {
        "stability": "Reason for exclusion",
        "fft": "Reason for exclusion"
    },
    "NEW_RUN": {
        "viz_type": "Reason"
    }
}
```

3. The exclusion check is automatic for `stability` and `fft` types

---

## 8. Related Documentation

| Document | Location | Purpose |
|----------|----------|---------|
| `visualize_armada.py` | `S7_ARMADA/visualizations/` | Main visualization script |
| `8_pfi_explained.md` | `visualizations/pics/8_pfi_dimensional/` | PFI validation guide |
| `TEMPORAL_STABILITY_MAP.md` | `docs/maps/` | Temporal stability overview |
| `ARMADA_MAP.md` | `docs/maps/` | ARMADA experiment index |

---

*"Choose your visualization wisely - the wrong plot can mislead; the right one reveals truth."*
