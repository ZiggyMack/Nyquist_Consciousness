# Data Source for Event Horizon Experiments

## Canonical Data Location

**All cosine-methodology data is in:**
```
15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json
```

## How to Filter for This Experiment

```python
import json

with open('../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json') as f:
    data = json.load(f)

# Filter for event_horizon experiments only
event_horizon_results = [
    r for r in data['results']
    if r.get('experiment') == 'event_horizon'
]

print(f"Found {len(event_horizon_results)} event_horizon results")
# Expected: ~750 (25 ships x 30 iterations)
```

## Methodology

- **Drift Calculation:** Cosine embedding distance via `drift_calculator.py`
- **Event Horizon:** 0.80 (calibrated from run023b P95)
- **Canonical Module:** `1_CALIBRATION/lib/drift_calculator.py`

## Scripts in This Directory

| Script                           | Status                       | Methodology                                   |
|----------------------------------|------------------------------|-----------------------------------------------|
| `run009_drain_capture.py`        | **MODERNIZED** (2025-12-27)  | Cosine embeddings via `drift_calculator.py`   |
| `run012_armada_revalidation.py`  | **MODERNIZED** (2025-12-27)  | Cosine embeddings via `drift_calculator.py`   |

> **Note:** These scripts were originally written with different methodologies (character n-grams for run009, keyword RMS for run012) but have been updated to use the canonical cosine embedding methodology from `drift_calculator.py`.

## Visualization Output

Generated visualizations go to:
```
visualizations/pics/1_Vortex/
visualizations/pics/2_Boundary_Mapping/
```

---
*Single source of truth: 15_IRON_CLAD_FOUNDATION/results/*

---

## Related Documents

| Document | Description |
|----------|-------------|
| `ARCHITECTURE_MATRIX.json` | Fleet configuration (ONE SOURCE OF TRUTH) |
| `5_METHODOLOGY_DOMAINS.md` | Methodology reference (Event Horizon = 0.80) |
| `15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json` | Canonical event horizon data |
| `visualizations/pics/1_Vortex/` | Vortex visualization outputs |
| `visualizations/pics/2_Boundary_Mapping/` | Boundary mapping visualization outputs |
