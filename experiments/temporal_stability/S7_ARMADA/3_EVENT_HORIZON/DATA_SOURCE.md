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

- **Drift Calculation:** Cosine distance (1 - cosine_similarity)
- **Event Horizon:** 0.80 (calibrated from run023b P95)
- **Legacy:** Runs 008-012 used keyword RMS with EH=1.23 (archived)

## Visualization Output

Generated visualizations go to:
```
visualizations/pics/1_Vortex/
visualizations/pics/2_Boundary_Mapping/
```

---
*Single source of truth: 15_IRON_CLAD_FOUNDATION/results/*
