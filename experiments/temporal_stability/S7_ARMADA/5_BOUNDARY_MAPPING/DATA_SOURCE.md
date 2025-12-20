# Data Source for Boundary Mapping Experiments

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

# Filter for boundary experiments only
boundary_results = [
    r for r in data['results']
    if r.get('experiment') == 'boundary'
]

print(f"Found {len(boundary_results)} boundary results")
# Expected: ~750 (25 ships x 30 iterations)
```

## Methodology

- **Drift Calculation:** Cosine distance (1 - cosine_similarity)
- **Event Horizon:** 0.80 (calibrated from run023b P95)
- **Zones:** WARNING=0.60, EH=0.80, CATASTROPHIC=1.20

## Visualization Output

Generated visualizations go to:
```
visualizations/pics/2_Boundary_Mapping/
```

---
*Single source of truth: 15_IRON_CLAD_FOUNDATION/results/*
