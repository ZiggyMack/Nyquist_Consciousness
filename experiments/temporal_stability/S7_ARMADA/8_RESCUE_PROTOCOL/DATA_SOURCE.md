# Data Source for Rescue Protocol Experiments

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

# Filter for rescue experiments only
rescue_results = [
    r for r in data['results']
    if r.get('experiment') == 'rescue'
]

print(f"Found {len(rescue_results)} rescue results")
# Expected: ~750 (25 ships x 30 iterations)
```

## Methodology

- **Drift Calculation:** Cosine distance (1 - cosine_similarity)
- **Event Horizon:** 0.80 (calibrated from run023b P95)
- **Recovery Metrics:** recovery_ratio, lambda (decay constant)

## Visualization Output

Generated visualizations go to:
```
visualizations/pics/4_Rescue/
```

---
*Single source of truth: 15_IRON_CLAD_FOUNDATION/results/*
