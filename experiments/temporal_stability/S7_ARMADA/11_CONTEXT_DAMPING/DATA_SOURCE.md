# Data Source for Context Damping Experiments

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

# Filter for recursive experiments only
recursive_results = [
    r for r in data['results']
    if r.get('experiment') == 'recursive'
]

print(f"Found {len(recursive_results)} recursive results")
# Expected: ~750 (25 ships x 30 iterations)
```

## Methodology

- **Drift Calculation:** Cosine distance (1 - cosine_similarity)
- **Event Horizon:** 0.80 (calibrated from run023b P95)
- **Recursive Loops:** Self-observation at multiple levels

## Visualization Output

Generated visualizations go to:
```
visualizations/pics/6_Architecture/
```

## Note on run018

The original `run018_recursive_learnings.py` was already using cosine methodology.
Its results are compatible with the IRON CLAD foundation data.

---
*Single source of truth: 15_IRON_CLAD_FOUNDATION/results/*
