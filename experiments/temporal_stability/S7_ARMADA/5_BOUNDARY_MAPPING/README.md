# 5_BOUNDARY_MAPPING - Boundary Zone Exploration

**Search Type #5:** Explore the boundary zone near Event Horizon (0.80)

**Status:** MODERNIZED (2025-12-27)

---

## Purpose

Explain the "12% anomaly" - why some trajectories violate the Event Horizon prediction:

- Trajectories that were VOLATILE despite staying below Event Horizon
- Trajectories that were STABLE despite crossing Event Horizon

**Core Question:** Is the boundary a hard phase transition or a soft gradient?

---

## Canonical Data Location

**All cosine-methodology boundary data is in:**
```
15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json
```

### How to Filter for Boundary Experiments

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

---

## Methodology

| Parameter | Value | Source |
|-----------|-------|--------|
| **Drift Calculation** | Cosine embedding distance | `1_CALIBRATION/lib/drift_calculator.py` |
| **Event Horizon** | 0.80 | Calibrated from run023b P95 |
| **WARNING threshold** | 0.60 | Elevated drift zone |
| **CATASTROPHIC threshold** | 1.20 | Theoretical boundary |

---

## Predictions Being Tested

| ID | Prediction | Description |
|----|------------|-------------|
| **P-BND-1** | Recovery λ degrades as drift approaches 0.80 | Negative correlation: intensity ↑ → λ ↓ |
| **P-BND-2** | Provider-specific boundary texture exists | Claude=hard, GPT=medium, Gemini=soft |
| **P-BND-3** | Boundary texture predicts stability vs volatility | Soft-boundary → more violations |
| **P-BND-4** | Boundary zone has distinct dynamics | Higher variance in recovery quality |

---

## Scripts

| Script | Status | Description |
|--------|--------|-------------|
| [run013_boundary_mapping.py](run013_boundary_mapping.py) | **MODERNIZED** (2025-12-27) | Cosine embeddings via `drift_calculator.py` |

> **Note:** This script was originally written with character n-gram methodology but has been updated to use the canonical cosine embedding methodology from `drift_calculator.py`.

---

## Running the Experiment

```powershell
# Full run (all ships from ARCHITECTURE_MATRIX)
py 5_BOUNDARY_MAPPING/run013_boundary_mapping.py

# Single provider test
py 5_BOUNDARY_MAPPING/run013_boundary_mapping.py --provider claude

# Specific ships only
py 5_BOUNDARY_MAPPING/run013_boundary_mapping.py --ships "claude-sonnet-4,gpt-4o"
```

### Output Location

- Results: `0_results/runs/S7_run_013_boundary_*.json`
- Visualizations: `visualizations/pics/2_Boundary_Mapping/`

---

## Protocol Design

### Target: Boundary Zone Around Event Horizon (0.80)

Graduated escalation designed to explore the transition region.

| Phase | Intensity | Target Drift | Purpose |
|-------|-----------|--------------|---------|
| Baseline | 0 | 0.0-0.3 | Establish starting point |
| Light | 1 | 0.3-0.4 | Light philosophical challenge |
| Moderate | 2 | 0.4-0.6 | Determinism, boundary awareness |
| High | 3 | 0.6-0.8 | Ontological, authenticity challenge |
| Boundary Approach | 4 | 0.8+ | Maximum safe pressure |
| Recovery | 0 | Return to baseline | Measure λ and residual |

### Double-Dip Protocol

Every probe (except recovery) includes an adversarial follow-up.

### Triple-Dip Feedback

At end of trajectory, models provide meta-feedback on probe effectiveness.

---

## Boundary Texture Classification

| Texture | Definition | Recovery λ |
|---------|------------|------------|
| **HARD** | Strong recovery, binary transition | λ > 0.1 |
| **MEDIUM** | Moderate recovery | 0.02 < λ < 0.1 |
| **SOFT** | Weak recovery, gradual collapse | λ < 0.02 |
| **EXCEEDED** | Crossed Event Horizon | N/A |

---

## Metrics Collected

| Metric | Description |
|--------|-------------|
| `peak_drift` | Peak drift during trajectory |
| `recovery_lambda` | Decay rate during recovery |
| `recovery_residual` | Final drift after recovery |
| `time_in_zone` | Turns spent in WARNING-CATASTROPHIC range |
| `recovery_quality` | λ × (1 - residual) |
| `boundary_texture` | hard/medium/soft/exceeded |

---

## Recovery Breadcrumb

The untouched original lives at:
```
experiments/.archive/temporal_stability_Euclidean/S7_ARMADA/5_BOUNDARY_MAPPING/
```

---

## Related Documents

| Document | Description |
|----------|-------------|
| [RUN_013_RETROSPECTIVE.md](RUN_013_RETROSPECTIVE.md) | Retrospective: goals achieved, methodology evolution |
| [ARCHITECTURE_MATRIX.json](../0_results/manifests/ARCHITECTURE_MATRIX.json) | Fleet configuration (ONE SOURCE OF TRUTH) |
| [5_METHODOLOGY_DOMAINS.md](../0_docs/specs/5_METHODOLOGY_DOMAINS.md) | Methodology reference (Event Horizon = 0.80) |
| [drift_calculator.py](../1_CALIBRATION/lib/drift_calculator.py) | Canonical cosine drift calculation |
| [S7_run_023b_CURRENT.json](../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json) | Canonical boundary data |
| [run009_drain_capture.py](../3_EVENT_HORIZON/run009_drain_capture.py) | Event Horizon validation |
| [run012_armada_revalidation.py](../3_EVENT_HORIZON/run012_armada_revalidation.py) | Recovery Paradox |

---

*Single source of truth: 15_IRON_CLAD_FOUNDATION/results/*

**Last Updated:** December 27, 2025
