<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-27
depends_on:
  - ./run_laplace_analysis.py
  - ../1_CALIBRATION/lib/drift_calculator.py
  - ../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
  - armada
  - drift
  - laplace
  - poles
  - control-systems
-->
# Laplace Pole-Zero Analysis

**Search Type #6:** Extract mathematical system dynamics from drift time-series.

**Status:** ACTIVE - POST-HOC analysis tool compatible with all other search types.

---

## The Scientific Question

If drift recovery follows a dynamical system, what are its mathematical characteristics?

- **Poles** = system eigenvalues (decay rates, stability margins)
- **Zeros** = cancellation points (hidden dynamics)
- **Transfer function** = input/output relationship

---

## Methods Implemented

### 1. Exponential Recovery Fit

Fit `D(t) = A * exp(-λ * t) + C` to recovery phase.

- λ > 0 → stable recovery (pole at s = -λ)
- λ ≈ 0 → marginal stability
- λ < 0 → unstable (identity diverging)

### 2. ARMA Pole Extraction

Fit AR(p) model to drift series, extract poles from characteristic polynomial.

- Poles in left half-plane (Re(s) < 0) → stable
- Poles near imaginary axis → marginally stable
- Complex conjugate poles → oscillatory behavior

### 3. Prony Analysis

Decompose drift into sum of exponentials to identify dominant modes.

---

## Key Predictions

| Prediction | Description | Status |
|------------|-------------|--------|
| P-LAP-1 | Poles can be extracted from drift time-series | To validate |
| P-LAP-2 | λ > 0 indicates stable recovery | To validate |
| P-LAP-3 | ARMA(2) captures drift dynamics | To validate |
| P-LAP-4 | STUCK trajectories have poles closer to 0 | To validate |

---

## Usage

```powershell
cd experiments/temporal_stability/S7_ARMADA/6_LAPLACE_ANALYSIS
py run_laplace_analysis.py
```

Output saved to `../0_results/analysis/laplace_analysis_*.json`

---

## Expected Findings

### If Recovery Paradox holds:

- All trajectories should have λ > 0 (stable poles)
- No trajectories should have poles in right half-plane
- STUCK trajectories may have λ closer to 0 (slower recovery)

### If Event Horizon is a bifurcation:

- Crossing 0.80 should correspond to pole crossing imaginary axis
- Above EH: pole moves toward Re(s) = 0
- At EH: pole crosses to right half-plane (instability)

---

## Files

| File | Purpose |
|------|---------|
| `run_laplace_analysis.py` | Main analysis script |
| `README.md` | This file |

---

## Related Documents

| Document | Description |
|----------|-------------|
| [TESTING_MAP.md](../../../../docs/maps/TESTING_MAP.md) | Search Type #6 specification |
| [drift_calculator.py](../1_CALIBRATION/lib/drift_calculator.py) | Canonical drift calculation |
| [S7_run_023b_CURRENT.json](../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json) | Source data |
| [5_METHODOLOGY_DOMAINS.md](../0_docs/specs/5_METHODOLOGY_DOMAINS.md) | Cosine methodology reference |

---

**Last Updated:** 2025-12-27
