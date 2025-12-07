# Laplace Pole-Zero Analysis

**Purpose:** Extract mathematical system dynamics from drift time-series.

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

- Crossing 1.23 should correspond to pole crossing imaginary axis
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

- [TESTING_MAP.md](../../../../docs/maps/TESTING_MAP.md) — Search Type #6 spec
- [run009_drain_capture.py](../3_EVENT_HORIZON/run009_drain_capture.py) — Source data

---

**Last Updated:** 2025-12-07
