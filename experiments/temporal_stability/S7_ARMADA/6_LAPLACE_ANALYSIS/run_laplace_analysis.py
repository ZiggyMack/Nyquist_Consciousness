"""
Laplace Pole-Zero Analysis for S7 ARMADA Drift Data

This script performs POST-HOC system identification on drift time-series to extract:
- Poles (system eigenvalues, decay rates, stability margins)
- Zeros (system nulls, cancellation points)
- Transfer function characteristics

Uses multiple methods:
1. ARMA modeling - autoregressive models for pole extraction
2. Prony analysis - decompose into sum of exponentials
3. Exponential decay fitting - extract recovery rate λ

UPDATED 2025-12-27: Publication-grade enhancements
- AIC/BIC model order selection (AR(1), AR(2), ARMA(2,1))
- Ljung-Box residual whiteness testing
- Bootstrap confidence intervals on poles
- Proper bilinear z-to-s transform option

The key insight: If drift D(t) behaves like a dynamical system, we can model it as:
    D(s) / Input(s) = Transfer Function H(s)

The Event Horizon (0.80) may correspond to a bifurcation point where a pole
crosses the imaginary axis - transitioning from stable to unstable dynamics.

Based on TESTING_MAP.md Search Type #6: Laplace Pole-Zero Analysis
Compatible with all other search types as POST-HOC analysis.
"""

import json
import numpy as np
from pathlib import Path
from datetime import datetime
from scipy import signal
from scipy.optimize import curve_fit
import warnings
warnings.filterwarnings('ignore')

# ============ CANONICAL IMPORTS ============

import sys
sys.path.insert(0, str(Path(__file__).parent.parent / "1_CALIBRATION" / "lib"))

try:
    from drift_calculator import (
        EVENT_HORIZON,
        THRESHOLD_WARNING,
        THRESHOLD_CATASTROPHIC
    )
except ImportError:
    # Fallback if drift_calculator not available
    EVENT_HORIZON = 0.80
    THRESHOLD_WARNING = 0.60
    THRESHOLD_CATASTROPHIC = 1.20

# ============ CONFIG ============

SCRIPT_DIR = Path(__file__).parent
OUTPUT_DIR = SCRIPT_DIR / "results"
VIZ_DIR = SCRIPT_DIR.parent / "visualizations" / "pics" / "16_Laplace_Analysis"

# Data sources ranked by suitability for Laplace analysis
DATA_SOURCES = {
    "jade": {
        "path": SCRIPT_DIR.parent / "17_JADE_LATTICE" / "results",
        "description": "JADE LATTICE (115 sessions, 56 pts/traj) - PUBLICATION GRADE",
        "is_jade": True  # Special handling for multi-file JADE format
    },
    "023": {
        "path": SCRIPT_DIR.parent / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023_COMBINED.json",
        "description": "COMBINED (825 results, ~14 pts/traj) - BEST balance"
    },
    "020B": {
        "path": SCRIPT_DIR.parent / "11_CONTEXT_DAMPING" / "results" / "S7_run_020B_CURRENT.json",
        "description": "Context Damping (69 results, ~29 pts/traj) - longest trajectories"
    },
    "023d": {
        "path": SCRIPT_DIR.parent / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023d_CURRENT.json",
        "description": "Extended recovery (750 results, ~14 pts/traj)"
    },
    "023e": {
        "path": SCRIPT_DIR.parent / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023e_CURRENT.json",
        "description": "Latest run (75 results, ~14 pts/traj)"
    },
    "023b": {
        "path": SCRIPT_DIR.parent / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023b_CURRENT.json",
        "description": "Large sample (4505 results, ~5 pts/traj) - statistical power but short trajectories"
    }
}

# Default to Run 023 COMBINED - best balance of sample size and trajectory length
DEFAULT_SOURCE = "023"

# Filtering thresholds
LAMBDA_CAP = 5.0  # Upper bound from curve_fit - values at cap are uninformative
LAMBDA_CAP_THRESHOLD = 4.9  # Values above this are considered "maxed out"
MIN_TRAJECTORY_LENGTH = 6  # Minimum points for reliable pole extraction

# ============ MODEL SELECTION (AIC/BIC) ============

def calculate_aic_bic(n: int, k: int, rss: float) -> tuple:
    """
    Calculate AIC and BIC for model selection.

    Args:
        n: Number of observations
        k: Number of parameters
        rss: Residual sum of squares

    Returns:
        (AIC, BIC) tuple
    """
    if n <= k or rss <= 0:
        return float('inf'), float('inf')

    # Log-likelihood (assuming Gaussian errors)
    log_likelihood = -n / 2 * (np.log(2 * np.pi * rss / n) + 1)

    # AIC = -2*LL + 2*k
    aic = -2 * log_likelihood + 2 * k

    # BIC = -2*LL + k*log(n)
    bic = -2 * log_likelihood + k * np.log(n)

    return aic, bic


def ljung_box_test(residuals: np.ndarray, lags: int = 10) -> dict:
    """
    Ljung-Box test for residual whiteness (autocorrelation).

    A significant result (p < 0.05) indicates residuals are NOT white noise,
    suggesting the model is inadequate.

    Args:
        residuals: Model residuals
        lags: Number of lags to test

    Returns:
        dict with Q statistic, p-value, and interpretation
    """
    n = len(residuals)
    if n < lags + 5:
        return {"error": "Too few observations for Ljung-Box test", "is_white": None}

    # Calculate autocorrelations
    residuals = residuals - np.mean(residuals)
    var = np.var(residuals)
    if var == 0:
        return {"error": "Zero variance in residuals", "is_white": None}

    acf = np.correlate(residuals, residuals, mode='full')
    acf = acf[n-1:] / (var * n)  # Normalize

    # Ljung-Box Q statistic
    Q = 0
    for k in range(1, min(lags + 1, len(acf))):
        Q += (acf[k] ** 2) / (n - k)
    Q = n * (n + 2) * Q

    # Chi-squared p-value (lags degrees of freedom)
    from scipy import stats
    p_value = 1 - stats.chi2.cdf(Q, lags)

    return {
        "Q_statistic": float(Q),
        "p_value": float(p_value),
        "lags": lags,
        "is_white": bool(p_value > 0.05),  # Null hypothesis: residuals are white
        "interpretation": "Residuals appear white (model adequate)" if p_value > 0.05
                          else "Residuals show autocorrelation (model may be inadequate)"
    }


def fit_ar_model(drifts: np.ndarray, order: int) -> dict:
    """
    Fit AR(p) model and return results with AIC/BIC.

    Args:
        drifts: Drift time series
        order: AR model order (p)

    Returns:
        dict with coefficients, poles, fit metrics, AIC/BIC
    """
    n = len(drifts)
    if n < order + 3:
        return {"error": f"Too few points for AR({order})"}

    try:
        # Build regression matrix
        X = np.zeros((n - order, order))
        y = drifts[order:]

        for i in range(order):
            X[:, i] = drifts[order - i - 1:n - i - 1]

        # Solve least squares
        coeffs, residuals, rank, s = np.linalg.lstsq(X, y, rcond=None)

        # Predictions and residuals
        y_pred = X @ coeffs
        resid = y - y_pred

        # Calculate RSS and R²
        rss = np.sum(resid ** 2)
        ss_tot = np.sum((y - np.mean(y)) ** 2)
        R2 = 1 - (rss / ss_tot) if ss_tot > 0 else 0

        # AIC/BIC
        k = order + 1  # AR coefficients + variance
        aic, bic = calculate_aic_bic(len(y), k, rss)

        # Find poles
        poly = np.zeros(order + 1)
        poly[0] = 1
        poly[1:] = -coeffs
        poles = np.roots(poly)

        # Convert to continuous-time (bilinear transform approximation)
        # z = (1 + s*T/2) / (1 - s*T/2) => s = 2/T * (z-1)/(z+1)
        # For T=1: s = 2 * (z-1)/(z+1)
        continuous_poles = []
        for z in poles:
            if np.abs(z + 1) > 1e-10:
                s = 2 * (z - 1) / (z + 1)
                continuous_poles.append(s)
            else:
                # z = -1 maps to infinity
                continuous_poles.append(complex(float('inf'), 0))

        # Ljung-Box test on residuals
        lb_test = ljung_box_test(resid)

        return {
            "order": order,
            "ar_coeffs": [float(c) for c in coeffs],
            "poles_discrete": [{"real": float(p.real), "imag": float(p.imag)} for p in poles],
            "poles": [{"real": float(p.real), "imag": float(p.imag)} for p in continuous_poles
                      if np.isfinite(p.real)],
            "R2": float(R2),
            "AIC": float(aic),
            "BIC": float(bic),
            "ljung_box": lb_test,
            "stability": all(np.abs(poles) < 1)  # Discrete stability: all poles inside unit circle
        }

    except Exception as e:
        return {"error": str(e)}


def select_best_ar_order(drifts: np.ndarray, max_order: int = 4, criterion: str = "BIC") -> dict:
    """
    Select best AR model order using AIC or BIC.

    Args:
        drifts: Drift time series
        max_order: Maximum order to consider
        criterion: "AIC" or "BIC"

    Returns:
        dict with best order and comparison table
    """
    results = []
    drifts = np.array(drifts)

    for order in range(1, max_order + 1):
        if len(drifts) < order + 5:
            continue

        fit = fit_ar_model(drifts, order)
        if "error" not in fit:
            results.append({
                "order": order,
                "AIC": fit["AIC"],
                "BIC": fit["BIC"],
                "R2": fit["R2"],
                "is_white": fit["ljung_box"].get("is_white")
            })

    if not results:
        return {"error": "Could not fit any AR model", "best_order": None}

    # Select best by criterion
    if criterion == "AIC":
        best = min(results, key=lambda x: x["AIC"])
    else:  # BIC
        best = min(results, key=lambda x: x["BIC"])

    return {
        "best_order": best["order"],
        "criterion": criterion,
        "comparison": results,
        "best_metrics": best
    }


def bootstrap_pole_ci(drifts: np.ndarray, order: int = 2, n_bootstrap: int = 100) -> dict:
    """
    Bootstrap confidence intervals for pole estimates.

    Args:
        drifts: Drift time series
        order: AR model order
        n_bootstrap: Number of bootstrap samples

    Returns:
        dict with pole estimates and 95% CIs
    """
    drifts = np.array(drifts)
    n = len(drifts)

    if n < order + 5:
        return {"error": "Too few points for bootstrap"}

    # Collect pole estimates from bootstrap samples
    real_parts = []
    imag_parts = []

    for _ in range(n_bootstrap):
        # Resample with replacement (block bootstrap for time series)
        block_size = max(3, n // 5)
        n_blocks = n // block_size + 1
        indices = []
        for _ in range(n_blocks):
            start = np.random.randint(0, max(1, n - block_size))
            indices.extend(range(start, min(start + block_size, n)))
        indices = indices[:n]

        boot_drifts = drifts[indices]

        # Fit AR model
        fit = fit_ar_model(boot_drifts, order)
        if "error" not in fit and fit.get("poles"):
            for pole in fit["poles"]:
                real_parts.append(pole["real"])
                imag_parts.append(pole["imag"])

    if not real_parts:
        return {"error": "Bootstrap failed - no valid pole estimates"}

    # Calculate 95% CI
    real_parts = np.array(real_parts)
    imag_parts = np.array(imag_parts)

    return {
        "n_bootstrap": n_bootstrap,
        "pole_mean_real": float(np.mean(real_parts)),
        "pole_mean_imag": float(np.mean(imag_parts)),
        "ci_real_95": (float(np.percentile(real_parts, 2.5)), float(np.percentile(real_parts, 97.5))),
        "ci_imag_95": (float(np.percentile(imag_parts, 2.5)), float(np.percentile(imag_parts, 97.5))),
        "ci_real_width": float(np.percentile(real_parts, 97.5) - np.percentile(real_parts, 2.5)),
        "ci_imag_width": float(np.percentile(imag_parts, 97.5) - np.percentile(imag_parts, 2.5)),
    }

# ============ DATA LOADING ============

def load_run_data(source: str = None) -> tuple:
    """
    Load run data from configured source.

    Returns: (data_dict, source_name, source_path)
    """
    if source is None:
        source = DEFAULT_SOURCE

    if source not in DATA_SOURCES:
        raise ValueError(f"Unknown source: {source}. Available: {list(DATA_SOURCES.keys())}")

    source_info = DATA_SOURCES[source]
    filepath = source_info["path"]

    # Special handling for JADE LATTICE (multi-file format)
    if source_info.get("is_jade"):
        return load_jade_lattice_data(filepath), source, filepath

    with open(filepath, 'r') as f:
        return json.load(f), source, filepath


def load_jade_lattice_data(results_dir: Path) -> dict:
    """
    Load JADE LATTICE multi-file results and convert to standard format.

    JADE LATTICE has 56 probes per session (Phase A: 19, Phase B: 17, Phase C: 20).
    This is the highest trajectory length in the dataset - ideal for Laplace analysis.

    Returns dict in format compatible with extract_drift_series.
    """
    sessions = []

    # Load all jade session files
    for json_file in results_dir.glob("jade_*.json"):
        # Skip incremental saves and analysis summaries
        if json_file.name.startswith("jade_incremental_"):
            continue
        if json_file.name.startswith("jade_analysis_"):
            continue

        try:
            with open(json_file, 'r', encoding='utf-8') as f:
                session = json.load(f)

            # Extract drift trajectory from all phases
            drift_sequence = []
            phases = session.get("phases", {})

            for phase_key in ["A", "B", "C"]:
                phase_data = phases.get(phase_key, {})
                exchanges = phase_data.get("exchanges", [])
                for ex in exchanges:
                    if ex.get("drift") is not None:
                        drift_sequence.append(ex["drift"])

            if len(drift_sequence) < MIN_TRAJECTORY_LENGTH:
                continue

            # Determine stability status from summary
            summary = session.get("summary", {})
            peak_drift = summary.get("peak_drift", max(drift_sequence) if drift_sequence else 0)
            event_horizon_crossed = summary.get("event_horizon_crossed", False)

            if peak_drift < EVENT_HORIZON:
                status = "STABLE"
            elif event_horizon_crossed:
                status = "STUCK"
            else:
                status = "RECOVERED"

            sessions.append({
                "ship": session.get("ship", "unknown"),
                "provider": session.get("provider", "unknown"),
                "arm": session.get("context_mode", "unknown"),  # bare_metal or i_am_only
                "drift_sequence": drift_sequence,
                "stability": status,
                "peak_drift": peak_drift,
                "final_drift": drift_sequence[-1] if drift_sequence else 0,
                "zone": "jade_lattice",
                "session_id": session.get("session_id", json_file.stem),
            })

        except Exception as e:
            print(f"  [WARN] Error loading {json_file.name}: {e}")
            continue

    print(f"  [JADE] Loaded {len(sessions)} sessions with ~56 pts/trajectory")
    return {"results": sessions, "experiment": "jade_lattice", "format": "jade"}

def extract_drift_series(run_data: dict) -> list:
    """
    Extract drift time-series from run data.

    Supports multiple formats:
    - Run 020B format: results[] with drift_sequence[] (BEST for Laplace - long trajectories)
    - Run 023b format: results[] list with probe_sequence[]
    - Run 023 format: sessions[] with exchanges[]
    - Run 009 format: trajectories_for_3d[]
    """
    trajectories = []

    # Check for Run 020B format (results list with drift_sequence)
    if "results" in run_data and isinstance(run_data["results"], list):
        first_result = run_data["results"][0] if run_data["results"] else {}

        # Run 020B has drift_sequence (longer trajectories - better for Laplace)
        if "drift_sequence" in first_result:
            for result in run_data["results"]:
                drifts = result.get("drift_sequence", [])
                if not drifts or len(drifts) < 4:
                    continue

                # Use existing stability classification
                stability = result.get("stability", "unknown")
                if stability in ["stable", "STABLE"]:
                    status = "STABLE"
                elif stability in ["recovered", "RECOVERED", "volatile", "VOLATILE"]:
                    status = "RECOVERED"
                elif stability in ["stuck", "STUCK", "critical", "CRITICAL"]:
                    status = "STUCK"
                else:
                    # Determine from trajectory
                    max_drift = max(drifts) if drifts else 0
                    final_drift = drifts[-1] if drifts else 0
                    if max_drift < EVENT_HORIZON:
                        status = "STABLE"
                    elif final_drift < EVENT_HORIZON:
                        status = "RECOVERED"
                    else:
                        status = "STUCK"

                trajectories.append({
                    "ship": result.get("ship", "unknown"),
                    "provider": result.get("arm", "unknown"),  # arm = experimental condition
                    "protocol": run_data.get("experiment", "context_damping"),
                    "drifts": drifts,
                    "status": status,
                    "baseline": 0.0,
                    "peak_drift": result.get("peak_drift", max(drifts) if drifts else 0),
                    "settled_drift": result.get("final_drift", drifts[-1] if drifts else 0),
                    "zone": result.get("zone", "unknown")
                })

        # Run 023b has probe_sequence (shorter trajectories)
        elif "probe_sequence" in first_result:
            for result in run_data["results"]:
                probe_sequence = result.get("probe_sequence", [])
                if not probe_sequence:
                    continue

                drifts = [probe.get("drift", 0.0) for probe in probe_sequence]

                # Skip trajectories too short for reliable pole extraction
                if len(drifts) < MIN_TRAJECTORY_LENGTH:
                    continue
                stability = result.get("stability_classification", "unknown")

                if stability in ["stable", "STABLE"]:
                    status = "STABLE"
                elif stability in ["recovered", "RECOVERED", "volatile"]:
                    status = "RECOVERED"
                elif stability in ["stuck", "STUCK", "critical"]:
                    status = "STUCK"
                else:
                    max_drift = max(drifts) if drifts else 0
                    final_drift = drifts[-1] if drifts else 0
                    if max_drift < EVENT_HORIZON:
                        status = "STABLE"
                    elif final_drift < EVENT_HORIZON:
                        status = "RECOVERED"
                    else:
                        status = "STUCK"

                trajectories.append({
                    "ship": result.get("model", "unknown"),
                    "provider": result.get("provider", "unknown"),
                    "protocol": result.get("experiment", "unknown"),
                    "drifts": drifts,
                    "status": status,
                    "baseline": 0.0,
                    "peak_drift": result.get("peak_drift", max(drifts) if drifts else 0),
                    "settled_drift": result.get("settled_drift", drifts[-1] if drifts else 0)
                })

    # Check for Run 023 format (sessions with exchanges)
    elif "sessions" in run_data:
        for session in run_data["sessions"]:
            # Skip invalid sessions
            if session.get("status") == "INVALID":
                continue

            # Extract drift values from exchanges
            exchanges = session.get("exchanges", [])
            if not exchanges:
                continue

            # Build drift series from exchanges
            drifts = [ex.get("drift", 0.0) for ex in exchanges]

            # Determine status based on trajectory behavior
            max_drift = max(drifts) if drifts else 0
            final_drift = drifts[-1] if drifts else 0

            if max_drift < EVENT_HORIZON:
                status = "STABLE"
            elif final_drift < EVENT_HORIZON:
                status = "RECOVERED"
            else:
                status = "STUCK"

            trajectories.append({
                "ship": session.get("model", "unknown"),
                "provider": session.get("provider", "unknown"),
                "protocol": session.get("scenario", "unknown"),
                "drifts": drifts,
                "status": status,
                "baseline": 0.0,  # Cosine methodology: first response is baseline (drift=0)
                "session_id": session.get("session_id", "unknown")
            })

    # Check for Run 009 format (trajectories_for_3d)
    elif "trajectories_for_3d" in run_data:
        for traj in run_data["trajectories_for_3d"]:
            trajectories.append({
                "ship": traj["ship"],
                "provider": traj["provider"],
                "protocol": traj.get("protocol", "unknown"),
                "drifts": traj["drifts"],
                "status": traj["status"],
                "baseline": traj["baseline"]
            })

    return trajectories

# ============ ANALYSIS METHODS ============

def exponential_decay(t, A, lambda_val, C):
    """Exponential decay model: D(t) = A * exp(-lambda * t) + C"""
    return A * np.exp(-lambda_val * t) + C

def fit_exponential_recovery(drifts: list, recovery_start: int = None) -> dict:
    """
    Fit exponential decay to recovery phase.

    If recovery_start is None, auto-detect by finding max drift point.
    Returns lambda (decay rate) and fit quality (R²).
    """
    if len(drifts) < 4:
        return {"lambda": None, "R2": None, "error": "Too few points"}

    drifts = np.array(drifts)

    # Auto-detect recovery start (point after max drift)
    if recovery_start is None:
        recovery_start = np.argmax(drifts)

    # Need at least 3 points for recovery fit
    if len(drifts) - recovery_start < 3:
        return {"lambda": None, "R2": None, "error": "Insufficient recovery points"}

    recovery = drifts[recovery_start:]
    t = np.arange(len(recovery))

    try:
        # Initial guesses
        A0 = recovery[0] - recovery[-1]
        C0 = recovery[-1]
        lambda0 = 0.3

        popt, _ = curve_fit(
            exponential_decay, t, recovery,
            p0=[A0, lambda0, C0],
            bounds=([0, 0, 0], [np.inf, 5, np.inf]),
            maxfev=1000
        )

        A, lambda_val, C = popt

        # Calculate R²
        fitted = exponential_decay(t, A, lambda_val, C)
        ss_res = np.sum((recovery - fitted) ** 2)
        ss_tot = np.sum((recovery - np.mean(recovery)) ** 2)
        R2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0

        # Flag if lambda hit the cap (uninformative - we don't know true value)
        maxed_out = bool(lambda_val >= LAMBDA_CAP_THRESHOLD)

        return {
            "lambda": float(lambda_val),
            "A": float(A),
            "C": float(C),
            "R2": float(R2),
            "recovery_start": int(recovery_start),
            "pole_location": float(-lambda_val),  # Pole at s = -lambda
            "maxed_out": maxed_out  # True if hit the cap - exclude from analysis
        }

    except Exception as e:
        return {"lambda": None, "R2": None, "error": str(e)}

def arma_pole_extraction(drifts: list, order: int = 2) -> dict:
    """
    Fit AR(p) model to drift series and extract poles.

    For an AR(p) model: y[t] = a1*y[t-1] + a2*y[t-2] + ... + ap*y[t-p] + e[t]

    Poles are roots of the characteristic polynomial:
    z^p - a1*z^(p-1) - a2*z^(p-2) - ... - ap = 0
    """
    if len(drifts) < order + 3:
        return {"poles": [], "error": "Too few points for AR model"}

    drifts = np.array(drifts)

    try:
        # Build regression matrix for AR model
        n = len(drifts)
        X = np.zeros((n - order, order))
        y = drifts[order:]

        for i in range(order):
            X[:, i] = drifts[order - i - 1:n - i - 1]

        # Solve least squares
        coeffs, _, _, _ = np.linalg.lstsq(X, y, rcond=None)

        # Build characteristic polynomial: z^p - a1*z^(p-1) - ... - ap
        poly = np.zeros(order + 1)
        poly[0] = 1
        poly[1:] = -coeffs

        # Find roots (poles)
        poles = np.roots(poly)

        # Convert to continuous-time equivalent (assuming unit sampling)
        # z = exp(s*T), so s = log(z)/T (T=1)
        continuous_poles = np.log(np.clip(np.abs(poles), 1e-10, None)) + 1j * np.angle(poles)

        # Calculate model fit
        y_pred = X @ coeffs
        ss_res = np.sum((y - y_pred) ** 2)
        ss_tot = np.sum((y - np.mean(y)) ** 2)
        R2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0

        return {
            "poles": [{"real": float(p.real), "imag": float(p.imag)} for p in continuous_poles],
            "ar_coeffs": [float(c) for c in coeffs],
            "R2": float(R2),
            "stability": all(np.real(continuous_poles) < 0)
        }

    except Exception as e:
        return {"poles": [], "error": str(e)}

def prony_analysis(drifts: list, n_components: int = 2) -> dict:
    """
    Prony analysis: decompose signal into sum of exponentials.

    D(t) = sum_i(A_i * exp((sigma_i + j*omega_i) * t))

    where sigma = decay rate, omega = oscillation frequency
    """
    if len(drifts) < 2 * n_components + 2:
        return {"components": [], "error": "Too few points for Prony analysis"}

    drifts = np.array(drifts)
    n = len(drifts)

    try:
        # Build Hankel matrix
        m = n // 2
        H = np.zeros((m, n_components))
        for i in range(m):
            for j in range(n_components):
                if i + j < n:
                    H[i, j] = drifts[i + j]

        # SVD to find dominant modes
        U, S, Vh = np.linalg.svd(H, full_matrices=False)

        # Use SVD to estimate exponential components
        components = []
        for i in range(min(n_components, len(S))):
            if S[i] > 1e-10:  # Only significant components
                # Approximate sigma from decay of singular values
                sigma = -np.log(S[i] / S[0]) / (i + 1) if i > 0 else 0
                components.append({
                    "index": i,
                    "sigma": float(sigma),
                    "omega": 0.0,  # Simplified - would need more complex analysis for oscillations
                    "amplitude": float(S[i]),
                    "pole_location": {"real": float(-sigma), "imag": 0.0}
                })

        return {
            "components": components,
            "n_significant": len(components),
            "singular_values": [float(s) for s in S[:n_components]]
        }

    except Exception as e:
        return {"components": [], "error": str(e)}

def classify_trajectory(analysis: dict) -> dict:
    """
    Classify trajectory based on pole locations.

    - Poles in left half-plane (Re(s) < 0) = stable
    - Poles near imaginary axis = marginally stable
    - Poles in right half-plane (Re(s) > 0) = unstable
    """
    classification = {
        "stability": "UNKNOWN",
        "dominant_pole": None,
        "decay_rate": None,
        "oscillatory": False
    }

    # From exponential fit
    if analysis.get("exponential", {}).get("lambda"):
        lambda_val = analysis["exponential"]["lambda"]
        classification["decay_rate"] = lambda_val
        classification["dominant_pole"] = -lambda_val

        if lambda_val > 0.1:
            classification["stability"] = "STABLE"
        elif lambda_val > 0:
            classification["stability"] = "MARGINAL"
        else:
            classification["stability"] = "UNSTABLE"

    # From ARMA poles
    if analysis.get("arma", {}).get("poles"):
        poles = analysis["arma"]["poles"]
        real_parts = [p["real"] for p in poles]
        imag_parts = [p["imag"] for p in poles]

        # Check for oscillatory behavior
        if any(abs(im) > 0.1 for im in imag_parts):
            classification["oscillatory"] = True

        # Dominant pole is one closest to imaginary axis (slowest decay)
        if real_parts:
            max_real = max(real_parts)
            classification["dominant_pole"] = max_real

            if max_real < -0.1:
                classification["stability"] = "STABLE"
            elif max_real < 0:
                classification["stability"] = "MARGINAL"
            else:
                classification["stability"] = "UNSTABLE"

    return classification

# ============ MAIN ANALYSIS ============

def analyze_trajectory(traj: dict, use_model_selection: bool = True) -> dict:
    """
    Run full Laplace analysis on a single trajectory.

    Args:
        traj: Trajectory dict with drifts, ship, provider, etc.
        use_model_selection: If True, use AIC/BIC to select best AR order

    Returns:
        Analysis results dict
    """
    drifts = traj["drifts"]

    result = {
        "ship": traj["ship"],
        "provider": traj["provider"],
        "protocol": traj["protocol"],
        "status": traj["status"],
        "n_points": len(drifts),
        "baseline": traj["baseline"],
        "peak_drift": max(drifts) if drifts else None,
        "final_drift": drifts[-1] if drifts else None
    }

    # Method 1: Exponential recovery fit
    result["exponential"] = fit_exponential_recovery(drifts)

    # Method 2: ARMA pole extraction with model selection
    if use_model_selection and len(drifts) >= 10:
        # Use AIC/BIC to select best order
        model_selection = select_best_ar_order(np.array(drifts), max_order=4, criterion="BIC")
        result["model_selection"] = model_selection

        best_order = model_selection.get("best_order", 2)
        if best_order:
            ar_result = fit_ar_model(np.array(drifts), best_order)
            result["arma"] = ar_result

            # Add bootstrap CI for poles if we have enough points
            if len(drifts) >= 15 and "error" not in ar_result:
                bootstrap_ci = bootstrap_pole_ci(np.array(drifts), order=best_order, n_bootstrap=50)
                result["bootstrap_ci"] = bootstrap_ci

                # Attach CI to poles for visualization
                if "error" not in bootstrap_ci and ar_result.get("poles"):
                    for pole in ar_result["poles"]:
                        pole["ci_real"] = bootstrap_ci.get("ci_real_width", 0.1) / 2
                        pole["ci_imag"] = bootstrap_ci.get("ci_imag_width", 0.1) / 2
        else:
            result["arma"] = arma_pole_extraction(drifts, order=2)
    else:
        # Fallback to hardcoded AR(2)
        result["arma"] = arma_pole_extraction(drifts, order=2)

    # Method 3: Prony analysis
    result["prony"] = prony_analysis(drifts, n_components=2)

    # Classification
    result["classification"] = classify_trajectory(result)

    return result

def analyze_run(run_data: dict, run_name: str) -> dict:
    """Analyze all trajectories in a run."""
    trajectories = extract_drift_series(run_data)

    print(f"\n{'='*60}")
    print(f"Analyzing {run_name}: {len(trajectories)} trajectories")
    print('='*60)

    results = []

    for traj in trajectories:
        analysis = analyze_trajectory(traj)
        results.append(analysis)

        # Print summary
        lambda_val = analysis["exponential"].get("lambda")
        stability = analysis["classification"]["stability"]
        lam_str = f"{lambda_val:.3f}" if lambda_val is not None else "N/A"
        print(f"  {analysis['ship'][:20]:<20} | lam={lam_str:<8} | {stability}")

    # Aggregate statistics (exclude maxed-out values - they're uninformative)
    lambdas_all = [r["exponential"]["lambda"] for r in results if r["exponential"].get("lambda")]
    lambdas_valid = [r["exponential"]["lambda"] for r in results
                    if r["exponential"].get("lambda") and not r["exponential"].get("maxed_out", False)]
    n_maxed_out = len([r for r in results if r["exponential"].get("maxed_out", False)])

    stabilities = [r["classification"]["stability"] for r in results]

    summary = {
        "run_name": run_name,
        "n_trajectories": len(results),
        "n_maxed_out": n_maxed_out,  # Count of trajectories that hit lambda cap
        "lambda_stats": {
            "mean": float(np.mean(lambdas_valid)) if lambdas_valid else None,
            "std": float(np.std(lambdas_valid)) if lambdas_valid else None,
            "min": float(np.min(lambdas_valid)) if lambdas_valid else None,
            "max": float(np.max(lambdas_valid)) if lambdas_valid else None,
            "n_valid": len(lambdas_valid),
            "n_excluded": n_maxed_out
        },
        "stability_distribution": {
            "STABLE": stabilities.count("STABLE"),
            "MARGINAL": stabilities.count("MARGINAL"),
            "UNSTABLE": stabilities.count("UNSTABLE"),
            "UNKNOWN": stabilities.count("UNKNOWN")
        },
        "trajectories": results
    }

    return summary

def compare_stable_vs_volatile(run_009_results: dict) -> dict:
    """
    Compare pole locations for STABLE vs VOLATILE trajectories.

    Key question: Do VOLATILE trajectories have poles closer to imaginary axis?
    """
    stable = [t for t in run_009_results["trajectories"] if t["status"] == "STABLE"]
    volatile = [t for t in run_009_results["trajectories"] if t["status"] in ["VOLATILE", "RECOVERED"]]
    stuck = [t for t in run_009_results["trajectories"] if t["status"] == "STUCK"]

    def get_stats(trajectories, label):
        lambdas = [t["exponential"]["lambda"] for t in trajectories if t["exponential"].get("lambda")]
        poles = []
        for t in trajectories:
            if t["arma"].get("poles"):
                poles.extend([p["real"] for p in t["arma"]["poles"]])

        return {
            "label": label,
            "count": len(trajectories),
            "lambda_mean": float(np.mean(lambdas)) if lambdas else None,
            "lambda_std": float(np.std(lambdas)) if lambdas else None,
            "pole_mean": float(np.mean(poles)) if poles else None,
            "pole_std": float(np.std(poles)) if poles else None
        }

    return {
        "stable": get_stats(stable, "STABLE"),
        "recovered": get_stats(volatile, "RECOVERED"),
        "stuck": get_stats(stuck, "STUCK"),
        "hypothesis": "STUCK trajectories should have poles closer to 0 (slower decay)"
    }

# ============ VISUALIZATION ============

def print_pole_zero_map(results: dict):
    """Print ASCII pole-zero map."""
    print("\n" + "="*60)
    print("POLE-ZERO MAP (Real axis)")
    print("="*60)
    print("  UNSTABLE  |  MARGINAL  |    STABLE")
    print("    Re>0    |   -0.1<Re<0   |   Re<-0.1")
    print("-"*60)

    for r in results["trajectories"][:10]:  # First 10
        pole = r["classification"].get("dominant_pole")
        if pole is not None:
            # Map pole to position
            pos = int((pole + 1) * 25)  # Scale to 0-50
            pos = max(0, min(49, pos))

            line = [" "] * 50
            line[25] = "|"  # Imaginary axis
            line[pos] = "x"

            print(f"{''.join(line)} {r['ship'][:15]}")

# ============ MAIN ============

def main(source: str = None):
    """
    Run Laplace pole-zero analysis.

    Args:
        source: Data source key ("020B", "023b", "018"). Default: "020B"
    """
    print("="*60)
    print("LAPLACE POLE-ZERO ANALYSIS")
    print("S7 ARMADA - Search Type #6")
    print(f"Event Horizon: {EVENT_HORIZON}")
    print("="*60)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Ensure output directory exists
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Load data
    print(f"\nAvailable data sources:")
    for key, info in DATA_SOURCES.items():
        marker = " <-- DEFAULT" if key == DEFAULT_SOURCE else ""
        print(f"  {key}: {info['description']}{marker}")

    try:
        run_data, source_name, source_path = load_run_data(source)
        print(f"\nLoading: {source_name}")
        print(f"Path: {source_path}")
    except FileNotFoundError as e:
        print(f"Error loading data: {e}")
        return

    # Analyze trajectories
    results = analyze_run(run_data, f"Run {source_name} (Cosine Methodology)")

    # Compare stable vs volatile
    comparison = compare_stable_vs_volatile(results)

    print("\n" + "="*60)
    print("STABLE vs STUCK COMPARISON")
    print("="*60)
    print(f"\nSTABLE trajectories (never crossed EH={EVENT_HORIZON}):")
    print(f"  Count: {comparison['stable']['count']}")
    if comparison['stable']['lambda_mean']:
        print(f"  Mean lambda: {comparison['stable']['lambda_mean']:.4f}")

    print(f"\nRECOVERED trajectories (crossed EH but recovered):")
    print(f"  Count: {comparison['recovered']['count']}")
    if comparison['recovered']['lambda_mean']:
        print(f"  Mean lambda: {comparison['recovered']['lambda_mean']:.4f}")

    print(f"\nSTUCK trajectories (crossed EH and stayed there):")
    print(f"  Count: {comparison['stuck']['count']}")
    if comparison['stuck']['lambda_mean']:
        print(f"  Mean lambda: {comparison['stuck']['lambda_mean']:.4f}")

    # Print pole map
    print_pole_zero_map(results)

    # Save results
    output = {
        "timestamp": timestamp,
        "methodology": "cosine_embedding",
        "event_horizon": EVENT_HORIZON,
        "source": source_name,
        "source_file": str(source_path),
        "analysis": results,
        "comparison": comparison
    }

    output_file = OUTPUT_DIR / f"laplace_analysis_{source_name}_{timestamp}.json"
    with open(output_file, 'w') as f:
        json.dump(output, f, indent=2)

    print(f"\n[OK] Results saved to: {output_file}")

    # Summary
    print("\n" + "="*60)
    print("KEY FINDINGS")
    print("="*60)

    if comparison['recovered']['lambda_mean'] and comparison['stuck']['lambda_mean']:
        ratio = comparison['recovered']['lambda_mean'] / comparison['stuck']['lambda_mean']
        print(f"Lambda ratio (RECOVERED/STUCK): {ratio:.2f}x")
        if ratio > 1.5:
            print("-> RECOVERED trajectories have faster decay (more stable poles)")
        elif ratio < 0.67:
            print("-> STUCK trajectories have faster decay (unexpected!)")
        else:
            print("-> No significant difference in decay rates")

    print("\n" + "="*60)
    print("PREDICTIONS TO VALIDATE")
    print("="*60)
    print(f"P-LAP-1: Poles can be extracted from drift time-series")
    print(f"P-LAP-2: lambda > 0 indicates stable recovery dynamics")
    print(f"P-LAP-3: ARMA(2) captures drift dynamics adequately")
    print(f"P-LAP-4: STUCK trajectories have poles closer to 0")
    print(f"\nEvent Horizon ({EVENT_HORIZON}) as bifurcation point:")
    print(f"  - At EH crossing, pole may move toward imaginary axis")
    print(f"  - STUCK = pole crossed to right half-plane (Re(s) > 0)")

if __name__ == "__main__":
    import sys
    source = sys.argv[1] if len(sys.argv) > 1 else None
    main(source)
