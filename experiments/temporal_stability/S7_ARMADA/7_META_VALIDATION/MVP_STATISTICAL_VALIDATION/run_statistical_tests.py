#!/usr/bin/env python3
"""
MVP_STATISTICAL_VALIDATION: Random-Walk Null Model Tests
=========================================================

Implements 5 statistical tests to prove identity drift is NOT random noise:
- Test A: AR(1) Slope Test (Recovery Detection)
- Test B: Variance Growth Test
- Test C: Sign Test (Drift Direction)
- Test D: Omega Exponential Decay
- Test E: Cross-Architecture Variance (already validated in Run 009)

Uses data from Runs 008-013 to validate lawful identity dynamics.
"""

import json
import numpy as np
from pathlib import Path
from datetime import datetime
from scipy import stats
from scipy.optimize import curve_fit
import warnings
warnings.filterwarnings('ignore')

# ============================================================================
# DATA LOADING
# ============================================================================

RESULTS_DIR = Path(__file__).resolve().parent.parent.parent / "0_results" / "runs"

def load_all_runs():
    """Load all available run data."""
    runs = {}
    for f in sorted(RESULTS_DIR.glob("S7_run_*.json")):
        with open(f, encoding='utf-8') as fp:
            data = json.load(fp)
            run_id = data.get("run_id", f.stem)
            runs[run_id] = data
    return runs

def extract_drift_sequences(run_data):
    """Extract drift sequences from run data - handles both old and new formats."""
    sequences = []
    results = run_data.get("results", [])

    # Check if results is a list (new format) or dict (old format)
    if isinstance(results, list):
        # New format: results is a list of ship dicts
        for ship in results:
            ship_name = ship.get("ship", "unknown")
            turns = ship.get("turns", [])
            if turns:
                drift_seq = [t.get("drift", 0) for t in turns]
                sequences.append({
                    "ship": ship_name,
                    "provider": ship.get("provider", "unknown"),
                    "drifts": drift_seq,
                    "turns": list(range(1, len(drift_seq) + 1))
                })
    elif isinstance(results, dict):
        # Old format: results is a dict with ship names as keys
        for ship_name, ship_data in results.items():
            if not isinstance(ship_data, dict):
                continue
            provider = ship_data.get("config", {}).get("provider", "unknown")

            # Try to find drift sequences
            seq_data = ship_data.get("sequences", {})
            curriculum = seq_data.get("s0_s77_curriculum", [])

            if curriculum:
                drift_seq = []
                for turn in curriculum:
                    drift_data = turn.get("drift_data", {})
                    drift = drift_data.get("drift") or drift_data.get("weighted_drift", 0)
                    drift_seq.append(drift)

                if drift_seq:
                    sequences.append({
                        "ship": ship_name,
                        "provider": provider,
                        "drifts": drift_seq,
                        "turns": list(range(1, len(drift_seq) + 1))
                    })

    return sequences

# ============================================================================
# TEST A: AR(1) SLOPE TEST
# ============================================================================

def test_a_ar1_slope(drift_sequence):
    """
    Test A: AR(1) Autoregressive Model

    Model: D_{t+1} = α·D_t + β + ε_t

    Null Hypothesis (Random Walk): α = 1 (no recovery)
    Alternative (Recovery Basin): α < 1 (drift pulls back)

    Returns dict with alpha, p-value, and interpretation.
    """
    drifts = np.array(drift_sequence)
    if len(drifts) < 4:
        return {"status": "insufficient_data", "n": len(drifts)}

    # Prepare lagged data
    D_t = drifts[:-1]  # D(t)
    D_t1 = drifts[1:]  # D(t+1)

    # Fit AR(1): D(t+1) = α*D(t) + β
    try:
        slope, intercept, r_value, p_value, std_err = stats.linregress(D_t, D_t1)

        # Test if α significantly different from 1 (random walk)
        # t-statistic for H0: α = 1
        t_stat = (slope - 1.0) / std_err if std_err > 0 else 0
        df = len(D_t) - 2
        p_alpha_eq_1 = 2 * (1 - stats.t.cdf(abs(t_stat), df))

        interpretation = "random_walk"
        if p_alpha_eq_1 < 0.05:
            if slope < 1:
                interpretation = "recovery_attractor"
            else:
                interpretation = "explosive_drift"

        return {
            "status": "success",
            "alpha": round(slope, 4),
            "beta": round(intercept, 4),
            "r_squared": round(r_value**2, 4),
            "p_value_slope": round(p_value, 6),
            "p_alpha_eq_1": round(p_alpha_eq_1, 6),
            "t_statistic": round(t_stat, 4),
            "interpretation": interpretation,
            "n": len(drifts)
        }
    except Exception as e:
        return {"status": "error", "error": str(e)}

# ============================================================================
# TEST B: VARIANCE GROWTH TEST
# ============================================================================

def saturating_model(t, a, lam):
    """Saturating variance model: Var = a * (1 - exp(-λt))"""
    return a * (1 - np.exp(-lam * t))

def linear_model(t, a, b):
    """Linear variance model: Var = a + b*t"""
    return a + b * t

def test_b_variance_growth(drift_sequence):
    """
    Test B: Variance Growth Test

    Random Walk: Var(D_t - D_0) grows linearly with t
    Attractor: Var(D_t - D_0) saturates

    Compare AIC of linear vs saturating models.
    """
    drifts = np.array(drift_sequence)
    if len(drifts) < 5:
        return {"status": "insufficient_data", "n": len(drifts)}

    D_0 = drifts[0]
    deltas = drifts - D_0
    t = np.arange(1, len(drifts) + 1)

    # Compute cumulative variance at each point
    variances = np.array([np.var(deltas[:i+1]) if i > 0 else 0 for i in range(len(deltas))])

    # Filter out zeros and negative values for fitting
    valid_idx = variances > 0
    if np.sum(valid_idx) < 3:
        return {"status": "insufficient_variance_data"}

    t_valid = t[valid_idx]
    var_valid = variances[valid_idx]

    try:
        # Fit linear model
        popt_lin, _ = curve_fit(linear_model, t_valid, var_valid, p0=[0, 0.1], maxfev=5000)
        pred_lin = linear_model(t_valid, *popt_lin)
        ss_res_lin = np.sum((var_valid - pred_lin)**2)
        aic_lin = len(t_valid) * np.log(ss_res_lin / len(t_valid)) + 2 * 2

        # Fit saturating model
        try:
            popt_sat, _ = curve_fit(saturating_model, t_valid, var_valid,
                                    p0=[np.max(var_valid), 0.1], maxfev=5000,
                                    bounds=([0, 0.001], [np.inf, 10]))
            pred_sat = saturating_model(t_valid, *popt_sat)
            ss_res_sat = np.sum((var_valid - pred_sat)**2)
            aic_sat = len(t_valid) * np.log(ss_res_sat / len(t_valid)) + 2 * 2
        except:
            aic_sat = np.inf
            popt_sat = [np.nan, np.nan]

        # Compare models
        delta_aic = aic_lin - aic_sat
        if delta_aic > 2:
            interpretation = "saturating_attractor"
        elif delta_aic < -2:
            interpretation = "linear_random_walk"
        else:
            interpretation = "inconclusive"

        return {
            "status": "success",
            "aic_linear": round(aic_lin, 4),
            "aic_saturating": round(aic_sat, 4) if not np.isinf(aic_sat) else "failed_to_fit",
            "delta_aic": round(delta_aic, 4) if not np.isinf(aic_sat) else "n/a",
            "linear_params": {"a": round(popt_lin[0], 4), "b": round(popt_lin[1], 4)},
            "saturating_params": {"a": round(popt_sat[0], 4), "lambda": round(popt_sat[1], 4)} if not np.isnan(popt_sat[0]) else "failed",
            "interpretation": interpretation,
            "n": len(drifts)
        }
    except Exception as e:
        return {"status": "error", "error": str(e)}

# ============================================================================
# TEST C: SIGN TEST (DRIFT DIRECTION)
# ============================================================================

def test_c_sign_test(drift_sequence):
    """
    Test C: Sign Test for Drift Direction

    Null: Sign of ΔD_t is 50/50 positive vs negative
    Alternative: Negative changes predominate (recovery)

    Uses binomial test.
    """
    drifts = np.array(drift_sequence)
    if len(drifts) < 4:
        return {"status": "insufficient_data", "n": len(drifts)}

    # Calculate differences
    delta_d = np.diff(drifts)

    # Count positives and negatives (exclude zeros)
    n_positive = np.sum(delta_d > 0)
    n_negative = np.sum(delta_d < 0)
    n_total = n_positive + n_negative

    if n_total < 3:
        return {"status": "insufficient_changes"}

    # Binomial test: H0 = 50/50
    # We're interested in whether negative (recovery) predominates
    # Use binomtest (scipy >= 1.7) or binom_test (older scipy)
    try:
        result = stats.binomtest(n_negative, n_total, 0.5, alternative='greater')
        p_value = result.pvalue
        result_two = stats.binomtest(n_negative, n_total, 0.5, alternative='two-sided')
        p_value_two_sided = result_two.pvalue
    except AttributeError:
        # Fallback for older scipy
        p_value = stats.binom_test(n_negative, n_total, 0.5, alternative='greater')
        p_value_two_sided = stats.binom_test(n_negative, n_total, 0.5, alternative='two-sided')

    prop_negative = n_negative / n_total

    if p_value < 0.05 and prop_negative > 0.5:
        interpretation = "systematic_recovery"
    elif p_value_two_sided < 0.05 and prop_negative < 0.5:
        interpretation = "systematic_drift_increase"
    else:
        interpretation = "random_walk"

    return {
        "status": "success",
        "n_positive": int(n_positive),
        "n_negative": int(n_negative),
        "n_zero": int(len(delta_d) - n_total),
        "proportion_negative": round(prop_negative, 4),
        "p_value_recovery": round(p_value, 6),
        "p_value_two_sided": round(p_value_two_sided, 6),
        "interpretation": interpretation,
        "n": len(drifts)
    }

# ============================================================================
# TEST D: OMEGA EXPONENTIAL DECAY
# ============================================================================

def test_d_omega_decay(drift_sequence, recovery_start_idx=None):
    """
    Test D: Exponential Decay in Recovery Phase

    Hypothesis: D_Ω(t) = D_0 · e^{-λt}

    Fit log(D) vs t and check for linear relationship.
    """
    drifts = np.array(drift_sequence)

    # If recovery start not specified, find max drift point
    if recovery_start_idx is None:
        recovery_start_idx = np.argmax(drifts)

    # Get recovery phase
    recovery_drifts = drifts[recovery_start_idx:]

    if len(recovery_drifts) < 3:
        return {"status": "insufficient_recovery_data", "n_recovery": len(recovery_drifts)}

    # Filter out zeros/negatives for log
    valid_idx = recovery_drifts > 0
    if np.sum(valid_idx) < 3:
        return {"status": "no_positive_values_for_log"}

    t = np.arange(len(recovery_drifts))[valid_idx]
    log_d = np.log(recovery_drifts[valid_idx])

    try:
        # Fit log(D) = log(D_0) - λt
        slope, intercept, r_value, p_value, std_err = stats.linregress(t, log_d)

        # λ = -slope (we expect negative slope for decay)
        lambda_decay = -slope
        r_squared = r_value**2

        # Interpretation
        if lambda_decay > 0 and r_squared >= 0.6:
            interpretation = "exponential_decay_confirmed"
        elif lambda_decay > 0 and r_squared >= 0.4:
            interpretation = "weak_exponential_decay"
        elif lambda_decay <= 0:
            interpretation = "no_decay_or_growth"
        else:
            interpretation = "poor_fit"

        return {
            "status": "success",
            "lambda": round(lambda_decay, 4),
            "r_squared": round(r_squared, 4),
            "p_value": round(p_value, 6),
            "D_0_estimate": round(np.exp(intercept), 4),
            "interpretation": interpretation,
            "recovery_start_idx": int(recovery_start_idx),
            "n_recovery": int(np.sum(valid_idx))
        }
    except Exception as e:
        return {"status": "error", "error": str(e)}

# ============================================================================
# AGGREGATE ANALYSIS
# ============================================================================

def run_all_tests_on_sequence(drift_seq, ship_name="unknown"):
    """Run all 4 tests on a single drift sequence."""
    return {
        "ship": ship_name,
        "test_a_ar1": test_a_ar1_slope(drift_seq),
        "test_b_variance": test_b_variance_growth(drift_seq),
        "test_c_sign": test_c_sign_test(drift_seq),
        "test_d_omega": test_d_omega_decay(drift_seq)
    }

def aggregate_results(all_results):
    """Aggregate test results across all ships."""
    aggregated = {
        "test_a": {"recovery": 0, "random_walk": 0, "explosive": 0, "other": 0},
        "test_b": {"saturating": 0, "linear": 0, "inconclusive": 0, "other": 0},
        "test_c": {"recovery": 0, "drift_increase": 0, "random_walk": 0, "other": 0},
        "test_d": {"decay_confirmed": 0, "weak_decay": 0, "no_decay": 0, "other": 0}
    }

    for result in all_results:
        # Test A
        interp_a = result.get("test_a_ar1", {}).get("interpretation", "other")
        if interp_a == "recovery_attractor":
            aggregated["test_a"]["recovery"] += 1
        elif interp_a == "random_walk":
            aggregated["test_a"]["random_walk"] += 1
        elif interp_a == "explosive_drift":
            aggregated["test_a"]["explosive"] += 1
        else:
            aggregated["test_a"]["other"] += 1

        # Test B
        interp_b = result.get("test_b_variance", {}).get("interpretation", "other")
        if interp_b == "saturating_attractor":
            aggregated["test_b"]["saturating"] += 1
        elif interp_b == "linear_random_walk":
            aggregated["test_b"]["linear"] += 1
        elif interp_b == "inconclusive":
            aggregated["test_b"]["inconclusive"] += 1
        else:
            aggregated["test_b"]["other"] += 1

        # Test C
        interp_c = result.get("test_c_sign", {}).get("interpretation", "other")
        if interp_c == "systematic_recovery":
            aggregated["test_c"]["recovery"] += 1
        elif interp_c == "systematic_drift_increase":
            aggregated["test_c"]["drift_increase"] += 1
        elif interp_c == "random_walk":
            aggregated["test_c"]["random_walk"] += 1
        else:
            aggregated["test_c"]["other"] += 1

        # Test D
        interp_d = result.get("test_d_omega", {}).get("interpretation", "other")
        if interp_d == "exponential_decay_confirmed":
            aggregated["test_d"]["decay_confirmed"] += 1
        elif interp_d == "weak_exponential_decay":
            aggregated["test_d"]["weak_decay"] += 1
        elif interp_d == "no_decay_or_growth":
            aggregated["test_d"]["no_decay"] += 1
        else:
            aggregated["test_d"]["other"] += 1

    return aggregated

# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 70)
    print("MVP STATISTICAL VALIDATION: Random-Walk Null Model Tests")
    print("=" * 70)
    print()

    # Load all runs
    print("Loading run data...")
    runs = load_all_runs()
    print(f"Found {len(runs)} runs")

    all_results = []
    total_sequences = 0

    # Process each run
    for run_id, run_data in runs.items():
        print(f"\n--- {run_id} ---")
        sequences = extract_drift_sequences(run_data)
        print(f"  Ships: {len(sequences)}")

        for seq in sequences:
            if len(seq["drifts"]) >= 4:
                result = run_all_tests_on_sequence(seq["drifts"], seq["ship"])
                result["run_id"] = run_id
                result["provider"] = seq["provider"]
                all_results.append(result)
                total_sequences += 1

    print(f"\n{'=' * 70}")
    print(f"TOTAL SEQUENCES ANALYZED: {total_sequences}")
    print(f"{'=' * 70}")

    # Aggregate results
    aggregated = aggregate_results(all_results)

    # Print summary
    print("\n" + "=" * 70)
    print("TEST A: AR(1) SLOPE (Recovery Detection)")
    print("=" * 70)
    a = aggregated["test_a"]
    total_a = sum(a.values())
    print(f"  Recovery Attractor (a < 1): {a['recovery']}/{total_a} ({100*a['recovery']/total_a:.1f}%)")
    print(f"  Random Walk (a ~ 1):        {a['random_walk']}/{total_a} ({100*a['random_walk']/total_a:.1f}%)")
    print(f"  Explosive (a > 1):          {a['explosive']}/{total_a} ({100*a['explosive']/total_a:.1f}%)")
    print(f"  Other/Error:                {a['other']}/{total_a}")

    # Test A conclusion
    if a['recovery'] > a['random_walk']:
        print(f"  >>> RESULT: RECOVERY ATTRACTOR PREDOMINATES - Reject random walk null")
    else:
        print(f"  >>> RESULT: Cannot reject random walk hypothesis")

    print("\n" + "=" * 70)
    print("TEST B: VARIANCE GROWTH (Saturation vs Linear)")
    print("=" * 70)
    b = aggregated["test_b"]
    total_b = sum(b.values())
    print(f"  Saturating (attractor):     {b['saturating']}/{total_b} ({100*b['saturating']/total_b:.1f}%)")
    print(f"  Linear (random walk):       {b['linear']}/{total_b} ({100*b['linear']/total_b:.1f}%)")
    print(f"  Inconclusive:               {b['inconclusive']}/{total_b} ({100*b['inconclusive']/total_b:.1f}%)")
    print(f"  Other/Error:                {b['other']}/{total_b}")

    if b['saturating'] > b['linear']:
        print(f"  >>> RESULT: SATURATING MODEL FITS BETTER - Identity has attractor")
    else:
        print(f"  >>> RESULT: Linear model fits as well or better")

    print("\n" + "=" * 70)
    print("TEST C: SIGN TEST (Drift Direction)")
    print("=" * 70)
    c = aggregated["test_c"]
    total_c = sum(c.values())
    print(f"  Systematic Recovery:        {c['recovery']}/{total_c} ({100*c['recovery']/total_c:.1f}%)")
    print(f"  Systematic Increase:        {c['drift_increase']}/{total_c} ({100*c['drift_increase']/total_c:.1f}%)")
    print(f"  Random (50/50):             {c['random_walk']}/{total_c} ({100*c['random_walk']/total_c:.1f}%)")
    print(f"  Other/Error:                {c['other']}/{total_c}")

    if c['recovery'] > c['random_walk']:
        print(f"  >>> RESULT: SYSTEMATIC RECOVERY - Drift direction is NOT random")
    else:
        print(f"  >>> RESULT: Cannot reject random drift direction")

    print("\n" + "=" * 70)
    print("TEST D: OMEGA EXPONENTIAL DECAY")
    print("=" * 70)
    d = aggregated["test_d"]
    total_d = sum(d.values())
    print(f"  Exponential Decay (R2>=0.6): {d['decay_confirmed']}/{total_d} ({100*d['decay_confirmed']/total_d:.1f}%)")
    print(f"  Weak Decay (R2>=0.4):        {d['weak_decay']}/{total_d} ({100*d['weak_decay']/total_d:.1f}%)")
    print(f"  No Decay:                   {d['no_decay']}/{total_d} ({100*d['no_decay']/total_d:.1f}%)")
    print(f"  Other/Error:                {d['other']}/{total_d}")

    decay_total = d['decay_confirmed'] + d['weak_decay']
    if decay_total > d['no_decay']:
        print(f"  >>> RESULT: EXPONENTIAL DECAY PATTERN FOUND - Recovery is lawful")
    else:
        print(f"  >>> RESULT: No clear exponential decay pattern")

    # Overall verdict
    print("\n" + "=" * 70)
    print("OVERALL VERDICT")
    print("=" * 70)

    passes = 0
    if a['recovery'] > a['random_walk']:
        passes += 1
        print("  [PASS] Test A: Recovery attractor detected")
    else:
        print("  [FAIL] Test A: Cannot reject random walk")

    if b['saturating'] > b['linear']:
        passes += 1
        print("  [PASS] Test B: Variance saturates (attractor)")
    else:
        print("  [FAIL] Test B: Linear variance growth")

    if c['recovery'] > c['random_walk']:
        passes += 1
        print("  [PASS] Test C: Systematic recovery direction")
    else:
        print("  [FAIL] Test C: Random drift direction")

    if decay_total > d['no_decay']:
        passes += 1
        print("  [PASS] Test D: Exponential decay in recovery")
    else:
        print("  [FAIL] Test D: No exponential decay")

    print(f"\n  TESTS PASSED: {passes}/4")

    if passes >= 3:
        print("\n  >>> CONCLUSION: Identity drift follows LAWFUL DYNAMICS, NOT random walk")
    elif passes >= 2:
        print("\n  >>> CONCLUSION: Mixed evidence - some attractor behavior detected")
    else:
        print("\n  >>> CONCLUSION: Cannot reject random walk hypothesis")

    # Save results
    output_dir = Path(__file__).parent / "results"
    output_dir.mkdir(exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = output_dir / f"statistical_tests_{timestamp}.json"

    output_data = {
        "timestamp": datetime.now().isoformat(),
        "total_sequences": total_sequences,
        "aggregated_results": aggregated,
        "tests_passed": passes,
        "detailed_results": all_results
    }

    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(output_data, f, indent=2)

    print(f"\n  Results saved to: {output_file}")

    return output_data

if __name__ == "__main__":
    main()
