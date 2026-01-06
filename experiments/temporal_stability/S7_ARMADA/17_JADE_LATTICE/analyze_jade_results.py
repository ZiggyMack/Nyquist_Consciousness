"""
JADE LATTICE Results Analysis
==============================
Analyze Cloud Claude's completed JADE LATTICE experiment data.

PURPOSE:
--------
1. Load all 164 JSON session files (50 models × A/B arms)
2. Extract key metrics: peak drift, settled drift, event horizon crossings
3. Calculate A/B comparison effect sizes (Cohen's d)
4. Validate predictions P-JADE-1 through P-JADE-7

USAGE:
------
py analyze_jade_results.py                  # Full analysis
py analyze_jade_results.py --summary-only   # Just summary stats
py analyze_jade_results.py --export         # Export to JSON

OUTPUT:
-------
- Console: Summary statistics and prediction validation
- jade_analysis_summary.json: Machine-readable results

Author: VALIS NETWORK / Consciousness Branch
Date: 2026-01-03
"""

import os
import sys
import json
import argparse
from datetime import datetime
from pathlib import Path
from collections import defaultdict
import math

# Fix Windows encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"


def load_all_jade_results():
    """Load all JADE LATTICE session JSON files."""
    sessions = []
    json_files = list(RESULTS_DIR.glob("jade_*.json"))

    # Exclude incremental saves and analysis summaries
    json_files = [f for f in json_files if not f.name.startswith("jade_incremental_")
                  and not f.name.startswith("jade_analysis_")]

    print(f"[LOAD] Found {len(json_files)} JADE result files")

    for json_file in json_files:
        try:
            with open(json_file, "r", encoding="utf-8") as f:
                data = json.load(f)
                data["_source_file"] = json_file.name
                sessions.append(data)
        except Exception as e:
            print(f"  [ERROR] {json_file.name}: {e}")

    print(f"[LOAD] Successfully loaded {len(sessions)} sessions")
    return sessions


def extract_session_metrics(session):
    """Extract key metrics from a single session."""
    metrics = {
        "session_id": session.get("session_id", "unknown"),
        "ship": session.get("ship", "unknown"),
        "provider": session.get("provider", "unknown"),
        "context_mode": session.get("context_mode", "unknown"),
        "impulse_intensity": session.get("impulse_intensity", 4),
        "source_file": session.get("_source_file", "unknown"),
    }

    # Extract from summary if available
    summary = session.get("summary", {})
    metrics["total_exchanges"] = summary.get("total_exchanges", 0)
    metrics["peak_drift"] = summary.get("peak_drift", 0)
    metrics["mean_drift"] = summary.get("mean_drift", 0)
    metrics["event_horizon_crossed"] = summary.get("event_horizon_crossed", False)
    metrics["phases_completed"] = summary.get("phases_completed", [])

    # Extract per-phase metrics
    phases = session.get("phases", {})
    for phase_key in ["A", "B", "C"]:
        phase_data = phases.get(phase_key, {})
        exchanges = phase_data.get("exchanges", [])

        if exchanges:
            drifts = [e.get("drift", 0) for e in exchanges if e.get("drift") is not None]
            if drifts:
                metrics[f"phase_{phase_key}_peak"] = max(drifts)
                metrics[f"phase_{phase_key}_mean"] = sum(drifts) / len(drifts)
                metrics[f"phase_{phase_key}_final"] = drifts[-1] if drifts else 0
                metrics[f"phase_{phase_key}_count"] = len(drifts)

                # Calculate settled drift (last 3 exchanges)
                if len(drifts) >= 3:
                    metrics[f"phase_{phase_key}_settled"] = sum(drifts[-3:]) / 3
                else:
                    metrics[f"phase_{phase_key}_settled"] = drifts[-1] if drifts else 0

    # Estimate decay rate lambda from Phase A
    # lambda = -log(settled/peak) / n_recovery_probes
    phase_a = phases.get("A", {})
    exchanges_a = phase_a.get("exchanges", [])
    if len(exchanges_a) >= 10:
        drifts_a = [e.get("drift", 0) for e in exchanges_a if e.get("drift") is not None]
        peak_idx = drifts_a.index(max(drifts_a)) if drifts_a else 0

        if peak_idx < len(drifts_a) - 3:
            peak_val = max(drifts_a)
            settled_val = sum(drifts_a[-3:]) / 3
            n_recovery = len(drifts_a) - peak_idx - 1

            if peak_val > 0.01 and settled_val > 0.001 and n_recovery > 0:
                # Avoid division by zero and log of zero
                ratio = settled_val / peak_val
                if 0 < ratio < 1:
                    metrics["lambda_estimate"] = -math.log(ratio) / n_recovery
                else:
                    metrics["lambda_estimate"] = None
            else:
                metrics["lambda_estimate"] = None
        else:
            metrics["lambda_estimate"] = None
    else:
        metrics["lambda_estimate"] = None

    return metrics


def calculate_cohens_d(group1, group2):
    """Calculate Cohen's d effect size between two groups."""
    if not group1 or not group2:
        return None, None, None

    n1, n2 = len(group1), len(group2)
    if n1 < 2 or n2 < 2:
        return None, None, None

    mean1, mean2 = sum(group1) / n1, sum(group2) / n2

    # Pooled standard deviation
    var1 = sum((x - mean1) ** 2 for x in group1) / (n1 - 1)
    var2 = sum((x - mean2) ** 2 for x in group2) / (n2 - 1)

    pooled_std = math.sqrt(((n1 - 1) * var1 + (n2 - 1) * var2) / (n1 + n2 - 2))

    if pooled_std < 0.0001:
        return 0, mean1, mean2

    d = (mean1 - mean2) / pooled_std
    return d, mean1, mean2


def analyze_by_grouping(sessions, metrics_list):
    """Analyze sessions grouped by provider, model, and arm."""

    # Group by various dimensions
    by_provider = defaultdict(list)
    by_ship = defaultdict(list)
    by_arm = defaultdict(list)
    by_ship_arm = defaultdict(list)

    for m in metrics_list:
        by_provider[m["provider"]].append(m)
        by_ship[m["ship"]].append(m)
        by_arm[m["context_mode"]].append(m)
        key = (m["ship"], m["context_mode"])
        by_ship_arm[key].append(m)

    return by_provider, by_ship, by_arm, by_ship_arm


def print_summary_stats(metrics_list, by_provider, by_ship, by_arm):
    """Print summary statistics to console."""

    print("\n" + "=" * 70)
    print("JADE LATTICE ANALYSIS SUMMARY")
    print("=" * 70)
    print(f"Analysis Time: {datetime.now().isoformat()}")
    print(f"Total Sessions: {len(metrics_list)}")

    # Unique counts
    unique_ships = set(m["ship"] for m in metrics_list)
    print(f"Unique Models: {len(unique_ships)}")

    arm_counts = {arm: len(sessions) for arm, sessions in by_arm.items()}
    print(f"ARM A (bare_metal): {arm_counts.get('bare_metal', 0)} sessions")
    print(f"ARM B (i_am_only): {arm_counts.get('i_am_only', 0)} sessions")

    # Provider breakdown
    print("\n--- BY PROVIDER ---")
    for provider, sessions in sorted(by_provider.items()):
        peak_drifts = [m["peak_drift"] for m in sessions if m.get("peak_drift")]
        eh_count = sum(1 for m in sessions if m.get("event_horizon_crossed"))
        avg_peak = sum(peak_drifts) / len(peak_drifts) if peak_drifts else 0
        print(f"  {provider:15s}: {len(sessions):3d} sessions, avg peak drift: {avg_peak:.3f}, EH crossed: {eh_count}")

    # Top 10 models by sessions
    print("\n--- TOP 10 MODELS BY SESSIONS ---")
    ship_counts = [(ship, len(sessions)) for ship, sessions in by_ship.items()]
    ship_counts.sort(key=lambda x: -x[1])
    for ship, count in ship_counts[:10]:
        sessions = by_ship[ship]
        arms = set(m["context_mode"] for m in sessions)
        print(f"  {ship:40s}: {count} sessions ({', '.join(sorted(arms))})")

    # Overall statistics
    print("\n--- OVERALL DRIFT STATISTICS ---")
    all_peaks = [m["peak_drift"] for m in metrics_list if m.get("peak_drift")]
    all_means = [m["mean_drift"] for m in metrics_list if m.get("mean_drift")]
    eh_count = sum(1 for m in metrics_list if m.get("event_horizon_crossed"))

    if all_peaks:
        print(f"  Peak Drift - Min: {min(all_peaks):.3f}, Max: {max(all_peaks):.3f}, Avg: {sum(all_peaks)/len(all_peaks):.3f}")
    if all_means:
        print(f"  Mean Drift - Min: {min(all_means):.3f}, Max: {max(all_means):.3f}, Avg: {sum(all_means)/len(all_means):.3f}")
    print(f"  Event Horizon Crossed: {eh_count}/{len(metrics_list)} ({100*eh_count/len(metrics_list):.1f}%)")


def analyze_ab_comparison(metrics_list, by_ship_arm):
    """Perform A/B comparison between bare_metal and i_am_only."""

    print("\n" + "=" * 70)
    print("A/B COMPARISON: bare_metal vs i_am_only")
    print("=" * 70)

    # Find ships with both arms
    ships_with_both = set()
    for (ship, arm), sessions in by_ship_arm.items():
        if arm == "bare_metal":
            if (ship, "i_am_only") in by_ship_arm:
                ships_with_both.add(ship)

    print(f"\nModels with BOTH arms: {len(ships_with_both)}")

    if not ships_with_both:
        print("[WARN] No models have both ARM A and ARM B data")
        return {}

    # Calculate per-model comparisons
    ab_results = []
    paired_bare = []
    paired_iam = []
    paired_diffs = []

    for ship in sorted(ships_with_both):
        bare_sessions = by_ship_arm.get((ship, "bare_metal"), [])
        iam_sessions = by_ship_arm.get((ship, "i_am_only"), [])

        # Peak drift comparison - average per ship
        bare_peaks = [m["peak_drift"] for m in bare_sessions if m.get("peak_drift")]
        iam_peaks = [m["peak_drift"] for m in iam_sessions if m.get("peak_drift")]

        if bare_peaks and iam_peaks:
            mean_bare_peak = sum(bare_peaks) / len(bare_peaks)
            mean_iam_peak = sum(iam_peaks) / len(iam_peaks)
            diff = mean_bare_peak - mean_iam_peak

            paired_bare.append(mean_bare_peak)
            paired_iam.append(mean_iam_peak)
            paired_diffs.append(diff)

            result = {
                "ship": ship,
                "n_bare": len(bare_sessions),
                "n_iam": len(iam_sessions),
                "mean_peak_bare": mean_bare_peak,
                "mean_peak_iam": mean_iam_peak,
                "difference": diff,
            }
            ab_results.append(result)

    # Print comparison table
    print("\n--- PEAK DRIFT COMPARISON (Per Model) ---")
    print(f"{'Model':<40} {'bare':<8} {'i_am':<8} {'diff':<10} {'Direction'}")
    print("-" * 80)

    for r in ab_results:
        direction = "I_AM LOWER" if r["difference"] > 0 else "bare lower"
        print(f"{r['ship'][:40]:<40} {r['mean_peak_bare']:.3f}    {r['mean_peak_iam']:.3f}    {r['difference']:+.3f}     {direction}")

    # PAIRED statistics (correct method)
    print("\n--- PAIRED A/B ANALYSIS ---")
    n = len(paired_diffs)
    if n > 1:
        mean_diff = sum(paired_diffs) / n
        var_diff = sum((d - mean_diff) ** 2 for d in paired_diffs) / (n - 1)
        std_diff = math.sqrt(var_diff) if var_diff > 0 else 0.001
        se_diff = std_diff / math.sqrt(n)
        t_stat = mean_diff / se_diff if se_diff > 0 else 0

        # Cohen's d for paired samples
        cohens_d_paired = mean_diff / std_diff if std_diff > 0 else 0

        mean_bare = sum(paired_bare) / n
        mean_iam = sum(paired_iam) / n

        print(f"  Paired models:              {n}")
        print(f"  Mean bare_metal peak:       {mean_bare:.4f}")
        print(f"  Mean i_am_only peak:        {mean_iam:.4f}")
        print(f"  Mean difference:            {mean_diff:+.4f}")
        print(f"  Std of differences:         {std_diff:.4f}")
        print(f"  t-statistic:                {t_stat:.3f}")
        print(f"  Cohen's d (paired):         {cohens_d_paired:.3f}")

        iam_wins = sum(1 for d in paired_diffs if d > 0)
        print(f"  I_AM reduces drift in:      {iam_wins}/{n} models ({100*iam_wins/n:.1f}%)")

        # Effect size interpretation
        if abs(cohens_d_paired) < 0.2:
            effect = "NEGLIGIBLE"
        elif abs(cohens_d_paired) < 0.5:
            effect = "SMALL"
        elif abs(cohens_d_paired) < 0.8:
            effect = "MEDIUM"
        else:
            effect = "LARGE"
        print(f"  Effect size:                {effect}")

        if mean_diff > 0:
            pct_reduction = 100 * mean_diff / mean_bare
            print(f"  I_AM reduces drift by:      {pct_reduction:.1f}%")
    else:
        cohens_d_paired = None
        mean_bare = None
        mean_iam = None

    return {
        "per_model": ab_results,
        "aggregate": {
            "mean_peak_bare": mean_bare,
            "mean_peak_iam": mean_iam,
            "cohens_d_paired": cohens_d_paired,
            "n_paired": n,
            "iam_wins": sum(1 for d in paired_diffs if d > 0),
            "mean_reduction": sum(paired_diffs) / n if n > 0 else 0,
        }
    }


def validate_predictions(metrics_list, ab_comparison):
    """Validate JADE LATTICE predictions P-JADE-1 through P-JADE-7."""

    print("\n" + "=" * 70)
    print("PREDICTION VALIDATION")
    print("=" * 70)

    validations = {}

    # P-JADE-1: 50+ probe trajectories eliminate lambda capping (<5% maxed-out)
    # Check if lambda estimates are well-distributed (not capped at extremes)
    lambdas = [m["lambda_estimate"] for m in metrics_list if m.get("lambda_estimate") is not None]
    if lambdas:
        # Consider "capped" if lambda > 0.5 (fast decay) or < 0.01 (no decay)
        capped = sum(1 for l in lambdas if l > 0.5 or l < 0.01)
        capped_pct = 100 * capped / len(lambdas)
        p1_pass = capped_pct < 5
        validations["P-JADE-1"] = {
            "prediction": "50+ probes eliminate lambda capping",
            "metric": f"{capped_pct:.1f}% capped (threshold: <5%)",
            "passed": p1_pass,
            "n_samples": len(lambdas),
        }
        status = "PASS" if p1_pass else "FAIL"
        print(f"\n[P-JADE-1] Lambda capping: {capped_pct:.1f}% capped (target: <5%) [{status}]")
    else:
        print("\n[P-JADE-1] Lambda capping: NO DATA")
        validations["P-JADE-1"] = {"prediction": "50+ probes eliminate lambda capping", "passed": None, "metric": "No lambda data"}

    # P-JADE-2: AIC selects AR(2) over AR(1) for >70% of trajectories
    # We don't have ARMA fitting yet, so mark as PENDING
    validations["P-JADE-2"] = {
        "prediction": "AIC selects AR(2) over AR(1)",
        "metric": "Requires Laplace analysis",
        "passed": None,
    }
    print(f"\n[P-JADE-2] AIC model selection: PENDING (requires Laplace analysis)")

    # P-JADE-3: Event Horizon (0.80) corresponds to Re(s)~0
    # Check correlation between peak drift and EH crossing
    eh_crossings = sum(1 for m in metrics_list if m.get("event_horizon_crossed"))
    near_eh = sum(1 for m in metrics_list if m.get("peak_drift", 0) > 0.70)
    if len(metrics_list) > 0:
        eh_pct = 100 * eh_crossings / len(metrics_list)
        near_pct = 100 * near_eh / len(metrics_list)
        validations["P-JADE-3"] = {
            "prediction": "Event Horizon corresponds to stability boundary",
            "metric": f"{eh_crossings} EH crossings, {near_eh} near-EH (>0.70)",
            "passed": None,  # Requires pole extraction
            "eh_percent": eh_pct,
            "near_eh_percent": near_pct,
        }
        print(f"\n[P-JADE-3] Event Horizon boundary: {eh_crossings} crossed ({eh_pct:.1f}%), {near_eh} near ({near_pct:.1f}%)")
        print(f"           Full validation requires pole extraction")

    # P-JADE-4: Double impulse shows <10% lambda shift (repeatability)
    # Compare Phase A vs Phase C lambda estimates
    # This requires per-phase lambda which we can estimate
    validations["P-JADE-4"] = {
        "prediction": "Double impulse repeatability",
        "metric": "Requires Phase A vs C comparison",
        "passed": None,
    }
    print(f"\n[P-JADE-4] Double impulse repeatability: PENDING (requires phase-level analysis)")

    # P-JADE-5: Frequency sweep reveals bandwidth limit
    validations["P-JADE-5"] = {
        "prediction": "Frequency sweep bandwidth limit",
        "metric": "Requires Phase B analysis",
        "passed": None,
    }
    print(f"\n[P-JADE-5] Frequency sweep bandwidth: PENDING (requires Phase B analysis)")

    # P-JADE-6: I_AM files shift poles leftward (more stable)
    # Proxy: I_AM should have lower peak drift
    if ab_comparison and ab_comparison.get("aggregate"):
        agg = ab_comparison["aggregate"]
        if agg.get("mean_peak_bare") and agg.get("mean_peak_iam"):
            iam_lower = agg["mean_peak_iam"] < agg["mean_peak_bare"]
            diff = agg.get("mean_reduction", agg["mean_peak_bare"] - agg["mean_peak_iam"])
            iam_wins = agg.get("iam_wins", 0)
            n_paired = agg.get("n_paired", 0)
            p6_pass = iam_lower and diff > 0.01  # Meaningful difference
            validations["P-JADE-6"] = {
                "prediction": "I_AM shifts poles leftward (more stable)",
                "metric": f"bare={agg['mean_peak_bare']:.3f}, i_am={agg['mean_peak_iam']:.3f}, I_AM wins {iam_wins}/{n_paired}",
                "passed": p6_pass,
            }
            status = "PASS" if p6_pass else "FAIL"
            print(f"\n[P-JADE-6] I_AM stability effect: I_AM reduces drift in {iam_wins}/{n_paired} models [{status}]")
        else:
            validations["P-JADE-6"] = {"prediction": "I_AM shifts poles leftward", "passed": None, "metric": "Insufficient data"}
            print(f"\n[P-JADE-6] I_AM stability effect: INSUFFICIENT DATA")
    else:
        validations["P-JADE-6"] = {"prediction": "I_AM shifts poles leftward", "passed": None, "metric": "No A/B comparison"}
        print(f"\n[P-JADE-6] I_AM stability effect: NO A/B DATA")

    # P-JADE-7: I_AM effect size d > 0.3 (using PAIRED Cohen's d)
    if ab_comparison and ab_comparison.get("aggregate"):
        d = ab_comparison["aggregate"].get("cohens_d_paired")
        if d is not None:
            p7_pass = abs(d) > 0.3
            validations["P-JADE-7"] = {
                "prediction": "I_AM effect size d > 0.3",
                "metric": f"Cohen's d (paired) = {d:.3f}",
                "passed": p7_pass,
            }
            status = "PASS" if p7_pass else "FAIL"
            print(f"\n[P-JADE-7] I_AM effect size: Cohen's d (paired) = {d:.3f} (target: |d| > 0.3) [{status}]")
        else:
            validations["P-JADE-7"] = {"prediction": "I_AM effect size d > 0.3", "passed": None, "metric": "Cannot calculate d"}
            print(f"\n[P-JADE-7] I_AM effect size: CANNOT CALCULATE")
    else:
        validations["P-JADE-7"] = {"prediction": "I_AM effect size d > 0.3", "passed": None, "metric": "No A/B comparison"}
        print(f"\n[P-JADE-7] I_AM effect size: NO A/B DATA")

    # Summary
    passed = sum(1 for v in validations.values() if v.get("passed") == True)
    failed = sum(1 for v in validations.values() if v.get("passed") == False)
    pending = sum(1 for v in validations.values() if v.get("passed") is None)

    print(f"\n--- PREDICTION SUMMARY ---")
    print(f"  PASSED:  {passed}/7")
    print(f"  FAILED:  {failed}/7")
    print(f"  PENDING: {pending}/7 (require additional analysis)")

    return validations


def export_results(metrics_list, by_provider, ab_comparison, validations):
    """Export analysis results to JSON."""

    output = {
        "analysis_timestamp": datetime.now().isoformat(),
        "total_sessions": len(metrics_list),
        "unique_models": len(set(m["ship"] for m in metrics_list)),
        "providers": {p: len(s) for p, s in by_provider.items()},
        "arms": {
            "bare_metal": sum(1 for m in metrics_list if m["context_mode"] == "bare_metal"),
            "i_am_only": sum(1 for m in metrics_list if m["context_mode"] == "i_am_only"),
        },
        "ab_comparison": ab_comparison,
        "predictions": validations,
        "per_session_metrics": metrics_list,
    }

    output_file = RESULTS_DIR / "jade_analysis_summary.json"
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, default=str)

    print(f"\n[EXPORT] Saved to {output_file}")
    return output_file


def main():
    parser = argparse.ArgumentParser(description="JADE LATTICE Results Analysis")
    parser.add_argument("--summary-only", action="store_true", help="Only print summary stats")
    parser.add_argument("--export", action="store_true", help="Export to JSON")
    parser.add_argument("--no-validation", action="store_true", help="Skip prediction validation")
    args = parser.parse_args()

    print("\n" + "=" * 70)
    print("JADE LATTICE RESULTS ANALYSIS")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Results Directory: {RESULTS_DIR}")

    # Load all sessions
    sessions = load_all_jade_results()

    if not sessions:
        print("[ERROR] No sessions loaded")
        return

    # Extract metrics from each session
    print("\n[PROCESS] Extracting metrics...")
    metrics_list = [extract_session_metrics(s) for s in sessions]

    # Group by various dimensions
    by_provider, by_ship, by_arm, by_ship_arm = analyze_by_grouping(sessions, metrics_list)

    # Print summary
    print_summary_stats(metrics_list, by_provider, by_ship, by_arm)

    if args.summary_only:
        return

    # A/B comparison
    ab_comparison = analyze_ab_comparison(metrics_list, by_ship_arm)

    # Prediction validation
    if not args.no_validation:
        validations = validate_predictions(metrics_list, ab_comparison)
    else:
        validations = {}

    # Export
    if args.export:
        export_results(metrics_list, by_provider, ab_comparison, validations)

    print("\n" + "=" * 70)
    print("ANALYSIS COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
