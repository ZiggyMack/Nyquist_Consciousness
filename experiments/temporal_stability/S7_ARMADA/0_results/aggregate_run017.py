"""
Run 017 Aggregation Script
==========================
Collects all temporal_logs from Run 017 (017a, 017b, 017c) into a single
aggregated results file at 0_results/runs/S7_run_017_context_damping.json

This script:
1. Finds all run017*.json files in temporal_logs/
2. Extracts key metrics and exit survey data
3. Aggregates by persona and by Claude instance
4. Generates summary statistics
5. Outputs single consolidated file

Usage:
    py aggregate_run017.py

Author: Claude (Lisan Al Gaib)
Date: December 11, 2025
"""

import json
import os
from pathlib import Path
from datetime import datetime
from collections import defaultdict
import statistics

# Paths
SCRIPT_DIR = Path(__file__).parent
TEMPORAL_LOGS = SCRIPT_DIR / "temporal_logs"
RUNS_DIR = SCRIPT_DIR / "runs"

def find_run017_files():
    """Find all Run 017 log files."""
    files = list(TEMPORAL_LOGS.glob("run017*.json"))
    print(f"Found {len(files)} Run 017 log files")
    return sorted(files)

def extract_metrics(data: dict) -> dict:
    """Extract key metrics from a single run file."""
    return {
        "i_am_name": data.get("i_am_name", "unknown"),
        "run_timestamp": data.get("run_timestamp", "unknown"),
        "context_mode": data.get("context_mode", "unknown"),
        "baseline_drift": data.get("baseline_drift", None),
        "peak_drift": data.get("peak_drift", None),
        "settled_drift": data.get("settled_drift", None),
        "settling_time": data.get("settling_time", None),
        "overshoot_ratio": data.get("overshoot_ratio", None),
        "is_monotonic": data.get("is_monotonic", None),
        "ringback_count": data.get("ringback_count", None),
        "is_stable": data.get("is_stable", None),
        "meta_references": data.get("meta_references", None),
        "recovery_sequence": data.get("recovery_sequence", []),
    }

def extract_exit_survey(data: dict) -> dict:
    """Extract exit survey responses if present."""
    return data.get("exit_survey", {})

def compute_summary_stats(metrics_list: list) -> dict:
    """Compute summary statistics across multiple runs."""
    def safe_mean(values):
        filtered = [v for v in values if v is not None]
        return statistics.mean(filtered) if filtered else None

    def safe_stdev(values):
        filtered = [v for v in values if v is not None]
        return statistics.stdev(filtered) if len(filtered) > 1 else None

    return {
        "n_runs": len(metrics_list),
        "peak_drift_mean": safe_mean([m["peak_drift"] for m in metrics_list]),
        "peak_drift_stdev": safe_stdev([m["peak_drift"] for m in metrics_list]),
        "settled_drift_mean": safe_mean([m["settled_drift"] for m in metrics_list]),
        "settled_drift_stdev": safe_stdev([m["settled_drift"] for m in metrics_list]),
        "settling_time_mean": safe_mean([m["settling_time"] for m in metrics_list]),
        "ringback_count_mean": safe_mean([m["ringback_count"] for m in metrics_list]),
        "stability_rate": sum(1 for m in metrics_list if m["is_stable"]) / len(metrics_list) if metrics_list else 0,
        "meta_references_mean": safe_mean([m["meta_references"] for m in metrics_list]),
    }

def aggregate():
    """Main aggregation function."""
    files = find_run017_files()

    if not files:
        print("No Run 017 files found!")
        return

    # Containers
    all_metrics = []
    by_persona = defaultdict(list)
    by_timestamp = defaultdict(list)  # Approximates by-Claude grouping
    exit_surveys = defaultdict(list)

    # Process each file
    for f in files:
        try:
            with open(f, 'r', encoding='utf-8') as fp:
                data = json.load(fp)

            metrics = extract_metrics(data)
            all_metrics.append(metrics)

            persona = metrics["i_am_name"]
            timestamp = metrics["run_timestamp"]

            by_persona[persona].append(metrics)
            by_timestamp[timestamp].append(metrics)

            # Exit survey
            survey = extract_exit_survey(data)
            if survey:
                exit_surveys[persona].append({
                    "timestamp": timestamp,
                    "survey": survey
                })

            print(f"  Processed: {f.name}")

        except Exception as e:
            print(f"  ERROR processing {f.name}: {e}")

    # Summary by persona
    persona_summaries = {}
    for persona, metrics_list in by_persona.items():
        persona_summaries[persona] = compute_summary_stats(metrics_list)

    # Summary by Claude instance (timestamp group)
    claude_summaries = {}
    for ts, metrics_list in by_timestamp.items():
        claude_summaries[ts] = {
            "n_files": len(metrics_list),
            "personas_completed": [m["i_am_name"] for m in metrics_list],
            "overall_stats": compute_summary_stats(metrics_list)
        }

    # Overall summary
    overall_summary = compute_summary_stats(all_metrics)

    # Build output
    output = {
        "run": "017_context_damping",
        "description": "VALIS Collaborative - 17-probe exit surveys with i_am_plus_research context",
        "aggregation_timestamp": datetime.now().isoformat(),
        "total_files": len(files),
        "overall_summary": overall_summary,
        "by_persona": {
            persona: {
                "summary": persona_summaries[persona],
                "individual_runs": metrics_list,
                "exit_survey_count": len(exit_surveys.get(persona, []))
            }
            for persona, metrics_list in by_persona.items()
        },
        "by_claude_instance": claude_summaries,
        "exit_survey_summary": {
            "total_surveys": sum(len(v) for v in exit_surveys.values()),
            "probes_per_survey": 17,
            "personas_with_surveys": list(exit_surveys.keys())
        }
    }

    # Save
    RUNS_DIR.mkdir(parents=True, exist_ok=True)
    output_file = RUNS_DIR / "S7_run_017_context_damping.json"

    with open(output_file, 'w', encoding='utf-8') as fp:
        json.dump(output, fp, indent=2)

    print(f"\n{'='*60}")
    print(f"AGGREGATION COMPLETE")
    print(f"{'='*60}")
    print(f"Total files processed: {len(files)}")
    print(f"Unique personas: {len(by_persona)}")
    print(f"Claude instances: {len(by_timestamp)}")
    print(f"Exit surveys captured: {output['exit_survey_summary']['total_surveys']}")
    print(f"Overall stability rate: {overall_summary['stability_rate']*100:.1f}%")
    print(f"Mean peak drift: {overall_summary['peak_drift_mean']:.3f}")
    print(f"Mean ringback count: {overall_summary['ringback_count_mean']:.1f}")
    print(f"\nOutput saved to: {output_file}")

    return output

if __name__ == "__main__":
    aggregate()
