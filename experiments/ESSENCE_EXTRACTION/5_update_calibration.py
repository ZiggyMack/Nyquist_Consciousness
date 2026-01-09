#!/usr/bin/env python3
"""
ESSENCE EXTRACTION - Phase 5: Update Calibration
==================================================
Generate calibration updates from aggregated essences.

This is the final phase that transforms extracted essences
into actionable calibration updates for the ARCHITECTURE_MATRIX.

WHAT IT DOES:
-------------
1. Reads model essences from results/model_essences/
2. Analyzes recovery patterns, drift signatures, stability profiles
3. Generates proposed updates for ARCHITECTURE_MATRIX.json
4. Creates human-readable calibration reports

OUTPUT:
-------
Results go to: results/calibration_updates/
  - calibration_proposals.json: Structured updates
  - calibration_report.md: Human-readable summary
  - provider_profiles.json: Per-provider behavioral patterns

USAGE:
------
py 5_update_calibration.py                  # Generate updates
py 5_update_calibration.py --apply          # Apply to ARCHITECTURE_MATRIX
py 5_update_calibration.py --dry-run        # Preview without applying
py 5_update_calibration.py --report-only    # Just generate reports
"""

import argparse
import json
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
ESSENCES_DIR = RESULTS_DIR / "model_essences"
CALIBRATION_DIR = RESULTS_DIR / "calibration_updates"
REPO_ROOT = SCRIPT_DIR.parent.parent
ARCHITECTURE_MATRIX = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "0_results" / "manifests" / "ARCHITECTURE_MATRIX.json"


def load_essences() -> dict:
    """Load all model essences from results."""
    essences = {}

    by_provider = ESSENCES_DIR / "by_provider"
    if not by_provider.exists():
        return essences

    for provider_dir in by_provider.iterdir():
        if not provider_dir.is_dir():
            continue

        provider = provider_dir.name
        essences[provider] = {}

        for essence_file in provider_dir.glob("*.json"):
            try:
                data = json.loads(essence_file.read_text(encoding="utf-8"))
                model_name = essence_file.stem
                essences[provider][model_name] = data
            except Exception:
                pass

    return essences


def analyze_essences(essences: dict) -> dict:
    """Analyze essences for calibration insights."""
    analysis = {
        "providers": {},
        "models": {},
        "patterns": {
            "high_stability": [],
            "high_drift": [],
            "strong_recovery": [],
            "weak_recovery": [],
        },
        "recommendations": [],
    }

    for provider, models in essences.items():
        provider_stats = {
            "model_count": len(models),
            "avg_drift": 0.0,
            "avg_stability": 0.0,
        }

        for model_name, essence in models.items():
            # Extract key metrics if present
            metrics = essence.get("metrics", {})
            drift = metrics.get("avg_drift", 0.5)
            stability = metrics.get("stability_score", 0.5)

            # Categorize
            if stability > 0.8:
                analysis["patterns"]["high_stability"].append(model_name)
            if drift > 0.7:
                analysis["patterns"]["high_drift"].append(model_name)

            # Store model-level data
            analysis["models"][model_name] = {
                "provider": provider,
                "drift": drift,
                "stability": stability,
            }

        analysis["providers"][provider] = provider_stats

    return analysis


def generate_calibration_proposals(analysis: dict) -> list:
    """Generate calibration proposals based on analysis."""
    proposals = []

    # High stability models might have their EH thresholds adjusted
    for model in analysis["patterns"]["high_stability"]:
        proposals.append({
            "model": model,
            "field": "stability_tier",
            "current": "unknown",
            "proposed": "high",
            "reason": "Consistently low drift in extraction data",
        })

    # High drift models might need warnings
    for model in analysis["patterns"]["high_drift"]:
        proposals.append({
            "model": model,
            "field": "stability_tier",
            "current": "unknown",
            "proposed": "volatile",
            "reason": "High drift observed in extraction data",
        })

    return proposals


def write_calibration_report(analysis: dict, proposals: list, output_dir: Path):
    """Write human-readable calibration report."""
    output_dir.mkdir(parents=True, exist_ok=True)

    report_lines = [
        "# Calibration Update Report",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "",
        "## Summary",
        f"- Providers analyzed: {len(analysis['providers'])}",
        f"- Models analyzed: {len(analysis['models'])}",
        f"- Update proposals: {len(proposals)}",
        "",
        "## Patterns Detected",
        f"- High stability models: {len(analysis['patterns']['high_stability'])}",
        f"- High drift models: {len(analysis['patterns']['high_drift'])}",
        "",
        "## Proposed Updates",
    ]

    for p in proposals[:20]:  # Limit to first 20
        report_lines.append(f"- {p['model']}: {p['field']} -> {p['proposed']} ({p['reason']})")

    report = "\n".join(report_lines)

    # Write report
    (output_dir / "calibration_report.md").write_text(report, encoding="utf-8")

    # Write structured proposals
    (output_dir / "calibration_proposals.json").write_text(
        json.dumps(proposals, indent=2), encoding="utf-8"
    )

    return len(proposals)


def main():
    parser = argparse.ArgumentParser(
        description="ESSENCE EXTRACTION - Phase 5: Update Calibration",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
This phase transforms extracted essences into ARCHITECTURE_MATRIX updates.

Examples:
  py 5_update_calibration.py               # Generate proposals
  py 5_update_calibration.py --apply       # Apply to ARCHITECTURE_MATRIX
  py 5_update_calibration.py --report-only # Just generate reports
        """
    )
    parser.add_argument("--apply", action="store_true",
                        help="Apply updates to ARCHITECTURE_MATRIX.json")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview without writing")
    parser.add_argument("--report-only", action="store_true",
                        help="Only generate reports, no proposals")

    args = parser.parse_args()

    print("="*60)
    print("ESSENCE EXTRACTION - PHASE 5: CALIBRATION UPDATE")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("="*60)

    # Load essences
    print("\n## Loading model essences...")
    essences = load_essences()
    total_models = sum(len(m) for m in essences.values())
    print(f"  Loaded: {total_models} model essences from {len(essences)} providers")

    if total_models == 0:
        print("\n  [WARNING] No essences found. Run extraction first.")
        return 1

    # Analyze
    print("\n## Analyzing essences...")
    analysis = analyze_essences(essences)
    print(f"  High stability: {len(analysis['patterns']['high_stability'])} models")
    print(f"  High drift: {len(analysis['patterns']['high_drift'])} models")

    # Generate proposals
    if not args.report_only:
        print("\n## Generating calibration proposals...")
        proposals = generate_calibration_proposals(analysis)
        print(f"  Proposals: {len(proposals)}")
    else:
        proposals = []

    # Write output
    if not args.dry_run:
        print("\n## Writing calibration report...")
        count = write_calibration_report(analysis, proposals, CALIBRATION_DIR)
        print(f"  Written to: {CALIBRATION_DIR}")
        print(f"  Proposals: {count}")

    # Apply to ARCHITECTURE_MATRIX if requested
    if args.apply and not args.dry_run:
        print("\n## Applying to ARCHITECTURE_MATRIX...")
        if ARCHITECTURE_MATRIX.exists():
            print(f"  Target: {ARCHITECTURE_MATRIX}")
            print("  [SKIP] Auto-apply not yet implemented")
            print("         Review calibration_proposals.json and apply manually")
        else:
            print(f"  [ERROR] ARCHITECTURE_MATRIX not found: {ARCHITECTURE_MATRIX}")

    print("\n" + "="*60)
    print("CALIBRATION UPDATE COMPLETE")
    print("="*60)

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
