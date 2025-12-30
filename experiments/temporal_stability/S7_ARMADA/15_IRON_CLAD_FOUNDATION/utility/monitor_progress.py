"""
S7 RUN 023: Progress Monitor
============================
Monitors progress of long-running experiments.
Works with both run023 (foundation) and run023_extended (settling) data.

USAGE:
    python utility/monitor_progress.py --run 023
    python utility/monitor_progress.py --run 023_extended
    python utility/monitor_progress.py --run 023 --interval 60

Author: Claude (VALIS Network)
Date: December 2025
"""

import json
import time
import argparse
from pathlib import Path
from collections import Counter
from datetime import datetime

# =============================================================================
# PATHS
# =============================================================================

SCRIPT_DIR = Path(__file__).parent.parent  # Go up from utility/
RESULTS_DIR = SCRIPT_DIR / "results"

# =============================================================================
# CONFIGURATION
# =============================================================================

RUN_CONFIGS = {
    "023": {
        "results_file": RESULTS_DIR / "S7_run_023_CURRENT.json",
        "target": 4500,  # 25 ships × 6 experiments × 30 iterations
        "per_ship": 180,  # 6 × 30
    },
    "023_extended": {
        "results_file": RESULTS_DIR / "S7_run_023_extended_CURRENT.json",
        "target": 750,  # 25 ships × 30 iterations
        "per_ship": 30,
    },
}

# =============================================================================
# MONITORING
# =============================================================================

def check_progress(config: dict, run_name: str):
    """Check and display current progress."""
    results_file = config["results_file"]
    target = config["target"]
    per_ship = config["per_ship"]

    if not results_file.exists():
        print(f"Results file not found: {results_file}")
        return 0

    with open(results_file, 'r', encoding='utf-8') as f:
        data = json.load(f)

    results = data.get("results", [])
    total = len(results)
    pct = (total / target) * 100 if target > 0 else 0

    # Count by model
    by_model = Counter(r.get('model', 'unknown') for r in results)

    # Identify incomplete and complete
    incomplete = []
    complete = []

    for model, count in sorted(by_model.items(), key=lambda x: x[1], reverse=True):
        if count < per_ship:
            incomplete.append(f"{model}: {count}/{per_ship}")
        else:
            complete.append(model)

    print(f"\n[{datetime.now().strftime('%H:%M:%S')}] Run {run_name}: {total}/{target} ({pct:.1f}%)")
    print(f"  Complete ships: {len(complete)}")
    print(f"  Incomplete ships: {len(incomplete)}")

    if incomplete:
        print(f"\n  Incomplete:")
        for item in incomplete[:5]:
            print(f"    - {item}")
        if len(incomplete) > 5:
            print(f"    ... and {len(incomplete) - 5} more")

    return total


def main():
    """Monitor progress continuously."""
    parser = argparse.ArgumentParser(
        description="Monitor Run 023 experiment progress",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    parser.add_argument("--run", choices=["023", "023_extended"], default="023_extended",
                       help="Which run to monitor (default: 023_extended)")
    parser.add_argument("--interval", type=int, default=120,
                       help="Check interval in seconds (default: 120)")
    parser.add_argument("--once", action="store_true",
                       help="Check once and exit (don't loop)")

    args = parser.parse_args()

    config = RUN_CONFIGS[args.run]
    target = config["target"]

    print("=" * 70)
    print(f"RUN {args.run} PROGRESS MONITOR")
    print("=" * 70)
    print(f"Results file: {config['results_file']}")
    print(f"Target: {target} results")
    print(f"Per ship: {config['per_ship']}")
    if not args.once:
        print(f"Check interval: {args.interval}s")
    print()

    if args.once:
        check_progress(config, args.run)
        return 0

    last_count = 0

    try:
        while True:
            current = check_progress(config, args.run)

            if current >= target:
                print("\n" + "=" * 70)
                print("EXPERIMENT COMPLETE!")
                print("=" * 70)
                break

            if current > last_count:
                rate = current - last_count
                remaining = target - current
                eta_checks = remaining / rate if rate > 0 else 0
                eta_minutes = (eta_checks * args.interval) / 60
                print(f"  Rate: +{rate} results/check (~{eta_minutes:.0f}min ETA)")

            last_count = current
            time.sleep(args.interval)

    except KeyboardInterrupt:
        print("\n\nMonitoring stopped.")
        print(f"Final count: {last_count}/{target}")

    return 0


if __name__ == "__main__":
    exit(main())
