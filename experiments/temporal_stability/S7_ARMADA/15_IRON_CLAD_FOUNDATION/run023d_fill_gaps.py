"""
S7 RUN 023d: FILL GAPS SCRIPT
==============================
Detects and fills missing experiments from rate limit interruptions.

USAGE:
    # Analyze gaps only (no execution)
    python run023d_fill_gaps.py --analyze

    # Fill gaps for specific ships
    python run023d_fill_gaps.py --ships claude-haiku-3.5 gpt-4o-mini

    # Fill all gaps
    python run023d_fill_gaps.py

Author: Claude (VALIS Network)
Date: December 20, 2025
"""

import os
import sys
import json
import argparse
from pathlib import Path
from collections import defaultdict

# Add parent paths for imports
sys.path.insert(0, str(Path(__file__).parent.parent))
sys.path.insert(0, str(Path(__file__).parent.parent / "1_CALIBRATION" / "lib"))

try:
    from fleet_loader import get_fleet_by_option, load_architecture_matrix
except ImportError as e:
    print(f"[ERROR] fleet_loader not available: {e}")
    sys.exit(1)

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
RESULTS_FILE = SCRIPT_DIR / "results" / "S7_run_023d_CURRENT.json"
TARGET_ITERATIONS = 30  # Expected iterations per ship

# =============================================================================
# GAP DETECTION
# =============================================================================

def load_current_results():
    """Load current results file."""
    if not RESULTS_FILE.exists():
        return {"results": []}

    with open(RESULTS_FILE, 'r', encoding='utf-8') as f:
        return json.load(f)

def analyze_gaps():
    """Analyze current results and identify gaps."""
    data = load_current_results()
    results = data.get("results", [])

    # Count results by model
    by_model = defaultdict(list)
    for r in results:
        model = r.get("model", "unknown")
        iteration = r.get("iteration", 0)
        by_model[model].append(iteration)

    # Get expected fleet
    try:
        ships = get_fleet_by_option("budget_patrol-lite")
        architecture_matrix = load_architecture_matrix()
    except Exception as e:
        print(f"[ERROR] Could not load fleet: {e}")
        return {}

    # Find gaps
    gaps = {}
    complete = []
    partial = []
    missing = []

    for ship_name in ships:
        if ship_name not in architecture_matrix:
            continue

        model = architecture_matrix[ship_name]["model"]
        completed_iters = set(by_model.get(model, []))
        expected_iters = set(range(TARGET_ITERATIONS))
        missing_iters = expected_iters - completed_iters

        if len(completed_iters) == TARGET_ITERATIONS:
            complete.append(ship_name)
        elif len(completed_iters) == 0:
            missing.append(ship_name)
            gaps[ship_name] = list(range(TARGET_ITERATIONS))
        else:
            partial.append((ship_name, len(completed_iters), sorted(missing_iters)))
            gaps[ship_name] = sorted(missing_iters)

    return {
        "complete": complete,
        "partial": partial,
        "missing": missing,
        "gaps": gaps,
        "total_results": len(results),
        "expected_total": len(ships) * TARGET_ITERATIONS,
    }

def print_gap_analysis(analysis):
    """Print gap analysis summary."""
    print("=" * 70)
    print("RUN 023d GAP ANALYSIS")
    print("=" * 70)
    print(f"Total results: {analysis['total_results']} / {analysis['expected_total']}")
    print(f"Complete ships: {len(analysis['complete'])}")
    print(f"Partial ships: {len(analysis['partial'])}")
    print(f"Missing ships: {len(analysis['missing'])}")
    print()

    if analysis['complete']:
        print("COMPLETE:")
        for ship in analysis['complete'][:10]:
            print(f"  - {ship}")
        if len(analysis['complete']) > 10:
            print(f"  ... and {len(analysis['complete']) - 10} more")
        print()

    if analysis['partial']:
        print("PARTIAL:")
        for ship, count, missing in analysis['partial']:
            print(f"  - {ship}: {count}/{TARGET_ITERATIONS} (missing: {len(missing)} iters)")
        print()

    if analysis['missing']:
        print("MISSING (not started):")
        for ship in analysis['missing']:
            print(f"  - {ship}")
        print()

    # Calculate total gaps
    total_gaps = sum(len(iters) for iters in analysis['gaps'].values())
    print(f"TOTAL GAPS: {total_gaps} experiments to fill")

# =============================================================================
# GAP FILLING
# =============================================================================

def fill_gaps(ship_filter=None, dry_run=False):
    """Fill gaps by running missing experiments."""

    analysis = analyze_gaps()
    gaps = analysis['gaps']

    if not gaps:
        print("[INFO] No gaps to fill!")
        return

    # Filter ships if specified
    if ship_filter:
        gaps = {k: v for k, v in gaps.items() if k in ship_filter}

    if not gaps:
        print(f"[INFO] No gaps found for specified ships: {ship_filter}")
        return

    print(f"\n[INFO] Will fill {sum(len(v) for v in gaps.values())} gaps across {len(gaps)} ships")

    if dry_run:
        print("[DRY RUN] Would fill these gaps:")
        for ship, iters in gaps.items():
            print(f"  {ship}: iterations {iters[:5]}{'...' if len(iters) > 5 else ''}")
        return

    # Import the experiment runner
    try:
        from run023d_extended_settling import (
            run_extended_settling,
            KEY_POOL,
            KeyPool,
            load_dotenv,
            ARMADA_DIR,
        )
        import run023d_extended_settling as runner
    except ImportError as e:
        print(f"[ERROR] Could not import runner: {e}")
        sys.exit(1)

    # Load environment
    env_path = ARMADA_DIR / ".env"
    if env_path.exists():
        load_dotenv(env_path)

    # Initialize key pool
    runner.KEY_POOL = KeyPool(start_offset=0, claude_key=12)

    architecture_matrix = load_architecture_matrix()

    # Load existing results
    data = load_current_results()
    results = data.get("results", [])

    # Track completed
    completed = set()
    for r in results:
        completed.add((r.get("model"), r.get("iteration")))

    # Fill gaps
    total_gaps = sum(len(v) for v in gaps.values())
    current = 0

    for ship_name, missing_iters in gaps.items():
        if ship_name not in architecture_matrix:
            print(f"[WARNING] {ship_name} not in architecture matrix")
            continue

        model_config = architecture_matrix[ship_name].copy()
        model_config["ship_name"] = ship_name
        model_name = model_config["model"]

        for iteration in missing_iters:
            current += 1

            if (model_name, iteration) in completed:
                print(f"[{current}/{total_gaps}] {ship_name} iter {iteration+1} - SKIPPED (already exists)")
                continue

            try:
                print(f"\n[{current}/{total_gaps}] {ship_name} iter {iteration+1}")
                result = run_extended_settling(ship_name, model_config, iteration)

                # Append result
                from dataclasses import asdict
                results.append(asdict(result))
                completed.add((model_name, iteration))

                # Incremental save
                data["results"] = results
                with open(RESULTS_FILE, 'w', encoding='utf-8') as f:
                    json.dump(data, f, indent=2, default=str)

            except Exception as e:
                print(f"    [ERROR] {ship_name} iter {iteration+1}: {e}")

    print(f"\n[DONE] Filled gaps. Total results: {len(results)}")

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Run 023d: Fill Gaps from Rate Limits",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    parser.add_argument("--analyze", action="store_true",
                       help="Analyze gaps only, don't fill")
    parser.add_argument("--ships", nargs="+",
                       help="Specific ships to fill gaps for")
    parser.add_argument("--dry-run", action="store_true",
                       help="Show what would be filled without executing")

    args = parser.parse_args()

    if args.analyze:
        analysis = analyze_gaps()
        print_gap_analysis(analysis)
    else:
        analysis = analyze_gaps()
        print_gap_analysis(analysis)
        print()
        fill_gaps(ship_filter=args.ships, dry_run=args.dry_run)

if __name__ == "__main__":
    main()
