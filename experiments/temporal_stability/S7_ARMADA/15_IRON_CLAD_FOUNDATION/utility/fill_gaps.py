"""
S7 RUN 023: UNIFIED GAP FILLER
==============================
Detects and fills missing experiments from rate limit interruptions.
Works with both foundation (run023) and extended settling (run023_extended) data.

USAGE:
    # Analyze gaps only
    python utility/fill_gaps.py --run 023 --analyze
    python utility/fill_gaps.py --run 023_extended --analyze

    # Fill gaps for specific ships
    python utility/fill_gaps.py --run 023 --ships grok-4-fast claude-3-5-haiku

    # Fill all gaps
    python utility/fill_gaps.py --run 023
    python utility/fill_gaps.py --run 023_extended

    # Complete partial ships (mode: ship)
    python utility/fill_gaps.py --run 023 --mode ship

    # Fill individual missing experiments (mode: exp)
    python utility/fill_gaps.py --run 023 --mode exp

MODES:
    --mode ship: Complete ships that have <N iterations (batch by ship)
    --mode exp:  Fill individual missing experiments (fine-grained)

Author: Claude (VALIS Network)
Date: December 2025
"""

import os
import sys
import json
import time
import argparse
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from dataclasses import asdict

# =============================================================================
# PATHS
# =============================================================================

SCRIPT_DIR = Path(__file__).parent.parent  # Go up from utility/
UTILITY_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"

# Add parent paths for imports
sys.path.insert(0, str(SCRIPT_DIR.parent))
sys.path.insert(0, str(SCRIPT_DIR.parent / "1_CALIBRATION" / "lib"))

# =============================================================================
# CONFIGURATION
# =============================================================================

# Run configurations
RUN_CONFIGS = {
    "023": {
        "results_file": RESULTS_DIR / "S7_run_023_CURRENT.json",
        "runner_module": "run023",
        "target_iterations": 30,
        "experiments_per_iter": 6,  # 6 experiment types
        "target_results": 180,  # 30 × 6
        "fleet": "budget_patrol-lite",
    },
    "023_extended": {
        "results_file": RESULTS_DIR / "S7_run_023_extended_CURRENT.json",
        "runner_module": "run023_extended",
        "target_iterations": 30,
        "experiments_per_iter": 1,  # Single extended settling
        "target_results": 30,
        "fleet": "budget_patrol-lite",
    },
}

# =============================================================================
# GAP DETECTION
# =============================================================================

def load_current_results(config: dict) -> dict:
    """Load current results file."""
    results_file = config["results_file"]
    if not results_file.exists():
        return {"results": []}

    with open(results_file, 'r', encoding='utf-8') as f:
        return json.load(f)


def analyze_gaps_foundation(config: dict) -> dict:
    """Analyze gaps in foundation (run023) data."""
    data = load_current_results(config)
    results = data.get("results", [])

    # Count by model and experiment
    model_exp_counts = defaultdict(lambda: defaultdict(int))
    model_counts = defaultdict(int)

    for r in results:
        model = r.get('model', 'unknown')
        exp = r.get('experiment', 'unknown')
        model_exp_counts[model][exp] += 1
        model_counts[model] += 1

    # Get expected fleet
    try:
        from fleet_loader import get_fleet_by_option, load_architecture_matrix
        ships = get_fleet_by_option(config["fleet"])
        architecture_matrix = load_architecture_matrix()
    except ImportError:
        print("[WARNING] fleet_loader not available, using results-only analysis")
        ships = list(model_counts.keys())
        architecture_matrix = {}

    # Find ships with gaps
    target = config["target_results"]
    complete = []
    partial = []
    gaps = {}

    for model in model_counts:
        count = model_counts[model]
        if count >= target:
            complete.append(model)
        else:
            missing = target - count
            partial.append((model, count, missing))
            gaps[model] = {
                "current": count,
                "missing": missing,
                "iterations_needed": missing // config["experiments_per_iter"],
            }

    return {
        "complete": complete,
        "partial": partial,
        "gaps": gaps,
        "total_results": len(results),
        "expected_total": len(ships) * target if ships else "unknown",
    }


def analyze_gaps_extended(config: dict) -> dict:
    """Analyze gaps in extended settling (run023_extended) data."""
    data = load_current_results(config)
    results = data.get("results", [])

    # Count by model and iteration
    by_model = defaultdict(list)
    for r in results:
        model = r.get("model", "unknown")
        iteration = r.get("iteration", 0)
        by_model[model].append(iteration)

    # Get expected fleet
    try:
        from fleet_loader import get_fleet_by_option, load_architecture_matrix
        ships = get_fleet_by_option(config["fleet"])
        architecture_matrix = load_architecture_matrix()
    except ImportError:
        print("[WARNING] fleet_loader not available")
        ships = []
        architecture_matrix = {}

    # Find gaps
    target = config["target_iterations"]
    complete = []
    partial = []
    missing = []
    gaps = {}

    models_seen = set()
    for ship_name in ships:
        if ship_name not in architecture_matrix:
            continue

        model = architecture_matrix[ship_name]["model"]
        if model in models_seen:
            continue
        models_seen.add(model)

        completed_iters = set(by_model.get(model, []))
        expected_iters = set(range(target))
        missing_iters = expected_iters - completed_iters

        if len(completed_iters) == target:
            complete.append(ship_name)
        elif len(completed_iters) == 0:
            missing.append(ship_name)
            gaps[ship_name] = {"iterations": list(range(target)), "model": model}
        else:
            partial.append((ship_name, len(completed_iters), sorted(missing_iters)))
            gaps[ship_name] = {"iterations": sorted(missing_iters), "model": model}

    return {
        "complete": complete,
        "partial": partial,
        "missing": missing,
        "gaps": gaps,
        "total_results": len(results),
        "expected_total": len(ships) * target,
    }


def print_gap_analysis(analysis: dict, run_name: str):
    """Print gap analysis summary."""
    print("=" * 70)
    print(f"RUN {run_name} GAP ANALYSIS")
    print("=" * 70)
    print(f"Total results: {analysis['total_results']} / {analysis['expected_total']}")
    print(f"Complete ships: {len(analysis['complete'])}")
    print(f"Partial ships: {len(analysis.get('partial', []))}")
    if 'missing' in analysis:
        print(f"Missing ships: {len(analysis['missing'])}")
    print()

    if analysis['complete']:
        print("COMPLETE:")
        for ship in analysis['complete'][:10]:
            print(f"  ✓ {ship}")
        if len(analysis['complete']) > 10:
            print(f"  ... and {len(analysis['complete']) - 10} more")
        print()

    if analysis.get('partial'):
        print("PARTIAL:")
        for item in analysis['partial']:
            if len(item) == 3:
                ship, count, missing = item
                if isinstance(missing, list):
                    print(f"  - {ship}: {count} done, missing {len(missing)} iters")
                else:
                    print(f"  - {ship}: {count} done, missing {missing}")
        print()

    if analysis.get('missing'):
        print("MISSING (not started):")
        for ship in analysis['missing']:
            print(f"  - {ship}")
        print()

    # Calculate total gaps
    gaps = analysis.get('gaps', {})
    if gaps:
        if 'iterations' in next(iter(gaps.values()), {}):
            total_gaps = sum(len(g.get('iterations', [])) for g in gaps.values())
        else:
            total_gaps = sum(g.get('missing', 0) for g in gaps.values())
        print(f"TOTAL GAPS: {total_gaps} experiments to fill")


# =============================================================================
# GAP FILLING
# =============================================================================

def fill_gaps_foundation(config: dict, ship_filter=None, mode="ship", dry_run=False, claude_key=12):
    """Fill gaps in foundation run023 data."""
    print("\n[INFO] Loading run023 module...")

    try:
        sys.path.insert(0, str(SCRIPT_DIR))
        import run023 as runner
        from run023 import KeyPool, ExperimentType, run_experiment
    except ImportError as e:
        print(f"[ERROR] Could not import run023: {e}")
        return

    # Load environment
    from dotenv import load_dotenv
    env_path = SCRIPT_DIR.parent / ".env"
    if env_path.exists():
        load_dotenv(env_path)

    runner.DRY_RUN = dry_run
    runner.KEY_POOL = KeyPool(start_offset=0, claude_key=claude_key)

    # Load current data
    data = load_current_results(config)
    results = data['results']

    if mode == "ship":
        fill_gaps_foundation_ship_mode(config, data, results, runner, ship_filter, dry_run)
    else:
        fill_gaps_foundation_exp_mode(config, data, results, runner, ship_filter, dry_run)


def fill_gaps_foundation_ship_mode(config, data, results, runner, ship_filter, dry_run):
    """Fill gaps by completing ships to N=30 iterations."""
    from fleet_loader import load_architecture_matrix
    from run023 import ExperimentType, run_experiment

    # Count by model
    model_counts = defaultdict(int)
    models_in_data = set()
    for r in results:
        model = r.get('model', 'unknown')
        model_counts[model] += 1
        models_in_data.add(model)

    # Identify partial ships
    architecture_matrix = load_architecture_matrix()
    target = config["target_results"]
    partial_ships = []
    models_added = set()

    for ship_name, ship_config in architecture_matrix.items():
        model = ship_config.get('model', '')
        if model not in models_in_data:
            continue
        if model in models_added:
            continue

        current = model_counts.get(model, 0)
        if current < target:
            needed = target - current
            iterations_needed = needed // config["experiments_per_iter"]
            if iterations_needed > 0:
                partial_ships.append({
                    'ship_name': ship_name,
                    'model': model,
                    'current': current,
                    'needed': needed,
                    'iterations': iterations_needed,
                    'config': ship_config
                })
                models_added.add(model)

    # Filter by ship if specified
    if ship_filter:
        partial_ships = [s for s in partial_ships
                        if any(f.lower() in s['ship_name'].lower() for f in ship_filter)]

    if not partial_ships:
        print("\n[SUCCESS] All ships are complete!")
        return

    print(f"\n{'=' * 70}")
    print("PARTIAL SHIPS TO COMPLETE")
    print(f"{'=' * 70}")
    for s in partial_ships:
        print(f"  {s['ship_name']}: {s['current']}/{target} (need {s['iterations']} iters)")

    if dry_run:
        print("\n[DRY RUN] Would fill the above gaps")
        return

    # Run experiments
    experiments = list(ExperimentType)

    for ship_idx, ship_info in enumerate(partial_ships):
        ship_name = ship_info['ship_name']
        model_config = ship_info['config'].copy()
        model_config['ship_name'] = ship_name
        iterations_needed = ship_info['iterations']
        start_iter = ship_info['current'] // config["experiments_per_iter"]

        print(f"\n{'=' * 60}")
        print(f"SHIP {ship_idx + 1}/{len(partial_ships)}: {ship_name}")
        print(f"{'=' * 60}")

        ship_results = []
        for iteration in range(iterations_needed):
            actual_iter = start_iter + iteration
            include_exit_survey = (actual_iter < 10)

            for exp_type in experiments:
                try:
                    print(f"  [{ship_name}] {exp_type.value} (iter {actual_iter + 1})")
                    result = run_experiment(ship_name, model_config, exp_type,
                                          include_exit_survey=include_exit_survey)
                    ship_results.append(result)

                except Exception as e:
                    print(f"    [ERROR] {e}")
                    time.sleep(3)

        # Save checkpoint
        data['results'].extend([asdict(r) for r in ship_results])
        data['last_updated'] = datetime.now().isoformat()

        with open(config["results_file"], 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, default=str)

        print(f"  [SAVED] Now {len(data['results'])} total results")


def fill_gaps_foundation_exp_mode(config, data, results, runner, ship_filter, dry_run):
    """Fill individual missing experiments."""
    from run023 import ExperimentType, run_experiment

    # Count by model and experiment
    model_exp_counts = defaultdict(lambda: defaultdict(int))
    for r in results:
        model = r.get('model', 'unknown')
        exp = r.get('experiment', 'unknown')
        model_exp_counts[model][exp] += 1

    # Find all gaps
    experiments = list(ExperimentType)
    target_per_exp = config["target_iterations"]
    gaps = []

    for model in model_exp_counts:
        for exp_type in experiments:
            count = model_exp_counts[model].get(exp_type.value, 0)
            if count < target_per_exp:
                missing = target_per_exp - count
                for _ in range(missing):
                    gaps.append({
                        'model': model,
                        'exp_type': exp_type,
                    })

    if ship_filter:
        gaps = [g for g in gaps
                if any(f.lower() in g['model'].lower() for f in ship_filter)]

    if not gaps:
        print("\n[SUCCESS] All experiments complete!")
        return

    print(f"\nGAPS TO FILL: {len(gaps)} experiments")

    if dry_run:
        print("[DRY RUN] Would fill the above gaps")
        return

    # Note: This mode requires ship_configs to be properly set up
    print("[WARNING] Experiment mode requires manual ship_configs setup")
    print("  Consider using --mode ship instead")


def fill_gaps_extended(config: dict, ship_filter=None, dry_run=False, claude_key=12):
    """Fill gaps in extended settling run023_extended data."""
    print("\n[INFO] Loading run023_extended module...")

    try:
        sys.path.insert(0, str(SCRIPT_DIR))
        import run023_extended as runner
        from run023_extended import run_extended_settling, KeyPool
        from fleet_loader import load_architecture_matrix
    except ImportError as e:
        print(f"[ERROR] Could not import run023_extended: {e}")
        return

    # Load environment
    from dotenv import load_dotenv
    env_path = SCRIPT_DIR.parent / ".env"
    if env_path.exists():
        load_dotenv(env_path)

    runner.DRY_RUN = dry_run
    runner.KEY_POOL = KeyPool(start_offset=0, claude_key=claude_key)

    # Get gap analysis
    analysis = analyze_gaps_extended(config)
    gaps = analysis['gaps']

    if not gaps:
        print("[INFO] No gaps to fill!")
        return

    # Filter ships if specified
    if ship_filter:
        gaps = {k: v for k, v in gaps.items()
                if any(f.lower() in k.lower() for f in ship_filter)}

    if not gaps:
        print(f"[INFO] No gaps found for specified ships: {ship_filter}")
        return

    total_gaps = sum(len(v.get('iterations', [])) for v in gaps.values())
    print(f"\n[INFO] Will fill {total_gaps} gaps across {len(gaps)} ships")

    if dry_run:
        print("[DRY RUN] Would fill these gaps:")
        for ship, info in gaps.items():
            iters = info.get('iterations', [])
            print(f"  {ship}: iterations {iters[:5]}{'...' if len(iters) > 5 else ''}")
        return

    # Load architecture matrix and current results
    architecture_matrix = load_architecture_matrix()
    data = load_current_results(config)
    results = data.get("results", [])

    # Track completed
    completed = set()
    for r in results:
        completed.add((r.get("model"), r.get("iteration")))

    # Fill gaps
    current = 0

    for ship_name, gap_info in gaps.items():
        if ship_name not in architecture_matrix:
            print(f"[WARNING] {ship_name} not in architecture matrix")
            continue

        model_config = architecture_matrix[ship_name].copy()
        model_config["ship_name"] = ship_name
        model_name = model_config["model"]
        missing_iters = gap_info.get('iterations', [])

        for iteration in missing_iters:
            current += 1

            if (model_name, iteration) in completed:
                print(f"[{current}/{total_gaps}] {ship_name} iter {iteration+1} - SKIPPED")
                continue

            try:
                print(f"\n[{current}/{total_gaps}] {ship_name} iter {iteration+1}")
                result = run_extended_settling(ship_name, model_config, iteration)

                results.append(asdict(result))
                completed.add((model_name, iteration))

                # Incremental save
                data["results"] = results
                with open(config["results_file"], 'w', encoding='utf-8') as f:
                    json.dump(data, f, indent=2, default=str)

            except Exception as e:
                print(f"    [ERROR] {ship_name} iter {iteration+1}: {e}")

    print(f"\n[DONE] Filled gaps. Total results: {len(results)}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Unified Gap Filler for Run 023 (foundation and extended)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python utility/fill_gaps.py --run 023 --analyze
    python utility/fill_gaps.py --run 023_extended --analyze
    python utility/fill_gaps.py --run 023 --ships grok-4-fast
    python utility/fill_gaps.py --run 023 --mode ship
    python utility/fill_gaps.py --run 023_extended --dry-run
        """
    )

    parser.add_argument("--run", choices=["023", "023_extended"], required=True,
                       help="Which run to analyze/fill (023 = foundation, 023_extended = settling)")
    parser.add_argument("--analyze", action="store_true",
                       help="Analyze gaps only, don't fill")
    parser.add_argument("--ships", nargs="+",
                       help="Specific ships to fill gaps for (partial match)")
    parser.add_argument("--mode", choices=["ship", "exp"], default="ship",
                       help="Fill mode: ship (complete partial ships) or exp (individual experiments)")
    parser.add_argument("--dry-run", action="store_true",
                       help="Show what would be filled without executing")
    parser.add_argument("--claude-key", type=int, default=12,
                       help="Which Claude API key to use (default: 12)")

    args = parser.parse_args()

    config = RUN_CONFIGS[args.run]

    # Analyze gaps
    if args.run == "023":
        analysis = analyze_gaps_foundation(config)
    else:
        analysis = analyze_gaps_extended(config)

    print_gap_analysis(analysis, args.run)

    if args.analyze:
        return 0

    # Fill gaps
    print()
    if args.run == "023":
        fill_gaps_foundation(config, ship_filter=args.ships, mode=args.mode,
                            dry_run=args.dry_run, claude_key=args.claude_key)
    else:
        fill_gaps_extended(config, ship_filter=args.ships,
                          dry_run=args.dry_run, claude_key=args.claude_key)

    return 0


if __name__ == "__main__":
    sys.exit(main())
