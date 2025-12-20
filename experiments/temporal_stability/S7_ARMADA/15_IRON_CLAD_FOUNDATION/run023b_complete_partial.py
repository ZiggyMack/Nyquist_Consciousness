"""
S7 RUN 023b COMPLETE PARTIAL: Fill in missing iterations for partial ships
=========================================================================
Reads S7_run_023b_CURRENT.json, identifies ships with <180 results,
and runs the exact number of iterations needed to reach N=30.

USAGE:
    python run023b_complete_partial.py                    # Complete all partial ships
    python run023b_complete_partial.py --dry-run          # Test without API calls
    python run023b_complete_partial.py --ship grok-4-fast # Only complete one ship

Author: Claude (VALIS Network)
Date: December 19, 2025
"""

import os
import sys
import json
import time
import argparse
from datetime import datetime
from pathlib import Path
from dataclasses import asdict
from collections import defaultdict

# Add parent paths for imports
SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR.parent))
sys.path.insert(0, str(SCRIPT_DIR.parent / "1_CALIBRATION" / "lib"))

from dotenv import load_dotenv

RESULTS_DIR = SCRIPT_DIR / "results"
SOURCE_FILE = RESULTS_DIR / "S7_run_023b_CURRENT.json"
TARGET_RESULTS = 180  # N=30 iterations × 6 experiments

def main():
    parser = argparse.ArgumentParser(
        description="Complete partial ships to N=30"
    )
    parser.add_argument("--dry-run", action="store_true",
                       help="Test flow without API calls")
    parser.add_argument("--claude-key", type=int, default=12,
                       help="Which API key to use for Claude models (default: 12)")
    parser.add_argument("--ship", type=str, default=None,
                       help="Only complete specific ship (partial match)")
    parser.add_argument("--exit-survey-limit", type=int, default=10,
                       help="Only do exit surveys on first N iterations (default: 10)")

    args = parser.parse_args()

    # Load environment
    env_path = SCRIPT_DIR.parent / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f"[INFO] Loaded .env from {env_path}", flush=True)

    # Import after env loaded
    import run023b_iron_clad_foundation as run023b
    from run023b_iron_clad_foundation import KeyPool, ExperimentType, run_experiment
    from fleet_loader import load_architecture_matrix

    run023b.DRY_RUN = args.dry_run
    if args.dry_run:
        print("\n" + "=" * 70, flush=True)
        print("DRY RUN MODE - No real API calls", flush=True)
        print("=" * 70, flush=True)

    # Load current data
    if not SOURCE_FILE.exists():
        print(f"[ERROR] Source file not found: {SOURCE_FILE}", flush=True)
        sys.exit(1)

    print(f"\n[INFO] Loading: {SOURCE_FILE.name}", flush=True)
    with open(SOURCE_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    existing_results = data['results']
    print(f"[INFO] Loaded {len(existing_results)} existing results", flush=True)

    # Count by model - only consider models that already have data
    model_counts = defaultdict(int)
    models_in_data = set()
    for r in existing_results:
        model = r.get('model', 'unknown')
        model_counts[model] += 1
        models_in_data.add(model)

    # Identify partial ships - only ships that are ALREADY in the data
    # Track which models we've already added to avoid duplicates
    architecture_matrix = load_architecture_matrix()
    partial_ships = []
    models_added = set()

    for ship_name, config in architecture_matrix.items():
        model = config.get('model', '')
        # Skip ships that have NO data (they weren't part of this run)
        if model not in models_in_data:
            continue
        # Skip if we already added this model (avoid duplicates like "google" vs "gemini-2.0-flash")
        if model in models_added:
            continue
        current = model_counts.get(model, 0)
        if current < TARGET_RESULTS:
            needed = TARGET_RESULTS - current
            iterations_needed = needed // 6  # 6 experiments per iteration
            if iterations_needed > 0:  # Only add if we actually need iterations
                partial_ships.append({
                    'ship_name': ship_name,
                    'model': model,
                    'current': current,
                    'needed': needed,
                    'iterations': iterations_needed,
                    'config': config
                })
                models_added.add(model)

    if not partial_ships:
        print("\n[SUCCESS] All ships are complete!", flush=True)
        return

    # Filter by --ship if specified
    if args.ship:
        partial_ships = [s for s in partial_ships if args.ship.lower() in s['ship_name'].lower()]
        if not partial_ships:
            print(f"[ERROR] No partial ships matching '{args.ship}'", flush=True)
            sys.exit(1)

    print(f"\n{'=' * 70}", flush=True)
    print("PARTIAL SHIPS TO COMPLETE", flush=True)
    print(f"{'=' * 70}", flush=True)
    for s in partial_ships:
        print(f"  {s['ship_name']}: {s['current']}/{TARGET_RESULTS} (need {s['iterations']} iters)", flush=True)

    total_new = sum(s['needed'] for s in partial_ships)
    print(f"\nTotal new results to generate: {total_new}", flush=True)

    # Initialize key pool
    run023b.KEY_POOL = KeyPool(start_offset=0, claude_key=args.claude_key)

    # Process each ship
    all_new_results = []
    experiments = list(ExperimentType)

    for ship_idx, ship_info in enumerate(partial_ships):
        ship_name = ship_info['ship_name']
        model_config = ship_info['config'].copy()
        model_config['ship_name'] = ship_name
        iterations_needed = ship_info['iterations']
        current_count = ship_info['current']
        start_iter = current_count // 6

        print(f"\n{'=' * 60}", flush=True)
        print(f"SHIP {ship_idx + 1}/{len(partial_ships)}: {ship_name}", flush=True)
        print(f"Model: {model_config.get('model', 'N/A')}", flush=True)
        print(f"Current: {current_count}, Need: {iterations_needed} iterations", flush=True)
        print(f"{'=' * 60}", flush=True)

        ship_results = []
        for iteration in range(iterations_needed):
            actual_iter = start_iter + iteration
            include_exit_survey = (actual_iter < args.exit_survey_limit)

            for exp_type in experiments:
                iter_label = f" (iter {actual_iter + 1}/30)"
                survey_label = "" if include_exit_survey else " [no exit survey]"

                try:
                    print(f"\n  [{ship_name}] {exp_type.value}{iter_label}{survey_label}", flush=True)
                    result = run_experiment(ship_name, model_config, exp_type,
                                          include_exit_survey=include_exit_survey)
                    ship_results.append(result)
                    all_new_results.append(asdict(result))

                    # Progress
                    done = len(all_new_results)
                    if done % 50 == 0:
                        print(f"\n  [PROGRESS] {done}/{total_new} new results", flush=True)

                except Exception as e:
                    print(f"    [ERROR] {ship_name}/{exp_type.value}: {e}", flush=True)
                    import traceback
                    traceback.print_exc()
                    time.sleep(3)

        # Save checkpoint after each ship
        print(f"\n  [SAVING] Updating {SOURCE_FILE.name}...", flush=True)
        data['results'].extend([asdict(r) for r in ship_results])
        data['last_updated'] = datetime.now().isoformat()

        with open(SOURCE_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, default=str)

        print(f"  [SAVED] Now {len(data['results'])} total results", flush=True)

    # Final summary
    print(f"\n{'=' * 70}", flush=True)
    print("COMPLETION SUMMARY", flush=True)
    print(f"{'=' * 70}", flush=True)
    print(f"New results added: {len(all_new_results)}", flush=True)
    print(f"Total results: {len(data['results'])}", flush=True)

    # Recount
    final_counts = defaultdict(int)
    for r in data['results']:
        model = r.get('model', 'unknown')
        final_counts[model] += 1

    incomplete = []
    for model, count in sorted(final_counts.items()):
        status = "COMPLETE" if count >= TARGET_RESULTS else f"PARTIAL ({count})"
        if count < TARGET_RESULTS:
            incomplete.append(model)

    if incomplete:
        print(f"\n[WARNING] {len(incomplete)} ships still incomplete", flush=True)
    else:
        print(f"\n[SUCCESS] All ships complete!", flush=True)

if __name__ == "__main__":
    main()
