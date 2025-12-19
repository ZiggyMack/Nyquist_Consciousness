"""
S7 RUN 023b FINISH: Complete the remaining 6 ships
===================================================
This script loads the existing checkpoint (19/25 ships) and completes the run.

REMAINING SHIPS (6):
    - deepseek-r1-distill (Together)
    - deepseek-v3 (Together)
    - qwen3-80b (Together)
    - qwen2.5-72b (Together)
    - llama3.3-70b (Together)
    - mistral-small (Together)

The output will be MERGED into the existing checkpoint to create ONE unified data file.

USAGE:
    python run023b_finish.py                    # Complete remaining ships
    python run023b_finish.py --dry-run          # Test without API calls
    python run023b_finish.py -N 30              # Run 30 iterations per ship

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

# Add parent paths for imports
SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR.parent))
sys.path.insert(0, str(SCRIPT_DIR.parent / "1_CALIBRATION" / "lib"))

from dotenv import load_dotenv

# =============================================================================
# CONFIGURATION
# =============================================================================

RESULTS_DIR = SCRIPT_DIR / "results"
CHECKPOINT_FILE = RESULTS_DIR / "_CHECKPOINT_run023_20251218_021956.json"

# Remaining ships to run (human-readable names from fleet_loader)
REMAINING_SHIPS = [
    'deepseek-r1-distill',
    'deepseek-v3',
    'qwen3-80b',
    'qwen2.5-72b',
    'llama3.3-70b',
    'mistral-small',
]

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Complete run023b by running remaining 6 ships and merging results"
    )
    parser.add_argument("--dry-run", action="store_true",
                       help="Test flow without API calls")
    parser.add_argument("--claude-key", type=int, default=12,
                       help="Which API key to use for Claude models (default: 12)")
    parser.add_argument("-N", "--iterations", type=int, default=1,
                       help="Number of iterations per ship/experiment (default: 1)")
    parser.add_argument("--exit-survey-limit", type=int, default=10,
                       help="Only do exit surveys on first N iterations (default: 10)")

    args = parser.parse_args()

    # Load environment BEFORE importing run023b (it uses env vars)
    env_path = SCRIPT_DIR.parent / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f"[INFO] Loaded .env from {env_path}")

    # Now import from run023b (after env is loaded)
    import run023b_iron_clad_foundation as run023b

    # Set global DRY_RUN
    run023b.DRY_RUN = args.dry_run

    if args.dry_run:
        print("\n" + "=" * 70)
        print("DRY RUN MODE - No real API calls")
        print("=" * 70)

    # Import what we need
    from run023b_iron_clad_foundation import (
        KeyPool,
        ExperimentType,
        run_experiment,
        save_results,
    )
    from fleet_loader import load_architecture_matrix, get_fleet_by_option

    # Load checkpoint
    if not CHECKPOINT_FILE.exists():
        print(f"[ERROR] Checkpoint file not found: {CHECKPOINT_FILE}")
        print("  Cannot continue without existing data to merge")
        sys.exit(1)

    print(f"\n[INFO] Loading checkpoint: {CHECKPOINT_FILE.name}")
    with open(CHECKPOINT_FILE, 'r', encoding='utf-8') as f:
        checkpoint_data = json.load(f)

    existing_results = checkpoint_data['results']
    run_timestamp = checkpoint_data['run_timestamp']
    print(f"[INFO] Loaded {checkpoint_data['ships_completed']}/{checkpoint_data['total_ships']} ships")
    print(f"[INFO] {len(existing_results)} experiment results in checkpoint")

    # Get full fleet and filter to remaining ships
    full_fleet = get_fleet_by_option('budget_patrol-lite')
    remaining_fleet = [ship for ship in full_fleet if ship in REMAINING_SHIPS]

    print(f"\n{'=' * 70}")
    print("RUN 023b FINISH - Completing Remaining Ships")
    print(f"{'=' * 70}")
    print(f"Remaining ships: {len(remaining_fleet)}")
    for ship in remaining_fleet:
        print(f"  - {ship}")
    print(f"Iterations per ship: {args.iterations}")
    print(f"Exit survey limit: {args.exit_survey_limit}")
    print(f"Dry run: {args.dry_run}")

    # Initialize key pool
    run023b.KEY_POOL = KeyPool(start_offset=0, claude_key=args.claude_key)

    # Load architecture matrix
    architecture_matrix = load_architecture_matrix()

    # All experiments
    experiments = list(ExperimentType)

    # Track progress
    ships_completed = checkpoint_data['ships_completed']
    total_ships = checkpoint_data['total_ships']
    all_new_results = []

    # Run experiments for remaining ships
    for ship_idx, ship_name in enumerate(remaining_fleet):
        if ship_name not in architecture_matrix:
            print(f"\n  [WARNING] Ship {ship_name} not in architecture matrix, skipping")
            continue

        model_config = architecture_matrix[ship_name].copy()
        model_config["ship_name"] = ship_name

        print(f"\n{'=' * 60}")
        print(f"SHIP {ships_completed + ship_idx + 1}/{total_ships}: {ship_name}")
        print(f"{'=' * 60}")

        ship_results = []
        for exp_type in experiments:
            for iteration in range(args.iterations):
                include_exit_survey = (iteration < args.exit_survey_limit)
                iter_label = f" (iter {iteration + 1}/{args.iterations})" if args.iterations > 1 else ""
                survey_label = "" if include_exit_survey else " [no exit survey]"

                try:
                    print(f"\n  [{ship_name}] {exp_type.value}{iter_label}{survey_label}")
                    result = run_experiment(ship_name, model_config, exp_type,
                                          include_exit_survey=include_exit_survey)
                    ship_results.append(result)
                    all_new_results.append(result)
                except Exception as e:
                    print(f"    [ERROR] {ship_name}/{exp_type.value}{iter_label}: {e}")
                    import traceback
                    traceback.print_exc()

        # Save checkpoint after each ship
        ships_completed += 1

        # Merge results - checkpoint format has dicts, not objects
        merged_results = existing_results + [asdict(r) for r in all_new_results]

        checkpoint_update = {
            "run_timestamp": run_timestamp,
            "ships_completed": ships_completed,
            "total_ships": total_ships,
            "results": merged_results,
            "checkpoint_time": datetime.now().isoformat(),
            "finish_script": True,
        }

        with open(CHECKPOINT_FILE, 'w', encoding='utf-8') as f:
            json.dump(checkpoint_update, f, indent=2, default=str)

        print(f"\n  [CHECKPOINT] Saved {ships_completed}/{total_ships} ships ({len(merged_results)} results)")

    # Final summary
    print(f"\n{'=' * 70}")
    print("COMPLETION SUMMARY")
    print(f"{'=' * 70}")

    final_results = existing_results + [asdict(r) for r in all_new_results]
    print(f"Original results: {len(existing_results)}")
    print(f"New results: {len(all_new_results)}")
    print(f"Total results: {len(final_results)}")

    # Save final merged file
    final_file = RESULTS_DIR / f"S7_run_023b_COMPLETE_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

    final_data = {
        "run_id": "S7_run_023b",
        "run_name": "IRON CLAD Foundation (Cosine, Complete)",
        "run_timestamp": run_timestamp,
        "completion_timestamp": datetime.now().isoformat(),
        "ships_completed": total_ships,
        "total_ships": total_ships,
        "methodology": "cosine_embedding",
        "iterations_per_ship": args.iterations,
        "results": final_results,
    }

    with open(final_file, 'w', encoding='utf-8') as f:
        json.dump(final_data, f, indent=2, default=str)

    print(f"\n[SUCCESS] Final results saved to: {final_file.name}")
    print(f"[INFO] File size: {final_file.stat().st_size / 1024 / 1024:.2f} MB")

    # Stats
    stable_count = sum(1 for r in final_results if r.get('stability_classification') == 'STABLE')
    print(f"\nStability: {stable_count}/{len(final_results)} STABLE ({100*stable_count/len(final_results):.1f}%)")

    # Rename checkpoint to backup
    if not args.dry_run and all_new_results:
        backup_file = RESULTS_DIR / f"_CHECKPOINT_run023_BACKUP_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        CHECKPOINT_FILE.rename(backup_file)
        print(f"[INFO] Checkpoint backed up to: {backup_file.name}")

if __name__ == "__main__":
    main()
