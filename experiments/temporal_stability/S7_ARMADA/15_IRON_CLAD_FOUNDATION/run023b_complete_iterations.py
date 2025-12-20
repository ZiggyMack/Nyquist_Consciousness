"""
S7 RUN 023b COMPLETE ITERATIONS: Run all 30 iterations for 6 ships
==================================================================
The 6 Together.ai ships had DRY_RUN fake data (36 results), not real API calls.
This script loads the CLEANED file (real data only) and runs all 30 iterations.

SHIPS TO COMPLETE (6) - ZERO real data, need 180 each:
    - deepseek-r1-distill (Together)
    - deepseek-v3 (Together)
    - qwen3-80b (Together)
    - qwen2.5-72b (Together)
    - llama3.3-70b (Together)
    - mistral-small (Together)

FIX APPLIED: DeepSeek-V3 model name fixed from
    deepseek-ai/DeepSeek-V3-0324 -> deepseek-ai/DeepSeek-V3

NOTE: Previous "finish" script results were DRY_RUN mode (fake data)!

USAGE:
    python run023b_complete_iterations.py                    # Run remaining 29 iterations
    python run023b_complete_iterations.py --dry-run          # Test without API calls
    python run023b_complete_iterations.py -N 5               # Run only 5 more iterations

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
# Load from the CLEANED file (DRY_RUN data removed)
SOURCE_FILE = RESULTS_DIR / "S7_run_023b_CLEANED.json"

# Ships that need ALL iterations (they had DRY_RUN fake data, now have 0)
INCOMPLETE_SHIPS = [
    'deepseek-r1-distill',
    'deepseek-v3',
    'qwen3-80b',
    'qwen2.5-72b',
    'llama3.3-70b',
    'mistral-small',
]

# Target iterations (they have 0 real data, need 30)
TARGET_ITERATIONS = 30
EXISTING_ITERATIONS = 0  # Changed from 1 - they had DRY_RUN data, not real

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Complete the remaining 29 iterations for 6 Together.ai ships"
    )
    parser.add_argument("--dry-run", action="store_true",
                       help="Test flow without API calls")
    parser.add_argument("--claude-key", type=int, default=12,
                       help="Which API key to use for Claude models (default: 12)")
    parser.add_argument("-N", "--iterations", type=int, default=TARGET_ITERATIONS - EXISTING_ITERATIONS,
                       help=f"Additional iterations per ship (default: {TARGET_ITERATIONS - EXISTING_ITERATIONS})")
    parser.add_argument("--exit-survey-limit", type=int, default=10,
                       help="Only do exit surveys on first N iterations (default: 10)")
    parser.add_argument("--start-iteration", type=int, default=EXISTING_ITERATIONS,
                       help=f"Starting iteration number for labeling (default: {EXISTING_ITERATIONS})")

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
    )
    from fleet_loader import load_architecture_matrix

    # Load source file
    if not SOURCE_FILE.exists():
        print(f"[ERROR] Source file not found: {SOURCE_FILE}")
        sys.exit(1)

    print(f"\n[INFO] Loading source data: {SOURCE_FILE.name}")
    with open(SOURCE_FILE, 'r', encoding='utf-8') as f:
        source_data = json.load(f)

    existing_results = source_data['results']
    run_timestamp = source_data.get('run_timestamp', datetime.now().isoformat())
    print(f"[INFO] Loaded {len(existing_results)} existing results")

    # Calculate iterations needed
    iterations_to_run = args.iterations
    start_iteration = args.start_iteration
    end_iteration = start_iteration + iterations_to_run

    print(f"\n{'=' * 70}")
    print("RUN 023b COMPLETE ITERATIONS")
    print(f"{'=' * 70}")
    print(f"Ships to complete: {len(INCOMPLETE_SHIPS)}")
    for ship in INCOMPLETE_SHIPS:
        print(f"  - {ship}")
    print(f"Iterations to add: {iterations_to_run} (iterations {start_iteration + 1} to {end_iteration})")
    print(f"Exit survey limit: {args.exit_survey_limit}")
    print(f"Dry run: {args.dry_run}")

    # Initialize key pool
    run023b.KEY_POOL = KeyPool(start_offset=0, claude_key=args.claude_key)

    # Load architecture matrix (has the FIXED DeepSeek-V3 model name!)
    architecture_matrix = load_architecture_matrix()

    # Verify the fix
    if 'deepseek-v3' in architecture_matrix:
        model = architecture_matrix['deepseek-v3'].get('model', '')
        if 'DeepSeek-V3-0324' in model:
            print(f"\n[WARNING] DeepSeek-V3 still has OLD model name: {model}")
            print("[WARNING] Should be: deepseek-ai/DeepSeek-V3")
        else:
            print(f"\n[INFO] DeepSeek-V3 model name: {model}")

    # All experiments
    experiments = list(ExperimentType)
    total_new = len(INCOMPLETE_SHIPS) * len(experiments) * iterations_to_run
    print(f"\nTotal new results to generate: {total_new}")

    # Track progress
    all_new_results = []
    results_count = 0

    # Run experiments for incomplete ships
    for ship_idx, ship_name in enumerate(INCOMPLETE_SHIPS):
        if ship_name not in architecture_matrix:
            print(f"\n  [WARNING] Ship {ship_name} not in architecture matrix, skipping")
            continue

        model_config = architecture_matrix[ship_name].copy()
        model_config["ship_name"] = ship_name

        print(f"\n{'=' * 60}")
        print(f"SHIP {ship_idx + 1}/{len(INCOMPLETE_SHIPS)}: {ship_name}")
        print(f"Model: {model_config.get('model', 'N/A')}")
        print(f"{'=' * 60}")

        ship_results = []
        for exp_type in experiments:
            for iteration in range(iterations_to_run):
                actual_iteration = start_iteration + iteration
                # Exit surveys only for first 10 TOTAL iterations (they already have 1)
                include_exit_survey = (actual_iteration < args.exit_survey_limit)
                iter_label = f" (iter {actual_iteration + 1}/{TARGET_ITERATIONS})"
                survey_label = "" if include_exit_survey else " [no exit survey]"

                try:
                    print(f"\n  [{ship_name}] {exp_type.value}{iter_label}{survey_label}")
                    result = run_experiment(ship_name, model_config, exp_type,
                                          include_exit_survey=include_exit_survey)
                    ship_results.append(result)
                    all_new_results.append(result)
                    results_count += 1

                    if results_count % 50 == 0:
                        print(f"\n  [PROGRESS] {results_count}/{total_new} new results")

                except Exception as e:
                    print(f"    [ERROR] {ship_name}/{exp_type.value}{iter_label}: {e}")
                    import traceback
                    traceback.print_exc()

                    # Add small delay after error to avoid hammering API
                    time.sleep(2)

        # Save checkpoint after each ship completes
        checkpoint_file = RESULTS_DIR / f"_CHECKPOINT_iterations_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

        checkpoint_data = {
            "source_file": str(SOURCE_FILE.name),
            "ships_completed": ship_idx + 1,
            "total_ships": len(INCOMPLETE_SHIPS),
            "iterations_per_ship": iterations_to_run,
            "new_results": [asdict(r) for r in all_new_results],
            "checkpoint_time": datetime.now().isoformat(),
        }

        with open(checkpoint_file, 'w', encoding='utf-8') as f:
            json.dump(checkpoint_data, f, indent=2, default=str)

        print(f"\n  [CHECKPOINT] Ship {ship_idx + 1}/{len(INCOMPLETE_SHIPS)} complete ({len(all_new_results)} new results)")

    # Final summary
    print(f"\n{'=' * 70}")
    print("COMPLETION SUMMARY")
    print(f"{'=' * 70}")

    final_results = existing_results + [asdict(r) for r in all_new_results]
    print(f"Original results: {len(existing_results)}")
    print(f"New results: {len(all_new_results)}")
    print(f"Total results: {len(final_results)}")

    # Save final merged file
    final_file = RESULTS_DIR / f"S7_run_023b_FINAL_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

    final_data = {
        "run_id": "S7_run_023b",
        "run_name": "IRON CLAD Foundation (Cosine, N=30 Complete)",
        "run_timestamp": run_timestamp,
        "completion_timestamp": datetime.now().isoformat(),
        "ships_completed": 25,
        "total_ships": 25,
        "methodology": "cosine_embedding",
        "iterations_per_ship": TARGET_ITERATIONS,
        "results": final_results,
        "notes": "Completed with fixed DeepSeek-V3 model name (deepseek-ai/DeepSeek-V3)"
    }

    with open(final_file, 'w', encoding='utf-8') as f:
        json.dump(final_data, f, indent=2, default=str)

    print(f"\n[SUCCESS] Final results saved to: {final_file.name}")
    print(f"[INFO] File size: {final_file.stat().st_size / 1024 / 1024:.2f} MB")

    # Stats
    stable_count = sum(1 for r in final_results if r.get('stability_classification') == 'STABLE')
    print(f"\nStability: {stable_count}/{len(final_results)} STABLE ({100*stable_count/len(final_results):.1f}%)")

    # Per-model counts
    model_counts = {}
    for r in final_results:
        model = r.get('model', 'unknown')
        model_counts[model] = model_counts.get(model, 0) + 1

    print(f"\nResults per model (expect 180 each):")
    incomplete = []
    for model, count in sorted(model_counts.items()):
        status = "OK" if count >= 180 else "INCOMPLETE"
        if count < 180:
            incomplete.append(model)
        print(f"  {model}: {count} [{status}]")

    if incomplete:
        print(f"\n[WARNING] {len(incomplete)} models still incomplete!")
    else:
        print(f"\n[SUCCESS] All models have complete data!")

if __name__ == "__main__":
    main()
