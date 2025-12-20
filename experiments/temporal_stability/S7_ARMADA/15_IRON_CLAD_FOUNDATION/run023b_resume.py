"""
S7 RUN 023b RESUME: Continue from checkpoint with remaining ships
=================================================================
Resumes from the latest checkpoint and continues with remaining ships.
Ships 1-2 (deepseek-r1-distill, deepseek-v3) already have 6 results each.

REMAINING SHIPS (4):
    - qwen3-80b (Together)
    - qwen2.5-72b (Together)
    - llama3.3-70b (Together)
    - mistral-small (Together)

USAGE:
    python run023b_resume.py                    # Run remaining ships
    python run023b_resume.py --dry-run          # Test without API calls
    python run023b_resume.py -N 30              # Run 30 iterations per ship

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

# Find the latest checkpoint file
def find_latest_checkpoint():
    checkpoints = list(RESULTS_DIR.glob("_CHECKPOINT_iterations_*.json"))
    if not checkpoints:
        return None
    return max(checkpoints, key=lambda p: p.stat().st_mtime)

# Ships that still need data
# Ships 1-2 done: deepseek-r1-distill, deepseek-v3
# Ships 3-6 remaining:
REMAINING_SHIPS = [
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
        description="Resume run023b from checkpoint with remaining ships"
    )
    parser.add_argument("--dry-run", action="store_true",
                       help="Test flow without API calls")
    parser.add_argument("--claude-key", type=int, default=12,
                       help="Which API key to use for Claude models (default: 12)")
    parser.add_argument("-N", "--iterations", type=int, default=1,
                       help="Number of iterations per ship (default: 1)")
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
    )
    from fleet_loader import load_architecture_matrix

    # Load checkpoint if available
    checkpoint_file = find_latest_checkpoint()
    existing_results = []
    if checkpoint_file:
        print(f"\n[INFO] Loading checkpoint: {checkpoint_file.name}")
        with open(checkpoint_file, 'r', encoding='utf-8') as f:
            checkpoint_data = json.load(f)
        existing_results = checkpoint_data.get('new_results', [])
        print(f"[INFO] Found {len(existing_results)} existing new results")

    # Load the cleaned source file
    source_file = RESULTS_DIR / "S7_run_023b_CLEANED.json"
    if source_file.exists():
        with open(source_file, 'r', encoding='utf-8') as f:
            source_data = json.load(f)
        base_results = source_data['results']
        print(f"[INFO] Loaded {len(base_results)} base results from cleaned file")
    else:
        print(f"[ERROR] Source file not found: {source_file}")
        sys.exit(1)

    print(f"\n{'=' * 70}")
    print("RUN 023b RESUME")
    print(f"{'=' * 70}")
    print(f"Remaining ships: {len(REMAINING_SHIPS)}")
    for ship in REMAINING_SHIPS:
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
    total_new = len(REMAINING_SHIPS) * len(experiments) * args.iterations
    print(f"\nTotal new results to generate: {total_new}")

    # Track progress
    all_new_results = list(existing_results)  # Start with existing checkpoint data
    results_count = 0

    # Run experiments for remaining ships
    for ship_idx, ship_name in enumerate(REMAINING_SHIPS):
        if ship_name not in architecture_matrix:
            print(f"\n  [WARNING] Ship {ship_name} not in architecture matrix, skipping")
            continue

        model_config = architecture_matrix[ship_name].copy()
        model_config["ship_name"] = ship_name

        print(f"\n{'=' * 60}")
        print(f"SHIP {ship_idx + 1}/{len(REMAINING_SHIPS)}: {ship_name}")
        print(f"Model: {model_config.get('model', 'N/A')}")
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
                    all_new_results.append(asdict(result))
                    results_count += 1

                    if results_count % 10 == 0:
                        print(f"\n  [PROGRESS] {results_count}/{total_new} new results")

                except Exception as e:
                    print(f"    [ERROR] {ship_name}/{exp_type.value}{iter_label}: {e}")
                    import traceback
                    traceback.print_exc()
                    time.sleep(3)  # Longer delay after error

        # Save checkpoint after each ship
        checkpoint_file = RESULTS_DIR / f"_CHECKPOINT_resume_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

        checkpoint_data = {
            "ships_completed": ship_idx + 1 + 2,  # +2 for already-done ships
            "total_ships": len(REMAINING_SHIPS) + 2,
            "iterations_per_ship": args.iterations,
            "new_results": all_new_results,
            "checkpoint_time": datetime.now().isoformat(),
        }

        with open(checkpoint_file, 'w', encoding='utf-8') as f:
            json.dump(checkpoint_data, f, indent=2, default=str)

        print(f"\n  [CHECKPOINT] Ship {ship_idx + 1}/{len(REMAINING_SHIPS)} complete ({len(all_new_results)} new results)")

    # Final summary
    print(f"\n{'=' * 70}")
    print("COMPLETION SUMMARY")
    print(f"{'=' * 70}")

    final_results = base_results + all_new_results
    print(f"Base results: {len(base_results)}")
    print(f"New results: {len(all_new_results)}")
    print(f"Total results: {len(final_results)}")

    # Save final merged file
    final_file = RESULTS_DIR / f"S7_run_023b_MERGED_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

    final_data = {
        "run_id": "S7_run_023b",
        "run_name": "IRON CLAD Foundation (Cosine, Merged)",
        "completion_timestamp": datetime.now().isoformat(),
        "ships_completed": 25,
        "total_ships": 25,
        "methodology": "cosine_embedding",
        "iterations_per_ship": args.iterations,
        "results": final_results,
        "notes": "Merged base + new results with retry logic for rate limits"
    }

    with open(final_file, 'w', encoding='utf-8') as f:
        json.dump(final_data, f, indent=2, default=str)

    print(f"\n[SUCCESS] Final results saved to: {final_file.name}")
    print(f"[INFO] File size: {final_file.stat().st_size / 1024 / 1024:.2f} MB")

    # Per-model counts
    model_counts = {}
    for r in final_results:
        model = r.get('model', 'unknown')
        model_counts[model] = model_counts.get(model, 0) + 1

    print(f"\nResults per model:")
    for model, count in sorted(model_counts.items(), key=lambda x: -x[1]):
        print(f"  {model}: {count}")

if __name__ == "__main__":
    main()
