"""
S7 RUN 018: GAP FILLER
=======================
Fills remaining gaps to reach IRON CLAD status (N=3 per model per experiment).

Uses the same experiment logic as run018_recursive_learnings.py but:
- Only runs experiments that are below target N
- Appends to S7_run_018_CURRENT.json incrementally
- Updates STATUS_SUMMARY_018.txt after each result

Usage:
  py run018_fill_gaps.py                    # Show gaps, don't run
  py run018_fill_gaps.py --execute          # Fill all gaps
  py run018_fill_gaps.py --execute --max 10 # Fill at most 10 gaps
  py run018_fill_gaps.py --dry-run          # Test mode (no API calls)

Author: Claude (Lisan Al Gaib)
Date: December 21, 2025
"""

import os
import sys
import json
import time
import argparse
from pathlib import Path
from datetime import datetime
from dataclasses import asdict

# Import from main script
SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

from run018_recursive_learnings import (
    # Core functions
    load_or_create_results,
    save_incremental,
    update_status_summary,
    detect_gaps,
    append_result,
    clear_embedding_cache,
    load_i_am_file,
    KeyPool,
    KEY_POOL,
    # Experiment runners
    run_threshold_experiment,
    run_architecture_experiment,
    run_nyquist_experiment,
    run_gravity_experiment,
    # Constants
    RESULTS_FILE,
    STATUS_FILE,
    DRY_RUN,
    ARMADA_DIR,
)

# Load environment
try:
    from dotenv import load_dotenv
except ImportError:
    def load_dotenv(path):
        if path and path.exists():
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, _, value = line.partition('=')
                        os.environ[key.strip()] = value.strip().strip('"').strip("'")


def show_gaps():
    """Display current gaps in IRON CLAD coverage."""
    gaps = detect_gaps(target_n=3)

    if not gaps:
        print("\n" + "=" * 60)
        print("IRON CLAD COMPLETE - No gaps remaining!")
        print("=" * 60)
        return []

    print("\n" + "=" * 60)
    print(f"RUN 018 GAPS ({len(gaps)} remaining)")
    print("=" * 60)

    by_experiment = {}
    for gap in gaps:
        exp = gap["experiment"]
        if exp not in by_experiment:
            by_experiment[exp] = []
        by_experiment[exp].append(gap)

    total_runs_needed = 0
    for exp in ["threshold", "architecture", "nyquist", "gravity"]:
        if exp in by_experiment:
            print(f"\n{exp.upper()}:")
            for gap in sorted(by_experiment[exp], key=lambda x: -x["need"]):
                print(f"  {gap['model']}: {gap['have']}/3 (need {gap['need']})")
                total_runs_needed += gap["need"]

    print(f"\n" + "-" * 60)
    print(f"TOTAL RUNS NEEDED: {total_runs_needed}")
    print("=" * 60)

    return gaps


def fill_gap(gap: dict, i_am_content: str, key_pool) -> bool:
    """
    Fill a single gap by running the experiment once.
    Returns True if successful.
    """
    import run018_recursive_learnings as main_script
    main_script.KEY_POOL = key_pool

    experiment = gap["experiment"]
    model = gap["model"]

    print(f"\n>>> FILLING GAP: {experiment} / {model} <<<")

    try:
        if experiment == "threshold":
            analysis = run_threshold_experiment(
                i_am_content, "base",
                skip_exit_survey=False,
                provider=model
            )
        elif experiment == "architecture":
            analysis = run_architecture_experiment(
                model, i_am_content,
                skip_exit_survey=False
            )
        elif experiment == "nyquist":
            analysis = run_nyquist_experiment(
                "high", i_am_content,
                skip_exit_survey=False,
                provider=model
            )
        elif experiment == "gravity":
            analysis = run_gravity_experiment(
                "full", i_am_content,
                skip_exit_survey=False,
                provider=model
            )
        else:
            print(f"  [ERROR] Unknown experiment type: {experiment}")
            return False

        # Convert to dict and append
        result_dict = asdict(analysis)
        append_result(result_dict, experiment, model)

        print(f"  [SUCCESS] {experiment}/{model} completed")
        return True

    except Exception as e:
        print(f"  [FAILED] {experiment}/{model}: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Fill gaps in Run 018 IRON CLAD coverage"
    )
    parser.add_argument("--execute", action="store_true",
                       help="Actually run experiments (default: just show gaps)")
    parser.add_argument("--max", type=int, default=0,
                       help="Maximum number of gaps to fill (0 = all)")
    parser.add_argument("--dry-run", action="store_true",
                       help="Use mock responses (no API calls)")
    parser.add_argument("--key-offset", "-k", type=int, default=0,
                       help="Starting offset in key pool")
    parser.add_argument("--i-am", type=str, default="base",
                       help="I_AM persona to use")

    args = parser.parse_args()

    # Set dry-run mode in main script
    import run018_recursive_learnings as main_script
    main_script.DRY_RUN = args.dry_run

    # Clear cache if not dry-run
    if not args.dry_run:
        clear_embedding_cache()

    # Load environment
    env_path = ARMADA_DIR / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f"Loaded API keys from: {env_path}")

    # Initialize key pool
    key_pool = KeyPool(start_offset=args.key_offset)

    # Show current gaps
    gaps = show_gaps()

    if not gaps:
        return

    if not args.execute:
        print("\nTo fill gaps, run with --execute flag")
        return

    # Load I_AM content
    i_am_content = load_i_am_file(args.i_am)

    # Fill gaps
    print("\n" + "=" * 60)
    print("FILLING GAPS")
    print("=" * 60)

    if args.dry_run:
        print("*** DRY RUN MODE - No API calls ***")

    max_gaps = args.max if args.max > 0 else len(gaps)
    success_count = 0
    fail_count = 0

    for i, gap in enumerate(gaps[:max_gaps]):
        print(f"\n[{i+1}/{min(len(gaps), max_gaps)}]")

        if fill_gap(gap, i_am_content, key_pool):
            success_count += 1
        else:
            fail_count += 1

        # Rate limiting
        time.sleep(1.0)

    # Final summary
    print("\n" + "=" * 60)
    print("GAP FILL COMPLETE")
    print("=" * 60)
    print(f"  Success: {success_count}")
    print(f"  Failed: {fail_count}")
    print(f"  Results: {RESULTS_FILE}")
    print(f"  Status: {STATUS_FILE}")

    # Show remaining gaps
    remaining = detect_gaps(target_n=3)
    if remaining:
        print(f"\n  Remaining gaps: {len(remaining)}")
    else:
        print("\n  IRON CLAD COMPLETE!")


if __name__ == "__main__":
    main()
