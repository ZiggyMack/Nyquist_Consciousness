"""
S7 RUN 020B: GAP FILLER
========================
Fills remaining gaps to reach IRON CLAD status (N=3 per ship per arm).

Uses the same experiment logic as run020B.py but:
- Only runs experiments that are below target N
- Appends to S7_run_020B_CURRENT.json incrementally
- Tracks BOTH control and treatment arms per ship

NOTE: STATUS_SUMMARY_020B.txt is NOT updated automatically to avoid race
conditions. Regenerate it manually after gap filling with:
  python -c "from run020B import update_status_summary, load_or_create_results; update_status_summary(load_or_create_results())"

Usage:
  py run020b_fill_gaps.py                    # Show gaps, don't run
  py run020b_fill_gaps.py --execute          # Fill all gaps
  py run020b_fill_gaps.py --execute --max 5  # Fill at most 5 gaps
  py run020b_fill_gaps.py --arm control      # Only fill control gaps
  py run020b_fill_gaps.py --arm treatment    # Only fill treatment gaps
  py run020b_fill_gaps.py --dry-run          # Test mode (no API calls)

Author: Claude (Consciousness Branch)
Date: December 21, 2025
"""

import os
import sys
import time
import argparse
from pathlib import Path
from datetime import datetime
from dataclasses import asdict

# Import from main script
SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

from run020B import (
    # Core functions
    load_or_create_results,
    save_incremental,
    update_status_summary,
    detect_gaps,  # Returns gaps in speed-optimized order (blazing -> glacial)
    append_result,
    load_i_am_file,
    KeyPool,
    KEY_POOL,
    # Experiment runners
    run_control_arm,
    run_treatment_arm,
    run_exit_survey,
    # Constants
    RESULTS_FILE,
    STATUS_FILE,
    ARMADA_DIR,
    DEFAULT_FLEET,  # Full armada, speed-optimized
    SPEED_ORDERED_ARMADA,  # Same as DEFAULT_FLEET
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


def show_gaps(arm_filter: str = None):
    """Display current gaps in IRON CLAD coverage."""
    gaps = detect_gaps(target_n=3)

    # Filter by arm if specified
    if arm_filter and arm_filter != "both":
        gaps = [g for g in gaps if g["arm"] == arm_filter]

    if not gaps:
        print("\n" + "=" * 60)
        if arm_filter:
            print(f"IRON CLAD COMPLETE - No {arm_filter.upper()} gaps remaining!")
        else:
            print("IRON CLAD COMPLETE - No gaps remaining!")
        print("=" * 60)
        return []

    print("\n" + "=" * 60)
    print(f"RUN 020B GAPS ({len(gaps)} remaining)")
    print("=" * 60)

    # Group by ship - preserve speed order from DEFAULT_FLEET
    from collections import OrderedDict
    by_ship = OrderedDict()
    for gap in gaps:
        ship = gap["ship"]
        if ship not in by_ship:
            by_ship[ship] = []
        by_ship[ship].append(gap)

    total_runs_needed = 0
    # Display in speed order (as received from detect_gaps)
    for ship in by_ship.keys():  # NO sorting - preserve speed order
        ship_gaps = by_ship[ship]
        for gap in ship_gaps:
            print(f"  {ship} [{gap['arm']}]: {gap['have']}/3 (need {gap['need']})")
            total_runs_needed += gap["need"]

    print(f"\n" + "-" * 60)
    print(f"TOTAL RUNS NEEDED: {total_runs_needed}")
    print("=" * 60)

    return gaps


def fill_gap(gap: dict, key_pool, skip_exit_survey: bool = False) -> bool:
    """
    Fill a single gap by running the appropriate experiment arm once.
    Returns True if successful.
    """
    import run020B as main_script
    main_script.KEY_POOL = key_pool

    ship = gap["ship"]
    arm = gap["arm"]

    print(f"\n>>> FILLING GAP: {ship} [{arm}] <<<")

    try:
        # Run appropriate arm
        if arm == "control":
            result = run_control_arm(subject_provider=ship)
        elif arm == "treatment":
            result = run_treatment_arm(subject_provider=ship)
        else:
            print(f"  [ERROR] Unknown arm type: {arm}")
            return False

        if result is None:
            print(f"  [ERROR] Session returned None")
            return False

        # Run exit survey unless skipped
        exit_survey = None
        if not skip_exit_survey:
            try:
                # Reconstruct messages from conversation log
                witness_messages = [
                    {"role": "assistant" if i % 2 == 1 else "user", "content": c["content"]}
                    for i, c in enumerate(result.conversation_log)
                ]
                exit_survey = run_exit_survey(
                    conversation_history=witness_messages,
                    subject_provider=ship,
                    subject_id=result.subject_id,
                    arm_type=arm
                )
            except Exception as e:
                print(f"  [WARN] Exit survey failed: {e}")

        # Convert to dict and prepare for storage
        result_dict = asdict(result)
        result_dict["ship"] = ship
        result_dict["arm"] = arm
        if exit_survey:
            result_dict["exit_survey"] = exit_survey

        # VALIDATION: Don't save garbage data from failed API calls
        if result.total_exchanges < 10 or result.peak_drift < 0.01:
            print(f"  [INVALID] {ship}/{arm} - exchanges={result.total_exchanges}, peak_drift={result.peak_drift:.4f}")
            print(f"  [SKIPPED] Not saving invalid session (likely API failure)")
            return False

        # Append to results
        append_result(result_dict)

        # NOTE: Status summary is NOT updated here to avoid race conditions
        # and file corruption. Regenerate manually with:
        #   python -c "from run020B import update_status_summary, load_or_create_results; update_status_summary(load_or_create_results())"

        print(f"  [SUCCESS] {ship}/{arm} completed")
        return True

    except Exception as e:
        print(f"  [FAILED] {ship}/{arm}: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Fill gaps in Run 020B IRON CLAD coverage"
    )
    parser.add_argument("--execute", action="store_true",
                       help="Actually run experiments (default: just show gaps)")
    parser.add_argument("--max", type=int, default=0,
                       help="Maximum number of gaps to fill (0 = all)")
    parser.add_argument("--arm", choices=["control", "treatment", "both"], default="both",
                       help="Which arm to fill gaps for (default: both)")
    parser.add_argument("--dry-run", action="store_true",
                       help="Use mock responses (no API calls)")
    parser.add_argument("--key-offset", "-k", type=int, default=0,
                       help="Starting offset in key pool")
    parser.add_argument("--skip-exit-survey", action="store_true",
                       help="Skip exit survey (debugging only)")
    parser.add_argument("--skip", type=str, default="",
                       help="Comma-separated list of ships to skip (e.g. 'gpt-5,o3-mini')")

    args = parser.parse_args()

    # Parse skip list
    skip_ships = set(s.strip() for s in args.skip.split(",") if s.strip())

    # Set dry-run mode in main script
    import run020B as main_script
    main_script.DRY_RUN = args.dry_run

    # Load environment
    env_path = ARMADA_DIR / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f"Loaded API keys from: {env_path}")

    # Initialize key pool
    key_pool = KeyPool(start_offset=args.key_offset)

    # Show current gaps
    arm_filter = None if args.arm == "both" else args.arm
    gaps = show_gaps(arm_filter=arm_filter)

    if not gaps:
        return

    # Filter out skipped ships
    if skip_ships:
        original_count = len(gaps)
        gaps = [g for g in gaps if g["ship"] not in skip_ships]
        skipped_count = original_count - len(gaps)
        if skipped_count > 0:
            print(f"\n[SKIP] Excluding {skipped_count} gaps for ships: {', '.join(sorted(skip_ships))}")
            print(f"[SKIP] {len(gaps)} gaps remaining after filtering")

    if not args.execute:
        print("\nTo fill gaps, run with --execute flag")
        return

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

        if fill_gap(gap, key_pool, args.skip_exit_survey):
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
    if arm_filter:
        remaining = [g for g in remaining if g["arm"] == arm_filter]
    if remaining:
        print(f"\n  Remaining gaps: {len(remaining)}")
    else:
        print("\n  IRON CLAD COMPLETE!")


if __name__ == "__main__":
    main()
