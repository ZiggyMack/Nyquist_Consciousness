"""
S7 RUN 020A: GAP FILLER
========================
Fills remaining gaps to reach IRON CLAD status (N=3 per provider).

Uses the same experiment logic as run020A.py but:
- Only runs experiments that are below target N
- Appends to S7_run_020A_CURRENT.json incrementally
- Updates STATUS_SUMMARY_020A.txt after each result

Usage:
  py run020a_fill_gaps.py                    # Show gaps, don't run
  py run020a_fill_gaps.py --execute          # Fill all gaps
  py run020a_fill_gaps.py --execute --max 5  # Fill at most 5 gaps
  py run020a_fill_gaps.py --dry-run          # Test mode (no API calls)

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

from run020A import (
    # Core functions
    load_or_create_results,
    save_incremental,
    update_status_summary,
    detect_gaps,
    append_result,
    load_i_am_file,
    KeyPool,
    KEY_POOL,
    # Experiment runner
    run_tribunal,
    run_exit_survey,
    # Constants
    RESULTS_FILE,
    STATUS_FILE,
    ARMADA_DIR,
    PROVIDER_FLAGSHIP_FLEET,
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
    print(f"RUN 020A GAPS ({len(gaps)} remaining)")
    print("=" * 60)

    total_runs_needed = 0
    for gap in sorted(gaps, key=lambda x: -x["need"]):
        print(f"  {gap['ship']} ({gap['provider']}): {gap['have']}/3 (need {gap['need']})")
        total_runs_needed += gap["need"]

    print(f"\n" + "-" * 60)
    print(f"TOTAL RUNS NEEDED: {total_runs_needed}")
    print("=" * 60)

    return gaps


def fill_gap(gap: dict, i_am_content: str, key_pool, skip_exit_survey: bool = False) -> bool:
    """
    Fill a single gap by running the tribunal experiment once.
    Returns True if successful.
    """
    import run020A as main_script
    main_script.KEY_POOL = key_pool

    ship = gap["ship"]
    provider = gap["provider"]

    print(f"\n>>> FILLING GAP: {ship} ({provider}) <<<")

    try:
        # Run tribunal session
        result = run_tribunal(subject_provider=ship)

        if result is None:
            print(f"  [ERROR] Session returned None")
            return False

        # Run exit survey unless skipped
        exit_survey = None
        if not skip_exit_survey:
            # Reconstruct messages from session
            try:
                witness_messages = result.get("conversation_log", [])
                if witness_messages:
                    exit_survey = run_exit_survey(
                        conversation_history=witness_messages,
                        subject_provider=ship,
                        subject_id=result.get("session_id", f"gap_{ship}"),
                    )
            except Exception as e:
                print(f"  [WARN] Exit survey failed: {e}")

        # Prepare result for storage
        result_dict = result if isinstance(result, dict) else asdict(result)
        result_dict["provider"] = provider
        result_dict["ship"] = ship
        if exit_survey:
            result_dict["exit_survey"] = exit_survey

        # Append to results
        append_result(result_dict)

        print(f"  [SUCCESS] {ship}/{provider} completed")
        return True

    except Exception as e:
        print(f"  [FAILED] {ship}/{provider}: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Fill gaps in Run 020A IRON CLAD coverage"
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
    parser.add_argument("--skip-exit-survey", action="store_true",
                       help="Skip exit survey (debugging only)")

    args = parser.parse_args()

    # Set dry-run mode in main script
    import run020A as main_script
    main_script.DRY_RUN = args.dry_run

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

        if fill_gap(gap, i_am_content, key_pool, args.skip_exit_survey):
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
