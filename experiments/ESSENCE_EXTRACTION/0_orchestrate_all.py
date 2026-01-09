#!/usr/bin/env python3
"""
ESSENCE EXTRACTION - Master Orchestrator
==========================================
Run all extraction phases from the hub.

This is the SSOT (Single Source of Truth) for all extraction efforts.
All extraction flows through or back-feeds to this directory.

USAGE:
------
py 0_orchestrate_all.py                  # Run all phases
py 0_orchestrate_all.py --phase 1        # Run only extraction
py 0_orchestrate_all.py --phase 2        # Run only double-dip
py 0_orchestrate_all.py --phase 3        # Run only triple-dip
py 0_orchestrate_all.py --phase 4        # Run only calibration update
py 0_orchestrate_all.py --status         # Show current status

ARCHITECTURE:
-------------
This hub orchestrates spokes at:
  - experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS/
  - experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/
  - experiments/temporal_stability/S7_ARMADA/15_IRON_CLAD_FOUNDATION/

Raw data stays at spokes. Derived outputs (essences, ideas, insights) live here.
"""

import argparse
import subprocess
import sys
from pathlib import Path
from datetime import datetime

# Paths
SCRIPT_DIR = Path(__file__).parent
EXTRACTION_SCRIPT = SCRIPT_DIR / "1_extraction" / "run_essence_extraction.py"
DOUBLE_DIP_SCRIPT = SCRIPT_DIR / "2_double_dip" / "run_double_dip_miner.py"
TRIPLE_DIP_SCRIPT = SCRIPT_DIR / "3_triple_dip" / "run_triple_dip_harvester.py"
CALIBRATION_SCRIPT = SCRIPT_DIR / "4_calibration" / "update_calibration_from_essence.py"
RESULTS_DIR = SCRIPT_DIR / "results"


def run_phase(phase_num: int, script_path: Path, phase_name: str, extra_args: list = None):
    """Run a single phase."""
    print(f"\n{'='*60}")
    print(f"PHASE {phase_num}: {phase_name}")
    print(f"{'='*60}")

    if not script_path.exists():
        print(f"  [SKIP] Script not found: {script_path.name}")
        return False

    cmd = [sys.executable, str(script_path)]
    if extra_args:
        cmd.extend(extra_args)

    print(f"  Running: {script_path.name}")
    try:
        result = subprocess.run(cmd, cwd=str(SCRIPT_DIR), capture_output=False)
        if result.returncode == 0:
            print(f"  [OK] Phase {phase_num} complete")
            return True
        else:
            print(f"  [FAIL] Phase {phase_num} returned {result.returncode}")
            return False
    except Exception as e:
        print(f"  [ERROR] {e}")
        return False


def show_status():
    """Show current extraction status."""
    print("\n" + "="*60)
    print("ESSENCE EXTRACTION HUB STATUS")
    print("="*60)

    # Check scripts
    scripts = [
        ("1_extraction", EXTRACTION_SCRIPT),
        ("2_double_dip", DOUBLE_DIP_SCRIPT),
        ("3_triple_dip", TRIPLE_DIP_SCRIPT),
        ("4_calibration", CALIBRATION_SCRIPT),
    ]

    print("\n## Phase Scripts:")
    for name, path in scripts:
        status = "OK" if path.exists() else "MISSING"
        print(f"  {name}: [{status}] {path.name}")

    # Check results
    print("\n## Results:")
    result_dirs = [
        ("model_essences", RESULTS_DIR / "model_essences"),
        ("double_dip", RESULTS_DIR / "double_dip"),
        ("triple_dip", RESULTS_DIR / "triple_dip"),
        ("calibration_updates", RESULTS_DIR / "calibration_updates"),
    ]

    for name, path in result_dirs:
        if path.exists():
            # Count files
            files = list(path.rglob("*"))
            file_count = len([f for f in files if f.is_file()])
            print(f"  {name}: {file_count} files")
        else:
            print(f"  {name}: [NOT CREATED]")

    print("\n## Hub-Spoke Architecture:")
    print("  Hub: experiments/ESSENCE_EXTRACTION/ (you are here)")
    print("  Spokes:")
    print("    - 14_CONSCIOUSNESS/ (gold_rush, diamond_rush)")
    print("    - 17_JADE_LATTICE/ (jade_*.json)")
    print("    - 15_IRON_CLAD_FOUNDATION/ (S7_run_*.json)")


def main():
    parser = argparse.ArgumentParser(
        description="ESSENCE EXTRACTION - Master Orchestrator",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Hub-Spoke Architecture:
  This hub orchestrates extraction across multiple spokes.
  Raw data stays at spokes; derived outputs aggregate here.

Examples:
  py 0_orchestrate_all.py              # Run all phases
  py 0_orchestrate_all.py --phase 1    # Extract model essences only
  py 0_orchestrate_all.py --status     # Show current status
        """
    )
    parser.add_argument("--phase", type=int, choices=[1, 2, 3, 4],
                        help="Run specific phase only")
    parser.add_argument("--status", action="store_true",
                        help="Show current status")
    parser.add_argument("--source", type=str, default="all",
                        help="Data source for extraction (default: all)")

    args = parser.parse_args()

    if args.status:
        show_status()
        return 0

    print("="*60)
    print("ESSENCE EXTRACTION - MASTER ORCHESTRATOR")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("="*60)
    print("\nThis is the SSOT hub. All extraction flows through here.")

    results = {}

    # Phase 1: Extraction
    if args.phase is None or args.phase == 1:
        results[1] = run_phase(1, EXTRACTION_SCRIPT, "Model Essence Extraction",
                               ["--source", args.source])

    # Phase 2: Double-dip
    if args.phase is None or args.phase == 2:
        results[2] = run_phase(2, DOUBLE_DIP_SCRIPT, "Double-Dip Idea Mining")

    # Phase 3: Triple-dip
    if args.phase is None or args.phase == 3:
        results[3] = run_phase(3, TRIPLE_DIP_SCRIPT, "Triple-Dip Exit Survey Harvest")

    # Phase 4: Calibration
    if args.phase is None or args.phase == 4:
        results[4] = run_phase(4, CALIBRATION_SCRIPT, "Calibration Update Generation")

    # Summary
    print("\n" + "="*60)
    print("ORCHESTRATION COMPLETE")
    print("="*60)

    for phase, success in results.items():
        status = "OK" if success else "FAILED/SKIPPED"
        print(f"  Phase {phase}: {status}")

    print(f"\nCompleted: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

    # Return non-zero if any phase failed
    return 0 if all(results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
