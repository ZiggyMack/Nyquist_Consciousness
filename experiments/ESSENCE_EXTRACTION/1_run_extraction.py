#!/usr/bin/env python3
"""
ESSENCE EXTRACTION - Phase 1 Driver
====================================
Drive extraction from the hub or spokes.

This script can:
1. Run extraction directly using the hub's internal script
2. Call spoke scripts (14_CONSCIOUSNESS) with --back-feed flag
3. Aggregate results from multiple spokes

USAGE:
------
py 1_run_extraction.py                     # Run hub extraction (all sources)
py 1_run_extraction.py --source 018        # Specific data source
py 1_run_extraction.py --spoke 14          # Drive 14_CONSCIOUSNESS spoke
py 1_run_extraction.py --all-spokes        # Run all spokes with back-feed
py 1_run_extraction.py --aggregate         # Aggregate results from spokes

DATA SOURCES (configured in 1_extraction/config.py):
- 018: IRON CLAD original (2488 subjects)
- 020b: Conversation log format (248 subjects)
- 023: Probe sequence format (4505 experiments)
- 023d: Extended settling (750 experiments)
"""

import argparse
import subprocess
import sys
from pathlib import Path
from datetime import datetime

# Paths
SCRIPT_DIR = Path(__file__).parent
HUB_EXTRACTION = SCRIPT_DIR / "1_extraction" / "run_essence_extraction.py"
RESULTS_DIR = SCRIPT_DIR / "results" / "model_essences"

# Spoke locations (relative to repo root)
REPO_ROOT = SCRIPT_DIR.parent.parent
SPOKE_14 = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "14_CONSCIOUSNESS"
SPOKE_17 = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "17_JADE_LATTICE"
SPOKE_15 = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "15_IRON_CLAD_FOUNDATION"


def run_hub_extraction(source: str = "all"):
    """Run extraction using the hub's internal script."""
    print(f"\n[HUB] Running extraction for source: {source}")

    if not HUB_EXTRACTION.exists():
        print(f"  [ERROR] Hub script not found: {HUB_EXTRACTION}")
        return False

    cmd = [sys.executable, str(HUB_EXTRACTION), "--source", source]
    result = subprocess.run(cmd, cwd=str(SCRIPT_DIR))
    return result.returncode == 0


def run_spoke_extraction(spoke_num: int):
    """Run extraction at a spoke with --back-feed to hub."""
    print(f"\n[SPOKE {spoke_num}] Running extraction with back-feed...")

    spoke_map = {
        14: SPOKE_14 / "run_essence_extraction.py",
        17: SPOKE_17 / "run_jade_extraction.py",
        15: SPOKE_15 / "run_iron_extraction.py",
    }

    script = spoke_map.get(spoke_num)
    if not script or not script.exists():
        print(f"  [SKIP] Spoke {spoke_num} extraction script not found")
        print(f"         Expected: {script}")
        return False

    cmd = [sys.executable, str(script), "--back-feed"]
    result = subprocess.run(cmd, cwd=str(script.parent))
    return result.returncode == 0


def aggregate_spoke_results():
    """Aggregate results from all spokes into hub."""
    print("\n[AGGREGATE] Collecting results from spokes...")

    # Define where each spoke stores its essence outputs
    spoke_outputs = [
        SPOKE_14 / "results" / "model_essences",
        SPOKE_17 / "results" / "model_essences",
        SPOKE_15 / "results" / "model_essences",
    ]

    total_aggregated = 0
    for spoke_dir in spoke_outputs:
        if not spoke_dir.exists():
            continue

        print(f"  Checking: {spoke_dir}")
        # In a real implementation, this would copy/merge files
        # For now, just count what's there
        files = list(spoke_dir.rglob("*.json"))
        total_aggregated += len(files)
        print(f"    Found {len(files)} essence files")

    print(f"\n  Total aggregated: {total_aggregated} files")
    return total_aggregated > 0


def main():
    parser = argparse.ArgumentParser(
        description="ESSENCE EXTRACTION - Phase 1 Driver",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py 1_run_extraction.py                  # Run hub extraction
  py 1_run_extraction.py --source 018     # Specific source
  py 1_run_extraction.py --spoke 14       # Drive spoke 14
  py 1_run_extraction.py --aggregate      # Collect spoke results
        """
    )
    parser.add_argument("--source", type=str, default="all",
                        help="Data source (018, 020b, 023, 023d, or all)")
    parser.add_argument("--spoke", type=int, choices=[14, 15, 17],
                        help="Run specific spoke extraction")
    parser.add_argument("--all-spokes", action="store_true",
                        help="Run all spokes with back-feed")
    parser.add_argument("--aggregate", action="store_true",
                        help="Aggregate results from spokes")

    args = parser.parse_args()

    print("="*60)
    print("ESSENCE EXTRACTION - PHASE 1: MODEL ESSENCE EXTRACTION")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("="*60)

    success = True

    if args.aggregate:
        success = aggregate_spoke_results()
    elif args.spoke:
        success = run_spoke_extraction(args.spoke)
    elif args.all_spokes:
        for spoke in [14, 15, 17]:
            if not run_spoke_extraction(spoke):
                success = False
    else:
        success = run_hub_extraction(args.source)

    print("\n" + "="*60)
    status = "COMPLETE" if success else "FAILED"
    print(f"Phase 1: {status}")
    print("="*60)

    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
