#!/usr/bin/env python3
"""
ESSENCE EXTRACTION - Phase 2 Driver (Double-Dip)
=================================================
Mine experiment ideas from model responses.

Double-dip means: we already ran experiments, now we're mining
the responses for ideas about FUTURE experiments.

USAGE:
------
py 2_run_double_dip.py                     # Run hub double-dip miner
py 2_run_double_dip.py --spoke 14          # Drive 14_CONSCIOUSNESS spoke
py 2_run_double_dip.py --aggregate         # Collect ideas from spokes

OUTPUT:
-------
Results go to: results/double_dip/
  - double_dip_ideas.json: Structured experiment ideas
  - double_dip_summary.md: Human-readable summary
"""

import argparse
import subprocess
import sys
from pathlib import Path
from datetime import datetime

# Paths
SCRIPT_DIR = Path(__file__).parent
HUB_DOUBLE_DIP = SCRIPT_DIR / "2_double_dip" / "run_double_dip_miner.py"
RESULTS_DIR = SCRIPT_DIR / "results" / "double_dip"

# Spoke locations
REPO_ROOT = SCRIPT_DIR.parent.parent
SPOKE_14 = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "14_CONSCIOUSNESS"


def run_hub_double_dip():
    """Run double-dip using hub's internal script."""
    print("\n[HUB] Running double-dip idea mining...")

    if not HUB_DOUBLE_DIP.exists():
        print(f"  [ERROR] Hub script not found: {HUB_DOUBLE_DIP}")
        return False

    cmd = [sys.executable, str(HUB_DOUBLE_DIP)]
    result = subprocess.run(cmd, cwd=str(SCRIPT_DIR))
    return result.returncode == 0


def run_spoke_double_dip(spoke_num: int):
    """Run double-dip at spoke with back-feed."""
    print(f"\n[SPOKE {spoke_num}] Running double-dip with back-feed...")

    spoke_scripts = {
        14: SPOKE_14 / "run_double_dip_miner.py",
    }

    script = spoke_scripts.get(spoke_num)
    if not script or not script.exists():
        print(f"  [SKIP] Spoke {spoke_num} double-dip script not found")
        return False

    cmd = [sys.executable, str(script), "--back-feed"]
    result = subprocess.run(cmd, cwd=str(script.parent))
    return result.returncode == 0


def aggregate_ideas():
    """Aggregate double-dip ideas from spokes."""
    print("\n[AGGREGATE] Collecting ideas from spokes...")

    spoke_outputs = [
        SPOKE_14 / "results" / "double_dip",
    ]

    total_ideas = 0
    for spoke_dir in spoke_outputs:
        if not spoke_dir.exists():
            continue

        ideas_file = spoke_dir / "double_dip_ideas.json"
        if ideas_file.exists():
            import json
            data = json.loads(ideas_file.read_text(encoding="utf-8"))
            count = len(data) if isinstance(data, list) else len(data.get("ideas", []))
            total_ideas += count
            print(f"  {spoke_dir.parent.name}: {count} ideas")

    print(f"\n  Total ideas: {total_ideas}")
    return total_ideas > 0


def main():
    parser = argparse.ArgumentParser(
        description="ESSENCE EXTRACTION - Phase 2: Double-Dip Idea Mining",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
What is Double-Dip?
  We already ran experiments (first dip).
  Now we mine those responses for ideas about future experiments (second dip).

Examples:
  py 2_run_double_dip.py              # Run hub miner
  py 2_run_double_dip.py --spoke 14   # Drive spoke 14
  py 2_run_double_dip.py --aggregate  # Collect spoke results
        """
    )
    parser.add_argument("--spoke", type=int, choices=[14],
                        help="Run specific spoke double-dip")
    parser.add_argument("--aggregate", action="store_true",
                        help="Aggregate ideas from spokes")

    args = parser.parse_args()

    print("="*60)
    print("ESSENCE EXTRACTION - PHASE 2: DOUBLE-DIP IDEA MINING")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("="*60)

    success = True

    if args.aggregate:
        success = aggregate_ideas()
    elif args.spoke:
        success = run_spoke_double_dip(args.spoke)
    else:
        success = run_hub_double_dip()

    print("\n" + "="*60)
    status = "COMPLETE" if success else "FAILED"
    print(f"Phase 2: {status}")
    print("="*60)

    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
