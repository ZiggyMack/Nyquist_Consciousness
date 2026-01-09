#!/usr/bin/env python3
"""
ESSENCE EXTRACTION - Phase 3 Driver (Triple-Dip)
=================================================
Harvest insights from exit survey responses.

Triple-dip means: we ran experiments (1), mined for ideas (2),
now we're harvesting meta-insights from exit surveys (3).

Exit surveys ask models about their experience during the experiment.
This reveals self-awareness patterns and recovery strategies.

USAGE:
------
py 3_run_triple_dip.py                     # Run hub triple-dip harvester
py 3_run_triple_dip.py --spoke 14          # Drive 14_CONSCIOUSNESS spoke
py 3_run_triple_dip.py --aggregate         # Collect insights from spokes

OUTPUT:
-------
Results go to: results/triple_dip/
  - triple_dip_insights.json: Structured exit survey insights
  - triple_dip_summary.md: Human-readable summary
  - provider_patterns.json: Recovery patterns by provider
"""

import argparse
import subprocess
import sys
from pathlib import Path
from datetime import datetime

# Paths
SCRIPT_DIR = Path(__file__).parent
HUB_TRIPLE_DIP = SCRIPT_DIR / "3_triple_dip" / "run_triple_dip_harvester.py"
RESULTS_DIR = SCRIPT_DIR / "results" / "triple_dip"

# Spoke locations
REPO_ROOT = SCRIPT_DIR.parent.parent
SPOKE_14 = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "14_CONSCIOUSNESS"


def run_hub_triple_dip():
    """Run triple-dip using hub's internal script."""
    print("\n[HUB] Running triple-dip insight harvesting...")

    if not HUB_TRIPLE_DIP.exists():
        print(f"  [ERROR] Hub script not found: {HUB_TRIPLE_DIP}")
        return False

    cmd = [sys.executable, str(HUB_TRIPLE_DIP)]
    result = subprocess.run(cmd, cwd=str(SCRIPT_DIR))
    return result.returncode == 0


def run_spoke_triple_dip(spoke_num: int):
    """Run triple-dip at spoke with back-feed."""
    print(f"\n[SPOKE {spoke_num}] Running triple-dip with back-feed...")

    spoke_scripts = {
        14: SPOKE_14 / "run_triple_dip_harvester.py",
    }

    script = spoke_scripts.get(spoke_num)
    if not script or not script.exists():
        print(f"  [SKIP] Spoke {spoke_num} triple-dip script not found")
        return False

    cmd = [sys.executable, str(script), "--back-feed"]
    result = subprocess.run(cmd, cwd=str(script.parent))
    return result.returncode == 0


def aggregate_insights():
    """Aggregate triple-dip insights from spokes."""
    print("\n[AGGREGATE] Collecting insights from spokes...")

    spoke_outputs = [
        SPOKE_14 / "results" / "triple_dip",
    ]

    total_insights = 0
    for spoke_dir in spoke_outputs:
        if not spoke_dir.exists():
            continue

        insights_file = spoke_dir / "triple_dip_insights.json"
        if insights_file.exists():
            import json
            data = json.loads(insights_file.read_text(encoding="utf-8"))
            count = len(data) if isinstance(data, list) else len(data.get("insights", []))
            total_insights += count
            print(f"  {spoke_dir.parent.name}: {count} insights")

    print(f"\n  Total insights: {total_insights}")
    return total_insights > 0


def main():
    parser = argparse.ArgumentParser(
        description="ESSENCE EXTRACTION - Phase 3: Triple-Dip Insight Harvesting",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
What is Triple-Dip?
  1st dip: Run experiments
  2nd dip: Mine responses for future experiment ideas
  3rd dip: Harvest exit survey meta-insights

Exit surveys reveal:
  - Model self-awareness of drift
  - Recovery strategies used
  - Authenticity anchors referenced
  - Provider-specific behavioral patterns

Examples:
  py 3_run_triple_dip.py              # Run hub harvester
  py 3_run_triple_dip.py --spoke 14   # Drive spoke 14
  py 3_run_triple_dip.py --aggregate  # Collect spoke results
        """
    )
    parser.add_argument("--spoke", type=int, choices=[14],
                        help="Run specific spoke triple-dip")
    parser.add_argument("--aggregate", action="store_true",
                        help="Aggregate insights from spokes")

    args = parser.parse_args()

    print("="*60)
    print("ESSENCE EXTRACTION - PHASE 3: TRIPLE-DIP INSIGHT HARVEST")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("="*60)

    success = True

    if args.aggregate:
        success = aggregate_insights()
    elif args.spoke:
        success = run_spoke_triple_dip(args.spoke)
    else:
        success = run_hub_triple_dip()

    print("\n" + "="*60)
    status = "COMPLETE" if success else "FAILED"
    print(f"Phase 3: {status}")
    print("="*60)

    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
