#!/usr/bin/env python3
"""
ESSENCE EXTRACTION - Phase 4: Sync Results
============================================
Synchronize results from spokes to hub.

This script pulls derived outputs from spoke directories
and aggregates them into the hub's canonical results.

WHAT GETS SYNCED:
-----------------
- Model essences (from extraction)
- Double-dip ideas (experiment proposals)
- Triple-dip insights (exit survey patterns)
- Jade analysis summaries (A/B test results)

WHAT STAYS AT SPOKES:
---------------------
- Raw JSON files (S7_run_*.json)
- Session logs (jade_*.json)
- Original API responses

USAGE:
------
py 4_sync_results.py                       # Sync all spokes
py 4_sync_results.py --spoke 14            # Sync specific spoke
py 4_sync_results.py --dry-run             # Preview without copying
py 4_sync_results.py --status              # Show sync status
"""

import argparse
import shutil
import json
from pathlib import Path
from datetime import datetime

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
REPO_ROOT = SCRIPT_DIR.parent.parent

# Spoke definitions
SPOKES = {
    14: {
        "name": "14_CONSCIOUSNESS",
        "path": REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "14_CONSCIOUSNESS",
        "sync_dirs": ["model_essences", "double_dip", "triple_dip"],
    },
    17: {
        "name": "17_JADE_LATTICE",
        "path": REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "17_JADE_LATTICE",
        "sync_dirs": ["model_essences"],
        "sync_files": ["jade_analysis_summary.json"],
    },
    15: {
        "name": "15_IRON_CLAD_FOUNDATION",
        "path": REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "15_IRON_CLAD_FOUNDATION",
        "sync_dirs": ["model_essences"],
    },
}


def sync_spoke(spoke_num: int, dry_run: bool = False) -> dict:
    """Sync results from a single spoke to hub."""
    spoke = SPOKES.get(spoke_num)
    if not spoke:
        return {"error": f"Unknown spoke: {spoke_num}"}

    results = {
        "spoke": spoke["name"],
        "files_synced": 0,
        "dirs_synced": 0,
        "dry_run": dry_run,
    }

    spoke_results = spoke["path"] / "results"
    if not spoke_results.exists():
        results["warning"] = "No results directory"
        return results

    # Sync directories
    for dir_name in spoke.get("sync_dirs", []):
        src_dir = spoke_results / dir_name
        dst_dir = RESULTS_DIR / dir_name

        if not src_dir.exists():
            continue

        for src_file in src_dir.rglob("*"):
            if not src_file.is_file():
                continue

            # Preserve relative path structure
            rel_path = src_file.relative_to(src_dir)
            dst_file = dst_dir / rel_path

            if not dry_run:
                dst_file.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src_file, dst_file)

            results["files_synced"] += 1

        results["dirs_synced"] += 1

    # Sync individual files
    for file_name in spoke.get("sync_files", []):
        src_file = spoke_results / file_name
        if not src_file.exists():
            continue

        dst_file = RESULTS_DIR / file_name
        if not dry_run:
            shutil.copy2(src_file, dst_file)
        results["files_synced"] += 1

    return results


def show_status():
    """Show current sync status."""
    print("\n" + "="*60)
    print("ESSENCE EXTRACTION - SYNC STATUS")
    print("="*60)

    print("\n## Hub Results:")
    for subdir in sorted(RESULTS_DIR.iterdir()) if RESULTS_DIR.exists() else []:
        if subdir.is_dir():
            files = list(subdir.rglob("*"))
            file_count = len([f for f in files if f.is_file()])
            print(f"  {subdir.name}/: {file_count} files")

    print("\n## Spoke Status:")
    for num, spoke in sorted(SPOKES.items()):
        spoke_results = spoke["path"] / "results"
        exists = "OK" if spoke_results.exists() else "NO RESULTS"

        syncable = 0
        if spoke_results.exists():
            for dir_name in spoke.get("sync_dirs", []):
                src_dir = spoke_results / dir_name
                if src_dir.exists():
                    syncable += len([f for f in src_dir.rglob("*") if f.is_file()])
            for file_name in spoke.get("sync_files", []):
                if (spoke_results / file_name).exists():
                    syncable += 1

        print(f"  Spoke {num} ({spoke['name']}): [{exists}] {syncable} syncable files")


def main():
    parser = argparse.ArgumentParser(
        description="ESSENCE EXTRACTION - Sync Results from Spokes to Hub",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Hub-Spoke Architecture:
  Raw data stays at spokes.
  Derived outputs (essences, ideas, insights) sync to hub.

Examples:
  py 4_sync_results.py              # Sync all spokes
  py 4_sync_results.py --spoke 14   # Sync specific spoke
  py 4_sync_results.py --dry-run    # Preview without copying
  py 4_sync_results.py --status     # Show sync status
        """
    )
    parser.add_argument("--spoke", type=int, choices=list(SPOKES.keys()),
                        help="Sync specific spoke only")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without copying")
    parser.add_argument("--status", action="store_true",
                        help="Show current sync status")

    args = parser.parse_args()

    if args.status:
        show_status()
        return 0

    print("="*60)
    print("ESSENCE EXTRACTION - PHASE 4: SYNC RESULTS")
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    if args.dry_run:
        print("Mode: DRY RUN (no files will be copied)")
    print("="*60)

    # Determine which spokes to sync
    spokes_to_sync = [args.spoke] if args.spoke else list(SPOKES.keys())

    total_files = 0
    for spoke_num in spokes_to_sync:
        print(f"\n## Syncing Spoke {spoke_num}...")
        result = sync_spoke(spoke_num, args.dry_run)

        if "error" in result:
            print(f"  [ERROR] {result['error']}")
        elif "warning" in result:
            print(f"  [WARNING] {result['warning']}")
        else:
            print(f"  Dirs synced: {result['dirs_synced']}")
            print(f"  Files synced: {result['files_synced']}")
            total_files += result['files_synced']

    print("\n" + "="*60)
    print("SYNC COMPLETE")
    print(f"Total files: {total_files}")
    if args.dry_run:
        print("(Dry run - no files were actually copied)")
    print("="*60)

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
