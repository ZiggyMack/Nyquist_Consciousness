#!/usr/bin/env python3
"""
Fix Run 018 Manifest - Filter out corrupted threshold experiment data.

Problem: The threshold experiment computed drift values incorrectly (~79 instead of ~0.79).
         The gravity experiment has correct values.

Solution: Regenerate manifest using only valid data (drift values in reasonable range 0-5).

Usage:
    py fix_run018_manifest.py --dry-run     # Preview changes
    py fix_run018_manifest.py               # Apply fix
"""

import json
from pathlib import Path
from datetime import datetime
from collections import defaultdict
import argparse

ARMADA_DIR = Path(__file__).parent.parent
MANIFEST_DIR = ARMADA_DIR / "0_results" / "manifests"
ARCHIVE_DIR = Path("d:/Documents/Nyquist_Consciousness/.archive/Run_Data_Consolidated")

# Drift values above this threshold are clearly corrupted
MAX_VALID_DRIFT = 5.0


def load_manifest(run_number: str = "018") -> dict:
    """Load existing manifest."""
    manifest_path = MANIFEST_DIR / f"RUN_{run_number}_DRIFT_MANIFEST.json"
    if manifest_path.exists():
        with open(manifest_path, 'r', encoding='utf-8') as f:
            return json.load(f)
    return {}


def analyze_manifest(manifest: dict) -> dict:
    """Analyze manifest for data quality issues."""
    stats = {
        "experiments": {},
        "corrupted_entries": 0,
        "valid_entries": 0,
        "total_entries": 0
    }

    for exp_name, models in manifest.get("experiments", {}).items():
        exp_stats = {"valid": 0, "corrupted": 0, "models": {}}

        for model_name, entries in models.items():
            model_valid = 0
            model_corrupted = 0

            for entry in entries:
                drift = entry.get("drift")
                stats["total_entries"] += 1

                if drift is not None and drift <= MAX_VALID_DRIFT:
                    model_valid += 1
                    stats["valid_entries"] += 1
                else:
                    model_corrupted += 1
                    stats["corrupted_entries"] += 1

            exp_stats["models"][model_name] = {"valid": model_valid, "corrupted": model_corrupted}
            exp_stats["valid"] += model_valid
            exp_stats["corrupted"] += model_corrupted

        stats["experiments"][exp_name] = exp_stats

    return stats


def rebuild_clean_manifest(manifest: dict, run_number: str = "018") -> dict:
    """Rebuild manifest keeping only valid entries."""
    clean = {
        "run": run_number,
        "generated": manifest.get("generated", datetime.now().isoformat()),
        "last_updated": datetime.now().isoformat(),
        "data_quality_fix": "Filtered corrupted threshold data (drift > 5.0) on " + datetime.now().isoformat(),
        "summary": {
            "total_files": 0,
            "experiments": set(),
            "models_tested": set(),
            "files_processed": manifest.get("summary", {}).get("files_processed", []),
            "iron_clad_status": {}
        },
        "experiments": defaultdict(lambda: defaultdict(list))
    }

    entries_kept = 0
    entries_removed = 0

    for exp_name, models in manifest.get("experiments", {}).items():
        for model_name, entries in models.items():
            valid_entries = []

            for entry in entries:
                drift = entry.get("drift")

                # Keep entry if drift is valid (or None - missing data)
                if drift is None or drift <= MAX_VALID_DRIFT:
                    valid_entries.append(entry)
                    entries_kept += 1
                else:
                    entries_removed += 1

            if valid_entries:
                clean["experiments"][exp_name][model_name] = valid_entries
                clean["summary"]["experiments"].add(exp_name)
                clean["summary"]["models_tested"].add(model_name)

    # Convert sets to lists
    clean["summary"]["experiments"] = sorted(clean["summary"]["experiments"])
    clean["summary"]["models_tested"] = sorted(clean["summary"]["models_tested"])
    clean["summary"]["total_files"] = manifest.get("summary", {}).get("total_files", 0)
    clean["summary"]["entries_kept"] = entries_kept
    clean["summary"]["entries_removed"] = entries_removed

    # Calculate IRON CLAD status
    iron_clad = {}
    for exp, models in clean["experiments"].items():
        iron_clad[exp] = {}
        for model, runs in models.items():
            n = len(runs)
            iron_clad[exp][model] = {
                "n": n,
                "complete": n >= 3,
                "needed": max(0, 3 - n)
            }
    clean["summary"]["iron_clad_status"] = iron_clad

    # Convert defaultdicts to regular dicts
    clean["experiments"] = {k: dict(v) for k, v in clean["experiments"].items()}

    return clean


def main():
    parser = argparse.ArgumentParser(description="Fix Run 018 manifest by filtering corrupted data")
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without applying")
    parser.add_argument("--run", default="018", help="Run number (default: 018)")
    args = parser.parse_args()

    print("=" * 60)
    print("RUN 018 MANIFEST DATA QUALITY FIX")
    print("=" * 60)

    # Load existing manifest
    manifest = load_manifest(args.run)
    if not manifest:
        print("ERROR: No manifest found!")
        return 1

    # Analyze data quality
    print("\n--- DATA QUALITY ANALYSIS ---")
    stats = analyze_manifest(manifest)

    print(f"Total entries: {stats['total_entries']}")
    print(f"Valid entries (drift <= {MAX_VALID_DRIFT}): {stats['valid_entries']}")
    print(f"Corrupted entries (drift > {MAX_VALID_DRIFT}): {stats['corrupted_entries']}")

    print("\n--- BY EXPERIMENT ---")
    for exp_name, exp_stats in stats["experiments"].items():
        status = "CORRUPTED" if exp_stats["corrupted"] > exp_stats["valid"] else "OK"
        print(f"  {exp_name}: {exp_stats['valid']} valid, {exp_stats['corrupted']} corrupted [{status}]")

    if stats['corrupted_entries'] == 0:
        print("\nNo corrupted entries found - manifest is clean!")
        return 0

    # Rebuild clean manifest
    print("\n--- REBUILDING MANIFEST ---")
    clean_manifest = rebuild_clean_manifest(manifest, args.run)

    print(f"Entries kept: {clean_manifest['summary']['entries_kept']}")
    print(f"Entries removed: {clean_manifest['summary']['entries_removed']}")
    print(f"Experiments remaining: {clean_manifest['summary']['experiments']}")
    print(f"Models remaining: {len(clean_manifest['summary']['models_tested'])}")

    if args.dry_run:
        print("\n[DRY RUN] - No changes made")
        print(f"Would save to: {MANIFEST_DIR / f'RUN_{args.run}_DRIFT_MANIFEST.json'}")
    else:
        # Backup original
        backup_path = MANIFEST_DIR / f"RUN_{args.run}_DRIFT_MANIFEST.backup.json"
        with open(backup_path, 'w', encoding='utf-8') as f:
            json.dump(manifest, f, indent=2)
        print(f"\nBackup saved to: {backup_path}")

        # Save clean manifest
        output_path = MANIFEST_DIR / f"RUN_{args.run}_DRIFT_MANIFEST.json"
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(clean_manifest, f, indent=2)
        print(f"Clean manifest saved to: {output_path}")

    print("\n" + "=" * 60)
    print("FIX COMPLETE")
    print("=" * 60)

    return 0


if __name__ == "__main__":
    exit(main())
