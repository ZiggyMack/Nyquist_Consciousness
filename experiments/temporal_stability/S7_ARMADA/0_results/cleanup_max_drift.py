#!/usr/bin/env python3
"""
Remove duplicate 'max_drift' fields from JSON files.

Standardizes on 'peak_drift' only.
Removes 'max_drift' fields which are duplicates or unused (0.0).

Usage:
    python cleanup_max_drift.py --dry-run    # Preview changes
    python cleanup_max_drift.py --execute    # Make changes
"""

import json
import argparse
from pathlib import Path
from typing import Dict, Any, Tuple


def remove_max_drift_recursive(obj: Any) -> Tuple[Any, int]:
    """
    Recursively remove 'max_drift' fields from a JSON object.
    Returns (modified_object, count_of_removals).
    """
    removed = 0

    if isinstance(obj, dict):
        new_dict = {}
        for key, value in obj.items():
            if key == 'max_drift':
                removed += 1
                # Skip this key entirely
                continue
            new_value, sub_removed = remove_max_drift_recursive(value)
            new_dict[key] = new_value
            removed += sub_removed
        return new_dict, removed

    elif isinstance(obj, list):
        new_list = []
        for item in obj:
            new_item, sub_removed = remove_max_drift_recursive(item)
            new_list.append(new_item)
            removed += sub_removed
        return new_list, removed

    else:
        return obj, 0


def process_file(file_path: Path, dry_run: bool) -> Tuple[bool, int]:
    """
    Process a single JSON file.
    Returns (was_modified, count_of_removals).
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            data = json.load(f)

        cleaned_data, removed_count = remove_max_drift_recursive(data)

        if removed_count > 0:
            if not dry_run:
                with open(file_path, 'w', encoding='utf-8') as f:
                    json.dump(cleaned_data, f, indent=2, ensure_ascii=False)
            return True, removed_count

        return False, 0

    except Exception as e:
        print(f"  ERROR processing {file_path.name}: {e}")
        return False, 0


def main():
    parser = argparse.ArgumentParser(description='Remove max_drift fields from JSON files')
    parser.add_argument('--dry-run', action='store_true', help='Preview changes without modifying files')
    parser.add_argument('--execute', action='store_true', help='Actually modify the files')
    args = parser.parse_args()

    if not args.dry_run and not args.execute:
        print("ERROR: Must specify --dry-run or --execute")
        return 1

    dry_run = args.dry_run

    print("=" * 60)
    print("MAX_DRIFT CLEANUP - Standardizing on peak_drift")
    print("=" * 60)
    print(f"Mode: {'DRY RUN' if dry_run else 'EXECUTE'}")
    print()

    # Directories to scan
    base_dir = Path(__file__).parent
    scan_dirs = [
        base_dir / "manifests",
        base_dir / "runs",
        base_dir / "temporal_logs",
        base_dir / "analysis",
        base_dir.parent / "9_STABILITY_CRITERIA" / "results",
    ]

    total_files = 0
    modified_files = 0
    total_removals = 0

    for scan_dir in scan_dirs:
        if not scan_dir.exists():
            continue

        print(f"Scanning: {scan_dir}")

        # Include legacy subdirs
        json_files = list(scan_dir.glob("*.json")) + list(scan_dir.glob("**/*.json"))
        # Remove duplicates
        json_files = list(set(json_files))

        for json_file in sorted(json_files):
            total_files += 1
            was_modified, removed = process_file(json_file, dry_run)

            if was_modified:
                modified_files += 1
                total_removals += removed
                action = "Would modify" if dry_run else "Modified"
                print(f"  {action}: {json_file.name} ({removed} removals)")

    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Files scanned: {total_files}")
    print(f"Files {'to modify' if dry_run else 'modified'}: {modified_files}")
    print(f"Total max_drift fields {'to remove' if dry_run else 'removed'}: {total_removals}")

    if dry_run:
        print()
        print("This was a DRY RUN. Run with --execute to make changes.")

    return 0


if __name__ == '__main__':
    exit(main())
