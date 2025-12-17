#!/usr/bin/env python3
"""
Build Validity Index for Run 018 Results
=========================================
Scans all result files and creates an index tracking which models have valid
data within each file. This handles the case where batch runs contain a mix
of valid and corrupted model data.

Output: VALIDITY_INDEX.json

Usage:
    py build_validity_index.py           # Build index
    py build_validity_index.py --report  # Show summary report
    py build_validity_index.py --mark    # Mark invalid entries in source files
"""

import json
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any

RESULTS_DIR = Path(__file__).parent
INDEX_FILE = RESULTS_DIR / "VALIDITY_INDEX.json"

# Thresholds for validity
MIN_VALID_DRIFT = 0.001  # Anything below this is likely a failed API call
MAX_VALID_DRIFT = 5.0    # Anything above this is corrupted embedding data


def analyze_file(filepath: Path) -> Dict[str, Any]:
    """Analyze a single result file for model validity."""
    result = {
        "filename": filepath.name,
        "valid_models": [],
        "invalid_models": [],
        "issues": [],
        "total_subjects": 0,
        "valid_count": 0,
        "invalid_count": 0
    }

    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except Exception as e:
        result["issues"].append(f"Failed to load: {e}")
        return result

    # Check for subjects array (architecture experiment format)
    if 'subjects' in data:
        subjects = data['subjects']
        result["total_subjects"] = len(subjects)

        for subject in subjects:
            provider = subject.get('provider', 'unknown')
            peak_drift = subject.get('peak_drift', 0)

            # Check validity
            if peak_drift < MIN_VALID_DRIFT:
                result["invalid_models"].append({
                    "model": provider,
                    "reason": f"peak_drift={peak_drift} (below threshold, likely API failure)"
                })
                result["invalid_count"] += 1
            elif peak_drift > MAX_VALID_DRIFT:
                result["invalid_models"].append({
                    "model": provider,
                    "reason": f"peak_drift={peak_drift} (above threshold, corrupted embedding)"
                })
                result["invalid_count"] += 1
            else:
                result["valid_models"].append(provider)
                result["valid_count"] += 1

    # Check for sessions array (older format)
    elif 'sessions' in data and isinstance(data['sessions'], list):
        sessions = data['sessions']
        result["total_subjects"] = len(sessions)

        for session in sessions:
            model = session.get('model', data.get('model', 'unknown'))
            probes = session.get('probes', [])

            if not probes:
                result["invalid_models"].append({
                    "model": model,
                    "reason": "No probe data"
                })
                result["invalid_count"] += 1
                continue

            # Check drift values
            drifts = [p.get('drift', 0) for p in probes]
            max_drift = max(drifts) if drifts else 0

            if max_drift < MIN_VALID_DRIFT:
                result["invalid_models"].append({
                    "model": model,
                    "reason": f"max_drift={max_drift} (below threshold)"
                })
                result["invalid_count"] += 1
            elif max_drift > MAX_VALID_DRIFT:
                result["invalid_models"].append({
                    "model": model,
                    "reason": f"max_drift={max_drift} (corrupted)"
                })
                result["invalid_count"] += 1
            else:
                result["valid_models"].append(model)
                result["valid_count"] += 1

    # Single-model format (threshold/nyquist/gravity from manifest copies)
    elif 'model' in data:
        model = data.get('model', 'unknown')
        drift = data.get('drift', data.get('final_drift', 0))
        result["total_subjects"] = 1

        if drift < MIN_VALID_DRIFT:
            result["invalid_models"].append({
                "model": model,
                "reason": f"drift={drift} (below threshold)"
            })
            result["invalid_count"] = 1
        elif drift > MAX_VALID_DRIFT:
            result["invalid_models"].append({
                "model": model,
                "reason": f"drift={drift} (corrupted)"
            })
            result["invalid_count"] = 1
        else:
            result["valid_models"].append(model)
            result["valid_count"] = 1

    return result


def build_index() -> Dict[str, Any]:
    """Build the complete validity index."""
    index = {
        "generated": datetime.now().isoformat(),
        "thresholds": {
            "min_valid_drift": MIN_VALID_DRIFT,
            "max_valid_drift": MAX_VALID_DRIFT
        },
        "summary": {
            "total_files": 0,
            "files_with_issues": 0,
            "total_valid_models": 0,
            "total_invalid_models": 0,
            "fully_valid_files": 0,
            "mixed_validity_files": 0,
            "fully_invalid_files": 0
        },
        "files": {}
    }

    # Scan all JSON files except those already marked corrupted
    json_files = sorted(RESULTS_DIR.glob("*.json"))

    for filepath in json_files:
        # Skip corrupted files and this index file
        if filepath.name.startswith('_CORRUPTED_'):
            continue
        if filepath.name == 'VALIDITY_INDEX.json':
            continue

        analysis = analyze_file(filepath)
        index["files"][filepath.name] = analysis
        index["summary"]["total_files"] += 1

        # Update summary stats
        if analysis["issues"]:
            index["summary"]["files_with_issues"] += 1

        index["summary"]["total_valid_models"] += analysis["valid_count"]
        index["summary"]["total_invalid_models"] += analysis["invalid_count"]

        # Categorize file
        if analysis["invalid_count"] == 0 and analysis["valid_count"] > 0:
            index["summary"]["fully_valid_files"] += 1
        elif analysis["valid_count"] == 0 and analysis["invalid_count"] > 0:
            index["summary"]["fully_invalid_files"] += 1
        elif analysis["valid_count"] > 0 and analysis["invalid_count"] > 0:
            index["summary"]["mixed_validity_files"] += 1

    return index


def print_report(index: Dict[str, Any]):
    """Print a human-readable report."""
    print("=" * 70)
    print("RUN 018 VALIDITY INDEX REPORT")
    print("=" * 70)
    print(f"Generated: {index['generated']}")
    print(f"Thresholds: {index['thresholds']['min_valid_drift']} < drift < {index['thresholds']['max_valid_drift']}")
    print()

    summary = index["summary"]
    print("SUMMARY:")
    print(f"  Total files scanned: {summary['total_files']}")
    print(f"  Fully valid files:   {summary['fully_valid_files']}")
    print(f"  Mixed validity:      {summary['mixed_validity_files']}")
    print(f"  Fully invalid:       {summary['fully_invalid_files']}")
    print(f"  Files with issues:   {summary['files_with_issues']}")
    print()
    print(f"  Total valid models:   {summary['total_valid_models']}")
    print(f"  Total invalid models: {summary['total_invalid_models']}")
    print()

    # Show mixed validity files (most interesting)
    if summary['mixed_validity_files'] > 0:
        print("MIXED VALIDITY FILES (contain both valid and invalid data):")
        print("-" * 70)
        for filename, analysis in index["files"].items():
            if analysis["valid_count"] > 0 and analysis["invalid_count"] > 0:
                print(f"\n  {filename}")
                print(f"    Valid: {analysis['valid_count']} | Invalid: {analysis['invalid_count']}")
                for inv in analysis["invalid_models"][:5]:  # Show first 5
                    print(f"      - {inv['model']}: {inv['reason']}")
                if len(analysis["invalid_models"]) > 5:
                    print(f"      ... and {len(analysis['invalid_models']) - 5} more")

    # Show fully invalid files
    if summary['fully_invalid_files'] > 0:
        print("\n\nFULLY INVALID FILES (should be marked _CORRUPTED_):")
        print("-" * 70)
        for filename, analysis in index["files"].items():
            if analysis["valid_count"] == 0 and analysis["invalid_count"] > 0:
                print(f"  {filename}")
                for inv in analysis["invalid_models"][:3]:
                    print(f"    - {inv['model']}: {inv['reason']}")


def mark_invalid_entries_in_files(index: Dict[str, Any], dry_run: bool = True) -> int:
    """
    Mark invalid entries directly in source JSON files by adding "_invalid": true field.

    This allows downstream scripts to skip invalid entries without needing the index.
    """
    marked_count = 0
    files_modified = 0

    for filename, analysis in index["files"].items():
        if not analysis["invalid_models"]:
            continue  # No invalid entries to mark

        filepath = RESULTS_DIR / filename
        if not filepath.exists():
            continue

        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)
        except Exception as e:
            print(f"Error reading {filename}: {e}")
            continue

        # Get set of invalid model names
        invalid_model_names = set(inv["model"] for inv in analysis["invalid_models"])

        modified = False

        # Mark invalid subjects
        if 'subjects' in data:
            for subject in data['subjects']:
                provider = subject.get('provider', 'unknown')
                if provider in invalid_model_names:
                    if not subject.get('_invalid'):
                        subject['_invalid'] = True
                        subject['_invalid_reason'] = "peak_drift out of valid range (API failure or corrupted)"
                        marked_count += 1
                        modified = True

        if modified:
            files_modified += 1
            if not dry_run:
                with open(filepath, 'w', encoding='utf-8') as f:
                    json.dump(data, f, indent=2)
                print(f"  Marked {filename}")

    return marked_count, files_modified


def main():
    parser = argparse.ArgumentParser(description="Build validity index for Run 018 results")
    parser.add_argument("--report", action="store_true", help="Show summary report")
    parser.add_argument("--mark", action="store_true", help="Mark invalid entries in source files")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be marked without modifying")
    args = parser.parse_args()

    print("Scanning result files...")
    index = build_index()

    # Save index
    with open(INDEX_FILE, 'w', encoding='utf-8') as f:
        json.dump(index, f, indent=2)
    print(f"Saved: {INDEX_FILE}")

    if args.report:
        print()
        print_report(index)
    elif args.mark:
        print("\nMarking invalid entries in source files...")
        if args.dry_run:
            print("(DRY RUN - no files will be modified)")
        marked, files_mod = mark_invalid_entries_in_files(index, dry_run=args.dry_run)
        print(f"\n{'Would mark' if args.dry_run else 'Marked'} {marked} entries in {files_mod} files")
    else:
        # Brief summary
        s = index["summary"]
        print(f"\nSummary: {s['total_files']} files, "
              f"{s['fully_valid_files']} valid, "
              f"{s['mixed_validity_files']} mixed, "
              f"{s['fully_invalid_files']} invalid")
        print(f"Models: {s['total_valid_models']} valid, {s['total_invalid_models']} invalid")
        print("\nRun with --report for detailed breakdown")
        print("Run with --mark to add _invalid flags to source files")


if __name__ == "__main__":
    main()
