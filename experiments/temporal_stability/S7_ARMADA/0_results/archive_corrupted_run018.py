#!/usr/bin/env python3
"""
Archive Corrupted Run 018 Data Files

Identifies files with drift > 5.0 (corrupted by embedding cache pollution)
and moves them to .archive/Run018_Corrupted/corrupted/

Root cause: During dry-run mode, random embeddings were cached:
    if DRY_RUN:
        fake_emb = list(np.random.randn(3072))
The Euclidean distance between two random 3072-dim vectors = sqrt(2*3072) = 78.4

Usage:
    py archive_corrupted_run018.py --dry-run    # Preview what would be moved
    py archive_corrupted_run018.py --execute    # Actually move the files
"""

import json
import shutil
import argparse
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from typing import Dict, List, Tuple

# Constants
MAX_VALID_DRIFT = 5.0
REPO_ROOT = Path("d:/Documents/Nyquist_Consciousness")
ARCHIVE_DIR = REPO_ROOT / ".archive" / "Run018_Corrupted" / "corrupted"
TEMPORAL_LOGS_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA" / "0_results" / "temporal_logs" / "run018"
RESULTS_DIR = REPO_ROOT / ".archive" / "Run_Data_Consolidated"


def is_corrupted(file_path: Path) -> Tuple[bool, float]:
    """
    Check if file contains corrupted drift values.
    Returns (is_corrupted, max_drift_found)
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            data = json.load(f)

        max_drift = 0.0

        # Check top-level drift fields
        for key in ['max_drift_achieved', 'baseline_to_final_drift', 'peak_drift',
                    'max_drift', 'final_drift']:
            if key in data:
                drift = data[key]
                if isinstance(drift, (int, float)):
                    max_drift = max(max_drift, drift)

        # Check probe sequences at top level
        for probe in data.get('probe_sequence', []):
            if isinstance(probe, dict) and 'drift' in probe:
                drift = probe['drift']
                if isinstance(drift, (int, float)):
                    max_drift = max(max_drift, drift)

        # Check subjects array (Run 018 format)
        for subject in data.get('subjects', []):
            if isinstance(subject, dict):
                if 'peak_drift' in subject:
                    drift = subject['peak_drift']
                    if isinstance(drift, (int, float)):
                        max_drift = max(max_drift, drift)

                # Check probe sequence within subject
                for probe in subject.get('probe_sequence', []):
                    if isinstance(probe, dict) and 'drift' in probe:
                        drift = probe['drift']
                        if isinstance(drift, (int, float)):
                            max_drift = max(max_drift, drift)

        # Check sessions array (older format)
        for session in data.get('sessions', []):
            if isinstance(session, dict):
                for key in ['peak_drift', 'max_drift', 'final_drift']:
                    if key in session:
                        drift = session[key]
                        if isinstance(drift, (int, float)):
                            max_drift = max(max_drift, drift)

        return (max_drift > MAX_VALID_DRIFT, max_drift)

    except Exception as e:
        print(f"  Warning: Could not parse {file_path.name}: {e}")
        return (False, 0.0)


def get_experiment_type(filename: str) -> str:
    """Extract experiment type from filename."""
    filename_lower = filename.lower()
    if '_threshold_' in filename_lower or 'threshold' in filename_lower:
        return 'threshold'
    if '_architecture_' in filename_lower or 'architecture' in filename_lower:
        return 'architecture'
    if '_nyquist_' in filename_lower or 'nyquist' in filename_lower:
        return 'nyquist'
    if '_gravity_' in filename_lower or 'gravity' in filename_lower:
        return 'gravity'
    return 'unknown'


def generate_corruption_report(moved: Dict[str, List[Tuple[str, float]]],
                               dry_run: bool) -> str:
    """Generate markdown report of what was/would be moved."""

    action = "WOULD BE MOVED" if dry_run else "MOVED"

    report = f"""# Run 018 Corruption Archive Report

**Generated:** {datetime.now().isoformat()}
**Action:** {action}
**Archive Location:** {ARCHIVE_DIR}

---

## Root Cause

During Run 018 experiments, the embedding cache got polluted with random vectors
from dry-run mode:

```python
if DRY_RUN:
    fake_emb = list(np.random.randn(3072))  # Random 3072-dim vector
    _embedding_cache[cache_key] = fake_emb
```

The Euclidean distance between two random 3072-dim vectors:
- Expected: sqrt(2 * 3072) = **78.4**
- Observed in corrupted files: **~78-79**

Valid drift values should be < 5.0 (typically 0.1 - 2.0)

---

## Files {action}

"""

    total_files = 0
    for category, files in sorted(moved.items()):
        if not files:
            continue
        report += f"### {category.replace('_', ' ').title()} ({len(files)} files)\n\n"
        report += "| Filename | Max Drift |\n"
        report += "|----------|----------|\n"
        for filename, max_drift in sorted(files, key=lambda x: -x[1]):
            report += f"| {filename} | {max_drift:.2f} |\n"
            total_files += 1
        report += "\n"

    report += f"""---

## Summary

| Category | Files |
|----------|-------|
"""
    for category, files in sorted(moved.items()):
        report += f"| {category.replace('_', ' ').title()} | {len(files)} |\n"

    report += f"| **TOTAL** | **{total_files}** |\n"

    report += f"""
---

## Recovery Actions Required

1. Re-run corrupted model-experiment combinations
2. Update RUN_018_DRIFT_MANIFEST.json to exclude archived files
3. Regenerate visualizations from clean data only
4. Update WHITE-PAPER IRON CLAD status

See: `S7_ARMADA/0_results/RERUN_QUEUE.md` for tracking
"""

    return report


def main():
    parser = argparse.ArgumentParser(
        description='Archive corrupted Run 018 data files'
    )
    parser.add_argument('--dry-run', action='store_true',
                        help='Preview what would be moved without actually moving')
    parser.add_argument('--execute', action='store_true',
                        help='Actually move the files')
    args = parser.parse_args()

    if not args.dry_run and not args.execute:
        print("ERROR: Must specify either --dry-run or --execute")
        print("  --dry-run : Preview what would be moved")
        print("  --execute : Actually move the files")
        return 1

    dry_run = args.dry_run

    print("=" * 60)
    print("RUN 018 CORRUPTED DATA ARCHIVER")
    print("=" * 60)
    print(f"Mode: {'DRY RUN (preview only)' if dry_run else 'EXECUTE (will move files)'}")
    print(f"Archive destination: {ARCHIVE_DIR}")
    print(f"Max valid drift: {MAX_VALID_DRIFT}")
    print()

    # Create archive structure (even in dry-run to show what would be created)
    if not dry_run:
        for exp in ['threshold', 'architecture', 'nyquist', 'gravity', 'unknown']:
            (ARCHIVE_DIR / 'temporal_logs' / exp).mkdir(parents=True, exist_ok=True)
        (ARCHIVE_DIR / 'results').mkdir(parents=True, exist_ok=True)

    moved = defaultdict(list)

    # Process temporal logs
    print(f"Scanning temporal logs: {TEMPORAL_LOGS_DIR}")
    if TEMPORAL_LOGS_DIR.exists():
        json_files = list(TEMPORAL_LOGS_DIR.glob('*.json'))
        print(f"  Found {len(json_files)} JSON files")

        for f in json_files:
            corrupted, max_drift = is_corrupted(f)
            if corrupted:
                exp = get_experiment_type(f.name)
                dest = ARCHIVE_DIR / 'temporal_logs' / exp / f.name

                if not dry_run:
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(f), str(dest))
                    print(f"  MOVED: {f.name} (drift={max_drift:.2f})")
                else:
                    print(f"  Would move: {f.name} (drift={max_drift:.2f})")

                moved[f'temporal_{exp}'].append((f.name, max_drift))
    else:
        print(f"  WARNING: Directory not found: {TEMPORAL_LOGS_DIR}")

    print()

    # Process consolidated results
    print(f"Scanning results: {RESULTS_DIR}")
    if RESULTS_DIR.exists():
        json_files = list(RESULTS_DIR.glob('*run_018*.json')) + \
                     list(RESULTS_DIR.glob('*run018*.json'))
        print(f"  Found {len(json_files)} Run 018 result files")

        for f in json_files:
            corrupted, max_drift = is_corrupted(f)
            if corrupted:
                dest = ARCHIVE_DIR / 'results' / f.name

                if not dry_run:
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(f), str(dest))
                    print(f"  MOVED: {f.name} (drift={max_drift:.2f})")
                else:
                    print(f"  Would move: {f.name} (drift={max_drift:.2f})")

                moved['results'].append((f.name, max_drift))
    else:
        print(f"  WARNING: Directory not found: {RESULTS_DIR}")

    print()

    # Generate report
    report = generate_corruption_report(moved, dry_run)
    report_path = ARCHIVE_DIR / 'CORRUPTION_REPORT.md'

    if not dry_run:
        report_path.parent.mkdir(parents=True, exist_ok=True)
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"Report written: {report_path}")
    else:
        print("=" * 60)
        print("PREVIEW REPORT:")
        print("=" * 60)
        print(report)

    # Summary
    total_files = sum(len(files) for files in moved.values())
    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total corrupted files found: {total_files}")
    for category, files in sorted(moved.items()):
        print(f"  {category}: {len(files)}")

    if dry_run:
        print()
        print("This was a DRY RUN. No files were moved.")
        print("To actually move files, run: py archive_corrupted_run018.py --execute")

    return 0


if __name__ == '__main__':
    exit(main())
