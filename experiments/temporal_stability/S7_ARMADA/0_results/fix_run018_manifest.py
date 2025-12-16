#!/usr/bin/env python3
"""
Fix Run 018 Manifest - Filter out corrupted data and generate recovery tracking.

Problem: Embedding cache pollution from dry-run mode caused corrupted drift values.
         Random embeddings produce Euclidean distance ≈ sqrt(2*3072) ≈ 78.4

Solution:
    1. Filter out corrupted entries (drift > 5.0)
    2. Generate IRON_CLAD_GAPS.md showing what's needed for N=3 per model/experiment
    3. Generate RERUN_QUEUE.md for tracking re-run progress

Usage:
    py fix_run018_manifest.py --dry-run        # Preview changes
    py fix_run018_manifest.py                  # Apply fix
    py fix_run018_manifest.py --generate-gaps  # Also generate gap reports
    py fix_run018_manifest.py --fresh          # Rebuild from source files
"""

import json
from pathlib import Path
from datetime import datetime
from collections import defaultdict
import argparse

ARMADA_DIR = Path(__file__).parent.parent
MANIFEST_DIR = ARMADA_DIR / "0_results" / "manifests"
RESULTS_DIR = ARMADA_DIR / "0_results"
ARCHIVE_DIR = Path("d:/Documents/Nyquist_Consciousness/.archive/Run_Data_Consolidated")
TEMPORAL_LOGS_DIR = ARMADA_DIR / "0_results" / "temporal_logs" / "run018"

# Drift values above this threshold are clearly corrupted
MAX_VALID_DRIFT = 5.0

# IRON CLAD requirement: N=3 runs per model per experiment
IRON_CLAD_N = 3


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


def generate_iron_clad_gaps(manifest: dict) -> str:
    """Generate IRON_CLAD_GAPS.md showing what's needed for completion."""
    iron_clad = manifest.get("summary", {}).get("iron_clad_status", {})

    # Categorize gaps
    complete = []
    incomplete = []
    total_loss = []  # Models with 0 valid runs

    for exp, models in iron_clad.items():
        for model, status in models.items():
            n = status.get("n", 0)
            needed = status.get("needed", IRON_CLAD_N)

            if status.get("complete", False):
                complete.append((exp, model, n))
            elif n == 0:
                total_loss.append((exp, model, IRON_CLAD_N))
            else:
                incomplete.append((exp, model, n, needed))

    # Calculate statistics
    total_combos = len(complete) + len(incomplete) + len(total_loss)
    complete_pct = (len(complete) / total_combos * 100) if total_combos > 0 else 0
    total_reruns_needed = sum(item[3] if len(item) > 3 else IRON_CLAD_N for item in incomplete + total_loss)

    report = f"""# IRON CLAD Gaps - Run 018

**Generated:** {datetime.now().isoformat()}
**Status:** {len(complete)}/{total_combos} complete ({complete_pct:.1f}%)
**Total Re-runs Needed:** {total_reruns_needed}

---

## Executive Summary

| Category | Count | % |
|----------|-------|---|
| Complete (N≥3) | {len(complete)} | {len(complete)/total_combos*100:.1f}% |
| Partial (N<3) | {len(incomplete)} | {len(incomplete)/total_combos*100:.1f}% |
| Total Loss (N=0) | {len(total_loss)} | {len(total_loss)/total_combos*100:.1f}% |

---

## Priority 1: Total Loss (N=0) - {len(total_loss)} model-experiments

These models have ZERO valid data and require full re-runs.

"""

    if total_loss:
        current_exp = None
        for exp, model, needed in sorted(total_loss, key=lambda x: (x[0], x[1])):
            if exp != current_exp:
                current_exp = exp
                report += f"\n### {exp.upper()}\n\n"
            report += f"- [ ] {model}: 0/{IRON_CLAD_N} (need {needed})\n"
    else:
        report += "_No total losses - all models have at least some valid data._\n"

    report += f"""
---

## Priority 2: Partial Data (0 < N < {IRON_CLAD_N}) - {len(incomplete)} model-experiments

These models have some valid data but need additional runs.

"""

    if incomplete:
        current_exp = None
        for exp, model, n, needed in sorted(incomplete, key=lambda x: (x[0], -x[3], x[1])):
            if exp != current_exp:
                current_exp = exp
                report += f"\n### {exp.upper()}\n\n"
            report += f"- [ ] {model}: {n}/{IRON_CLAD_N} (need {needed})\n"
    else:
        report += "_No partial data - all models either complete or total loss._\n"

    report += f"""
---

## Complete (N≥{IRON_CLAD_N}) - {len(complete)} model-experiments

For reference, these model-experiments are complete:

"""

    if complete:
        complete_by_exp = defaultdict(list)
        for exp, model, n in complete:
            complete_by_exp[exp].append((model, n))

        for exp in sorted(complete_by_exp.keys()):
            report += f"### {exp.upper()} ({len(complete_by_exp[exp])} models)\n"
            for model, n in sorted(complete_by_exp[exp]):
                report += f"- [x] {model}: {n}/{IRON_CLAD_N}\n"
            report += "\n"

    report += f"""---

## Recovery Strategy

1. **Run one model at a time** to ensure data validity
2. **Validate after each write** - check drift values are < {MAX_VALID_DRIFT}
3. **Priority order:** Total Loss first, then Partial by most needed

### Recommended Command Pattern

```bash
# Single model, single experiment
py run018_recursive_learnings.py -e threshold --providers claude-opus-4.5

# Validate output before continuing
py fix_run018_manifest.py --dry-run
```

---

*Generated by fix_run018_manifest.py*
"""

    return report


def generate_rerun_queue(manifest: dict) -> str:
    """Generate RERUN_QUEUE.md for tracking re-run progress."""
    iron_clad = manifest.get("summary", {}).get("iron_clad_status", {})

    # Build queue sorted by priority
    queue = []
    for exp, models in iron_clad.items():
        for model, status in models.items():
            needed = status.get("needed", 0)
            if needed > 0:
                queue.append({
                    "experiment": exp,
                    "model": model,
                    "have": status.get("n", 0),
                    "need": needed,
                    "priority": 1 if status.get("n", 0) == 0 else 2
                })

    # Sort: priority 1 first, then by most needed
    queue.sort(key=lambda x: (x["priority"], -x["need"], x["experiment"], x["model"]))

    total_runs = sum(q["need"] for q in queue)

    report = f"""# Run 018 Re-run Queue

**Generated:** {datetime.now().isoformat()}
**Total Runs Needed:** {total_runs}
**Models in Queue:** {len(queue)}

---

## Queue Status

| # | Experiment | Model | Have | Need | Priority | Status |
|---|------------|-------|------|------|----------|--------|
"""

    for i, item in enumerate(queue, 1):
        priority = "P1 (Total Loss)" if item["priority"] == 1 else "P2 (Partial)"
        report += f"| {i} | {item['experiment']} | {item['model']} | {item['have']} | {item['need']} | {priority} | PENDING |\n"

    report += f"""
---

## Execution Log

Record completed runs here:

| Date | Experiment | Model | Runs | Drift Range | Validated |
|------|------------|-------|------|-------------|-----------|
| | | | | | |

---

## Recovery Commands

```bash
# Check current status
py fix_run018_manifest.py --dry-run

# Run single model (recommended approach)
py run018_recursive_learnings.py -e threshold --providers claude-opus-4.5

# After each run, validate:
# 1. Check output file exists in 0_results/runs/
# 2. Verify drift values are < {MAX_VALID_DRIFT}
# 3. Update this log
```

---

*Generated by fix_run018_manifest.py*
"""

    return report


def main():
    parser = argparse.ArgumentParser(description="Fix Run 018 manifest by filtering corrupted data")
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without applying")
    parser.add_argument("--run", default="018", help="Run number (default: 018)")
    parser.add_argument("--generate-gaps", action="store_true",
                        help="Generate IRON_CLAD_GAPS.md and RERUN_QUEUE.md")
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
        # Still generate gap reports if requested
        if args.generate_gaps and not args.dry_run:
            print("\n--- GENERATING GAP REPORTS ---")
            # IRON_CLAD_GAPS.md
            gaps_report = generate_iron_clad_gaps(manifest)
            gaps_path = RESULTS_DIR / "IRON_CLAD_GAPS.md"
            with open(gaps_path, 'w', encoding='utf-8') as f:
                f.write(gaps_report)
            print(f"  IRON_CLAD_GAPS.md saved to: {gaps_path}")

            # RERUN_QUEUE.md
            queue_report = generate_rerun_queue(manifest)
            queue_path = RESULTS_DIR / "RERUN_QUEUE.md"
            with open(queue_path, 'w', encoding='utf-8') as f:
                f.write(queue_report)
            print(f"  RERUN_QUEUE.md saved to: {queue_path}")
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

        # Generate gap reports if requested
        if args.generate_gaps:
            print("\n--- GENERATING GAP REPORTS ---")

            # IRON_CLAD_GAPS.md
            gaps_report = generate_iron_clad_gaps(clean_manifest)
            gaps_path = RESULTS_DIR / "IRON_CLAD_GAPS.md"
            with open(gaps_path, 'w', encoding='utf-8') as f:
                f.write(gaps_report)
            print(f"  IRON_CLAD_GAPS.md saved to: {gaps_path}")

            # RERUN_QUEUE.md
            queue_report = generate_rerun_queue(clean_manifest)
            queue_path = RESULTS_DIR / "RERUN_QUEUE.md"
            with open(queue_path, 'w', encoding='utf-8') as f:
                f.write(queue_report)
            print(f"  RERUN_QUEUE.md saved to: {queue_path}")

    print("\n" + "=" * 60)
    print("FIX COMPLETE")
    print("=" * 60)

    return 0


if __name__ == "__main__":
    exit(main())
