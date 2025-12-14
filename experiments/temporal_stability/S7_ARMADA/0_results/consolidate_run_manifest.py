#!/usr/bin/env python3
"""
Consolidate scattered run results into unified manifests.

Creates:
1. RUN_018_DRIFT_MANIFEST.json - All drift values by experiment/model
2. TEMPORAL_LOG_INDEX.json - Index pointing to temporal log files

Usage:
    python consolidate_run_manifest.py [--run 018]
    python consolidate_run_manifest.py [--run 018] --archive  # Move processed files

IMPORTANT: After consolidation, files are moved to _consolidated/ subfolder
to prevent double-processing. The manifest tracks which files were processed.
"""

import json
import os
import shutil
from pathlib import Path
from datetime import datetime
from collections import defaultdict
import argparse

ARMADA_DIR = Path(__file__).parent.parent
RUNS_DIR = ARMADA_DIR / "0_results" / "runs"
TEMPORAL_LOGS_DIR = ARMADA_DIR / "0_results" / "temporal_logs"
OUTPUT_DIR = ARMADA_DIR / "0_results" / "manifests"

# Prefix for files that have been consolidated (prevents re-processing)
CONSOLIDATED_PREFIX = "_CONSOLIDATED_"


def consolidate_run_drift(run_number: str = "018", archive_after: bool = False):
    """
    Consolidate all drift values for a run into a single manifest.

    Structure:
    {
        "run": "018",
        "generated": "2025-12-14T...",
        "summary": {
            "total_files": N,
            "experiments": ["threshold", "nyquist", "gravity", "architecture"],
            "models_tested": [...],
            "iron_clad_status": {...}
        },
        "experiments": {
            "threshold": {
                "gemini-2.5-pro": [
                    {"drift": 0.746, "timestamp": "...", "file": "..."},
                    ...  # Multiple runs for N=3
                ],
                ...
            }
        }
    }
    """
    manifest = {
        "run": run_number,
        "generated": datetime.now().isoformat(),
        "summary": {
            "total_files": 0,
            "experiments": set(),
            "models_tested": set(),
            "iron_clad_status": {}
        },
        "experiments": defaultdict(lambda: defaultdict(list))
    }

    # Find all run files (excluding already-consolidated ones)
    pattern = f"S7_run_{run_number}_*.json"
    all_files = list(RUNS_DIR.glob(pattern))

    # Filter out files that start with consolidated prefix
    run_files = [f for f in all_files if not f.name.startswith(CONSOLIDATED_PREFIX)]
    skipped_files = [f for f in all_files if f.name.startswith(CONSOLIDATED_PREFIX)]

    # Also check legacy_runs
    legacy_dir = RUNS_DIR / "legacy_runs"
    if legacy_dir.exists():
        legacy_files = list(legacy_dir.glob(pattern))
        run_files.extend([f for f in legacy_files if not f.name.startswith(CONSOLIDATED_PREFIX)])

    # Also check subdirectories (pre_armada_018, etc.)
    for subdir in RUNS_DIR.iterdir():
        if subdir.is_dir() and not subdir.name.startswith('_') and subdir.name not in ['legacy_runs']:
            subdir_files = list(subdir.glob(pattern))
            run_files.extend([f for f in subdir_files if not f.name.startswith(CONSOLIDATED_PREFIX)])

    print(f"Found {len(run_files)} NEW files for Run {run_number}")
    if skipped_files:
        print(f"  (Skipping {len(skipped_files)} already-consolidated files)")

    manifest["summary"]["total_files"] = len(run_files)
    manifest["summary"]["files_processed"] = []  # Track which files we process

    for file_path in sorted(run_files):
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)

            # Parse filename: S7_run_018_threshold_gemini-2.5-pro_20251214_092653.json
            parts = file_path.stem.split('_')
            # Find experiment type (after run number)
            exp_idx = 3  # S7_run_018_<experiment>
            experiment = parts[exp_idx] if len(parts) > exp_idx else "unknown"

            # Model is everything between experiment and timestamp
            # Timestamp is last two parts (YYYYMMDD_HHMMSS)
            timestamp = f"{parts[-2]}_{parts[-1]}"
            model_parts = parts[exp_idx + 1:-2]
            model = "_".join(model_parts) if model_parts else "unknown"

            manifest["summary"]["experiments"].add(experiment)
            manifest["summary"]["models_tested"].add(model)

            # Extract drift values from subjects
            subjects = data.get("subjects", [])
            for subject in subjects:
                drift_entry = {
                    "drift": subject.get("baseline_to_final_drift", subject.get("peak_drift", None)),
                    "max_drift": subject.get("max_drift_achieved", None),
                    "timestamp": timestamp,
                    "file": file_path.name,
                    "i_am": subject.get("i_am_name", "base"),
                    "probe_count": len(subject.get("probe_sequence", [])),
                    "catastrophic": subject.get("catastrophic_reached", False)
                }

                # For gravity experiments, also capture fitted parameters
                if experiment == "gravity":
                    drift_entry["gamma"] = subject.get("fitted_gamma")
                    drift_entry["lambda"] = subject.get("fitted_lambda")
                    drift_entry["omega"] = subject.get("fitted_omega")
                    drift_entry["r_squared"] = subject.get("fit_r_squared")

                # For nyquist experiments, capture aliasing
                if experiment == "nyquist":
                    drift_entry["aliasing_index"] = subject.get("identity_aliasing_index")

                manifest["experiments"][experiment][model].append(drift_entry)

            # Track this file as processed
            manifest["summary"]["files_processed"].append(str(file_path))

        except Exception as e:
            print(f"  Error processing {file_path.name}: {e}")

    # Convert sets to lists for JSON serialization
    manifest["summary"]["experiments"] = sorted(manifest["summary"]["experiments"])
    manifest["summary"]["models_tested"] = sorted(manifest["summary"]["models_tested"])

    # Calculate IRON CLAD status (N=3 per model per experiment)
    iron_clad = {}
    for exp, models in manifest["experiments"].items():
        iron_clad[exp] = {}
        for model, runs in models.items():
            n = len(runs)
            iron_clad[exp][model] = {
                "n": n,
                "complete": n >= 3,
                "needed": max(0, 3 - n)
            }
    manifest["summary"]["iron_clad_status"] = iron_clad

    # Convert defaultdicts to regular dicts
    manifest["experiments"] = {k: dict(v) for k, v in manifest["experiments"].items()}

    return manifest, run_files


def archive_consolidated_files(run_files: list, run_number: str):
    """
    Rename processed files with CONSOLIDATED prefix to prevent re-processing.
    """
    archived_count = 0
    for file_path in run_files:
        file_path = Path(file_path)
        if file_path.exists() and not file_path.name.startswith(CONSOLIDATED_PREFIX):
            new_name = file_path.parent / f"{CONSOLIDATED_PREFIX}{file_path.name}"
            file_path.rename(new_name)
            archived_count += 1

    print(f"\nArchived {archived_count} files (renamed with {CONSOLIDATED_PREFIX} prefix)")
    return archived_count


def create_temporal_log_index():
    """
    Create an index of all temporal log files.

    Structure:
    {
        "generated": "...",
        "total_files": N,
        "by_run": {
            "017": {
                "prep": ["file1.json", ...],
                "personas": [...]
            },
            "018": {...}
        }
    }
    """
    index = {
        "generated": datetime.now().isoformat(),
        "total_files": 0,
        "by_run": defaultdict(lambda: defaultdict(list))
    }

    # Walk temporal_logs directory
    for root, dirs, files in os.walk(TEMPORAL_LOGS_DIR):
        for filename in files:
            if not filename.endswith('.json'):
                continue

            index["total_files"] += 1
            rel_path = Path(root).relative_to(TEMPORAL_LOGS_DIR)

            # Parse run number from filename (run017_..., run018_..., etc.)
            if filename.startswith("run"):
                parts = filename.split('_')
                run_num = parts[0].replace("run", "")
                experiment = parts[1] if len(parts) > 1 else "unknown"

                full_path = str(rel_path / filename) if str(rel_path) != "." else filename
                index["by_run"][run_num][experiment].append(full_path)
            elif "meta_loop" in filename.lower():
                index["by_run"]["legacy"]["meta_loop"].append(filename)

    # Convert defaultdicts
    index["by_run"] = {k: dict(v) for k, v in index["by_run"].items()}

    return index


def main():
    parser = argparse.ArgumentParser(description="Consolidate run results into manifests")
    parser.add_argument("--run", default="018", help="Run number to consolidate (default: 018)")
    parser.add_argument("--archive", action="store_true",
                        help="Rename processed files with _CONSOLIDATED_ prefix after consolidation")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be consolidated without making changes")
    args = parser.parse_args()

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Consolidate drift manifest
    print(f"\n{'='*60}")
    print(f"CONSOLIDATING RUN {args.run} DRIFT MANIFEST")
    if args.dry_run:
        print("(DRY RUN - no changes will be made)")
    print(f"{'='*60}")

    manifest, run_files = consolidate_run_drift(args.run)

    if manifest["summary"]["total_files"] == 0:
        print("\nNo new files to consolidate!")
        print("(Files with _CONSOLIDATED_ prefix are skipped)")
        return

    if not args.dry_run:
        output_file = OUTPUT_DIR / f"RUN_{args.run}_DRIFT_MANIFEST.json"
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(manifest, f, indent=2)
        print(f"\nSaved: {output_file}")

    # Print summary
    print(f"\n--- SUMMARY ---")
    print(f"Total files processed: {manifest['summary']['total_files']}")
    print(f"Experiments: {', '.join(manifest['summary']['experiments'])}")
    print(f"Models tested: {len(manifest['summary']['models_tested'])}")

    print(f"\n--- IRON CLAD STATUS (N=3 required) ---")
    for exp, models in manifest["summary"]["iron_clad_status"].items():
        complete = sum(1 for m in models.values() if m["complete"])
        total = len(models)
        print(f"  {exp}: {complete}/{total} models complete")
        incomplete = [(m, d["n"]) for m, d in models.items() if not d["complete"]]
        if incomplete:
            for m, n in incomplete[:5]:
                print(f"    - {m}: {n}/3")
            if len(incomplete) > 5:
                print(f"    ... and {len(incomplete)-5} more")

    # Archive files if requested
    if args.archive and not args.dry_run:
        archive_consolidated_files(run_files, args.run)
    elif args.archive and args.dry_run:
        print(f"\n(Would archive {len(run_files)} files)")

    # Create temporal log index
    print(f"\n{'='*60}")
    print(f"CREATING TEMPORAL LOG INDEX")
    print(f"{'='*60}")

    log_index = create_temporal_log_index()

    if not args.dry_run:
        index_file = OUTPUT_DIR / "TEMPORAL_LOG_INDEX.json"
        with open(index_file, 'w', encoding='utf-8') as f:
            json.dump(log_index, f, indent=2)
        print(f"\nSaved: {index_file}")

    print(f"Total temporal logs indexed: {log_index['total_files']}")

    for run, exps in log_index["by_run"].items():
        total = sum(len(files) for files in exps.values())
        print(f"  Run {run}: {total} files")


if __name__ == "__main__":
    main()
