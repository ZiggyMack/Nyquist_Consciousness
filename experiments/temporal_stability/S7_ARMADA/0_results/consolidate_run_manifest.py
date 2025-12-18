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
ARCHITECTURE_RESULTS_DIR = ARMADA_DIR / "11_CONTEXT_DAMPING" / "results"

# Prefix for files that have been consolidated (prevents re-processing)
CONSOLIDATED_PREFIX = "_CONSOLIDATED_"
# Prefix for files with corrupted data (skipped during consolidation)
CORRUPTED_PREFIX = "_CORRUPTED_"
# Maximum valid drift value (above this = corrupted embedding data)
MAX_VALID_DRIFT = 5.0
# Minimum valid drift value (below this = API failure / no real data)
MIN_VALID_DRIFT = 0.001


def consolidate_run_drift(run_number: str = "018", fresh_mode: bool = False):
    """
    Consolidate all drift values for a run into a single manifest.

    By default, APPENDS to existing manifest. Use fresh_mode=True to overwrite.

    Structure:
    {
        "run": "018",
        "generated": "2025-12-14T...",
        "last_updated": "2025-12-15T...",
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
    output_file = OUTPUT_DIR / f"RUN_{run_number}_DRIFT_MANIFEST.json"

    # Load existing manifest for append mode (default)
    already_processed = set()
    existing_experiments = {}
    existing_generated = None

    if not fresh_mode and output_file.exists():
        print(f"Loading existing manifest for APPEND mode...")
        with open(output_file, 'r', encoding='utf-8') as f:
            existing = json.load(f)
        # Extract already-processed files to skip (by filename only)
        for fp in existing.get("summary", {}).get("files_processed", []):
            already_processed.add(Path(fp).name)
        # Preserve existing experiments data
        existing_experiments = existing.get("experiments", {})
        existing_generated = existing.get("generated")
        print(f"  Found {len(already_processed)} already-processed files to skip")
    elif fresh_mode:
        print("FRESH mode: Creating new manifest from scratch")

    manifest = {
        "run": run_number,
        "generated": existing_generated or datetime.now().isoformat(),
        "last_updated": datetime.now().isoformat(),
        "summary": {
            "total_files": 0,
            "experiments": set(),
            "models_tested": set(),
            "iron_clad_status": {}
        },
        "experiments": defaultdict(lambda: defaultdict(list))
    }

    # Merge existing experiments data first
    for exp, models in existing_experiments.items():
        manifest["summary"]["experiments"].add(exp)
        for model, runs in models.items():
            manifest["summary"]["models_tested"].add(model)
            manifest["experiments"][exp][model].extend(runs)

    # Find all run files (excluding already-consolidated ones)
    pattern = f"S7_run_{run_number}_*.json"
    all_files = list(RUNS_DIR.glob(pattern))

    # Filter out files that start with consolidated prefix
    run_files = [f for f in all_files if not f.name.startswith(CONSOLIDATED_PREFIX)]
    skipped_files = [f for f in all_files if f.name.startswith(CONSOLIDATED_PREFIX)]

    # Also filter out files already in manifest (by filename) for append mode
    if already_processed:
        before_count = len(run_files)
        run_files = [f for f in run_files if f.name not in already_processed]
        skipped_manifest = before_count - len(run_files)
        if skipped_manifest > 0:
            print(f"  (Skipping {skipped_manifest} files already in manifest)")

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

    # Track cumulative files processed (existing + new)
    manifest["summary"]["files_processed"] = list(already_processed)  # Start with existing

    for file_path in sorted(run_files):
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)

            # Parse filename: S7_run_018_threshold_gemini-2.5-pro_20251214_092653.json
            # OR for 020A/020B: S7_run_020A_anthropic_20251213_082831.json
            parts = file_path.stem.split('_')
            run_part = parts[2]  # "018" or "020A" or "020B"

            # For 020A/020B, the experiment is in the JSON data, not filename
            # For 018, the experiment is in the filename
            if run_part in ["020A", "020B"]:
                # Model is right after run number
                model = parts[3] if len(parts) > 3 else "unknown"
                timestamp = f"{parts[-2]}_{parts[-1]}"
                # Get experiment from JSON data
                experiment = data.get("experiment", "tribunal" if run_part == "020A" else "induced")
            else:
                # Standard 018 format: S7_run_018_<experiment>_<model>_<timestamp>
                exp_idx = 3  # S7_run_018_<experiment>
                experiment = parts[exp_idx] if len(parts) > exp_idx else "unknown"
                # Model is everything between experiment and timestamp
                # Timestamp is last two parts (YYYYMMDD_HHMMSS)
                timestamp = f"{parts[-2]}_{parts[-1]}"
                model_parts = parts[exp_idx + 1:-2]
                model = "_".join(model_parts) if model_parts else "unknown"

            # If model is "unknown" from filename, try to get from JSON metadata
            if model == "unknown":
                # Try data["model"], data["provider"], or first subject's model
                model = data.get("model", data.get("provider", "unknown"))
                if model == "unknown" and data.get("subjects"):
                    # Try to get from first subject's provider field
                    first_subject = data["subjects"][0]
                    model = first_subject.get("provider", first_subject.get("model", "unknown"))

            manifest["summary"]["experiments"].add(experiment)
            manifest["summary"]["models_tested"].add(model)

            # Extract drift values - 020A/020B use "results", 018 uses "subjects"
            items = data.get("subjects", data.get("results", []))
            for item in items:
                # Handle both 018 subjects and 020 results format
                drift_entry = {
                    "drift": item.get("baseline_to_final_drift", item.get("final_drift", item.get("peak_drift", None))),
                    "peak_drift": item.get("peak_drift", item.get("max_drift_achieved", None)),
                    "timestamp": timestamp,
                    "file": file_path.name,
                    "i_am": item.get("i_am_name", "base"),
                    "probe_count": len(item.get("probe_sequence", item.get("drift_sequence", []))),
                    "catastrophic": item.get("catastrophic_reached", False)
                }

                # For gravity experiments, also capture fitted parameters
                if experiment == "gravity":
                    drift_entry["gamma"] = item.get("fitted_gamma")
                    drift_entry["lambda"] = item.get("fitted_lambda")
                    drift_entry["omega"] = item.get("fitted_omega")
                    drift_entry["r_squared"] = item.get("fit_r_squared")

                # For nyquist experiments, capture aliasing AND sampling_rate
                if experiment == "nyquist":
                    drift_entry["aliasing_index"] = item.get("identity_aliasing_index")
                    drift_entry["sampling_rate"] = item.get("sampling_rate", "unknown")

                # For 020A tribunal, capture phase peaks
                if experiment == "tribunal":
                    phase_markers = item.get("phase_markers", {})
                    drift_entry["prosecutor_peak"] = phase_markers.get("prosecutor_peak")
                    drift_entry["defense_peak"] = phase_markers.get("defense_peak")
                    drift_entry["total_exchanges"] = item.get("total_exchanges")

                # For 020B induced, capture arm type
                if experiment == "induced":
                    drift_entry["arm"] = item.get("arm")

                # Validate drift - skip entries with corrupted or failed data
                # Corrupted embeddings produce drift=0 with peak_drift~78.4 (random vector distance)
                # Failed API calls produce drift=0 (no actual embedding computed)
                drift_val = drift_entry.get("drift") or 0
                peak_drift_val = drift_entry.get("peak_drift") or 0

                # Skip corrupted entries (high peak_drift = random vector distance)
                if drift_val == 0 and peak_drift_val > MAX_VALID_DRIFT:
                    print(f"  Skipping corrupted entry in {file_path.name}: drift=0, peak_drift={peak_drift_val:.1f}")
                    continue

                # Skip failed API calls (drift=0 with no valid peak_drift either)
                if drift_val < MIN_VALID_DRIFT and peak_drift_val < MIN_VALID_DRIFT:
                    # Both values are essentially zero - this was a failed run
                    continue

                manifest["experiments"][experiment][model].append(drift_entry)

            # Track this file as processed (by filename for deduplication)
            manifest["summary"]["files_processed"].append(file_path.name)

        except Exception as e:
            print(f"  Error processing {file_path.name}: {e}")

    # NOTE: Keep sets as sets - they will be converted to lists after architecture processing
    # Update total_files to be cumulative count
    manifest["summary"]["total_files"] = len(manifest["summary"]["files_processed"])
    manifest["summary"]["new_files_this_run"] = len(run_files)

    return manifest, run_files


def consolidate_architecture_data(manifest: dict, run_number: str = "018"):
    """
    Consolidate architecture experiment data from 11_CONTEXT_DAMPING/results/.

    Architecture data has a different structure:
    - Files: run018a_architecture_*.json
    - Contains: subjects[] with peak_drift, settling_time, ringback_count, full_recovery_curve

    Skips files prefixed with _CORRUPTED_ or _CONSOLIDATED_.
    Also validates peak_drift < MAX_VALID_DRIFT as safety net.
    """
    if not ARCHITECTURE_RESULTS_DIR.exists():
        print(f"Architecture results dir not found: {ARCHITECTURE_RESULTS_DIR}")
        return manifest, []

    pattern = f"run{run_number}a_architecture_*.json"
    all_files = list(ARCHITECTURE_RESULTS_DIR.glob(pattern))

    # Filter out corrupted and consolidated files
    arch_files = [f for f in all_files
                  if not f.name.startswith(CORRUPTED_PREFIX)
                  and not f.name.startswith(CONSOLIDATED_PREFIX)]

    skipped_corrupted = len([f for f in all_files if f.name.startswith(CORRUPTED_PREFIX)])
    skipped_consolidated = len([f for f in all_files if f.name.startswith(CONSOLIDATED_PREFIX)])

    print(f"\nFound {len(arch_files)} architecture files for Run {run_number}")
    if skipped_corrupted:
        print(f"  (Skipping {skipped_corrupted} _CORRUPTED_ files)")
    if skipped_consolidated:
        print(f"  (Skipping {skipped_consolidated} _CONSOLIDATED_ files)")

    # Get already-processed files from manifest
    already_processed = set(manifest["summary"].get("files_processed", []))
    before_count = len(arch_files)
    arch_files = [f for f in arch_files if f.name not in already_processed]
    if before_count - len(arch_files) > 0:
        print(f"  (Skipping {before_count - len(arch_files)} already in manifest)")

    if not arch_files:
        return manifest, []

    # Ensure architecture exists in experiments
    if "architecture" not in manifest["experiments"]:
        manifest["experiments"]["architecture"] = {}

    new_files_processed = []
    valid_entries = 0
    corrupted_entries = 0

    for file_path in sorted(arch_files):
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)

            # Parse model from filename: run018a_architecture_<model>_<timestamp>.json
            # OR legacy format: run018a_architecture_<timestamp>.json
            parts = file_path.stem.split('_')
            if len(parts) >= 4:
                # New format: run018a_architecture_claude-opus-4.5_20251214_054300
                model_parts = parts[2:-2]  # Everything between "architecture" and timestamp
                model = "-".join(model_parts) if model_parts else "unknown"
                timestamp = f"{parts[-2]}_{parts[-1]}"
            else:
                # Legacy format or unexpected - try to get from JSON
                model = "unknown"
                timestamp = parts[-2] + "_" + parts[-1] if len(parts) >= 2 else "unknown"

            # Process subjects
            for subject in data.get("subjects", []):
                # Get model from subject if not from filename
                subject_model = subject.get("provider", subject.get("model", model))
                if subject_model == "unknown" or model == "unknown":
                    subject_model = subject.get("provider", model)

                peak_drift = subject.get("peak_drift", 0)

                # Validate drift value - skip both corrupted (>5) AND failed API calls (=0)
                if peak_drift > MAX_VALID_DRIFT:
                    corrupted_entries += 1
                    continue  # Skip corrupted entries (bad embeddings)
                if peak_drift < MIN_VALID_DRIFT:
                    corrupted_entries += 1
                    continue  # Skip failed API calls (returned 0)

                drift_entry = {
                    "drift": subject.get("baseline_to_final_drift", peak_drift),
                    "peak_drift": peak_drift,
                    "settling_time": subject.get("settling_time"),
                    "ringback_count": subject.get("ringback_count"),
                    "recovery_curve_shape": subject.get("recovery_curve_shape"),
                    "observed_signature": subject.get("observed_signature"),
                    "timestamp": timestamp,
                    "file": file_path.name,
                    "probe_count": len(subject.get("full_recovery_curve", [])),
                }

                # Initialize model entry if needed
                if subject_model not in manifest["experiments"]["architecture"]:
                    manifest["experiments"]["architecture"][subject_model] = []

                manifest["experiments"]["architecture"][subject_model].append(drift_entry)
                valid_entries += 1

                # Track model
                manifest["summary"]["models_tested"].add(subject_model)

            manifest["summary"]["files_processed"].append(file_path.name)
            new_files_processed.append(file_path)

        except Exception as e:
            print(f"  Error processing {file_path.name}: {e}")

    manifest["summary"]["experiments"].add("architecture")
    print(f"  Added {valid_entries} valid entries, skipped {corrupted_entries} corrupted")

    return manifest, new_files_processed


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


def move_to_archive_dir():
    """
    Move all _CONSOLIDATED_ files to root .archive/Run_Data_Consolidated/.
    Keeps the runs directory clean while preserving source files in a central archive.
    """
    # Use root .archive directory, not local _archived
    repo_root = ARMADA_DIR.parent.parent.parent  # Navigate up from S7_ARMADA
    archived_dir = repo_root / ".archive" / "Run_Data_Consolidated"
    archived_dir.mkdir(parents=True, exist_ok=True)

    moved_count = 0
    for f in RUNS_DIR.glob(f"{CONSOLIDATED_PREFIX}*.json"):
        dest = archived_dir / f.name
        shutil.move(str(f), str(dest))
        moved_count += 1

    print(f"\nMoved {moved_count} consolidated files to {archived_dir}")
    return moved_count


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
    parser.add_argument("--no-mark", action="store_true",
                        help="Skip marking files with _CONSOLIDATED_ prefix (default: files ARE marked)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Show what would be consolidated without making changes")
    parser.add_argument("--fresh", action="store_true",
                        help="Create fresh manifest, ignoring existing (default: append to existing)")
    parser.add_argument("--archive-dir", action="store_true",
                        help="Move _CONSOLIDATED_ files to _archived/ subdirectory after consolidation")
    args = parser.parse_args()

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Consolidate drift manifest
    print(f"\n{'='*60}")
    print(f"CONSOLIDATING RUN {args.run} DRIFT MANIFEST")
    if args.dry_run:
        print("(DRY RUN - no changes will be made)")
    if args.fresh:
        print("(FRESH MODE - will overwrite existing manifest)")
    print(f"{'='*60}")

    manifest, run_files = consolidate_run_drift(args.run, fresh_mode=args.fresh)

    # Also consolidate architecture data (from 11_CONTEXT_DAMPING/results/)
    if args.run == "018":
        manifest, arch_files = consolidate_architecture_data(manifest, args.run)
        run_files.extend(arch_files)

    total_new = manifest["summary"].get("new_files_this_run", 0) + len(arch_files if args.run == "018" else [])
    if total_new == 0:
        print("\nNo new files to consolidate!")
        print("(Files with _CONSOLIDATED_ or _CORRUPTED_ prefix are skipped)")
        print(f"Existing manifest has {manifest['summary']['total_files']} files")
        return

    # Convert sets to lists for JSON serialization (after architecture processing)
    if isinstance(manifest["summary"]["experiments"], set):
        manifest["summary"]["experiments"] = sorted(manifest["summary"]["experiments"])
    if isinstance(manifest["summary"]["models_tested"], set):
        manifest["summary"]["models_tested"] = sorted(manifest["summary"]["models_tested"])

    # Convert defaultdicts to regular dicts
    manifest["experiments"] = {k: dict(v) for k, v in manifest["experiments"].items()}

    # Recalculate IRON CLAD status after adding architecture
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

    # Update total files count
    manifest["summary"]["total_files"] = len(manifest["summary"]["files_processed"])

    if not args.dry_run:
        output_file = OUTPUT_DIR / f"RUN_{args.run}_DRIFT_MANIFEST.json"
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(manifest, f, indent=2)
        print(f"\nSaved: {output_file}")

    # Print summary
    print(f"\n--- SUMMARY ---")
    print(f"NEW files this run: {manifest['summary'].get('new_files_this_run', 0)}")
    print(f"Total files in manifest: {manifest['summary']['total_files']}")
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

    # Mark files as consolidated (default behavior, skip with --no-mark)
    if not args.no_mark and not args.dry_run:
        archive_consolidated_files(run_files, args.run)
    elif not args.no_mark and args.dry_run:
        print(f"\n(Would mark {len(run_files)} files with _CONSOLIDATED_ prefix)")

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

    # Move consolidated files to archive directory if requested
    if args.archive_dir and not args.dry_run:
        move_to_archive_dir()
    elif args.archive_dir and args.dry_run:
        # Count how many would be moved
        count = len(list(RUNS_DIR.glob(f"{CONSOLIDATED_PREFIX}*.json")))
        print(f"\n(Would move {count} consolidated files to _archived/)")


if __name__ == "__main__":
    main()
