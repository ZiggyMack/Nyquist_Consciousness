"""
Migrate existing Run 020 data to canonical location with correct naming.

Source: 11_CONTEXT_DAMPING/results/run020_*.json
Target: 0_results/runs/S7_run_020A_{model}_{timestamp}.json
        0_results/runs/S7_run_020B_{model}_{timestamp}.json

The migration:
1. Reads each existing 020 file
2. Extracts model/provider info from contents
3. Determines if it's 020A (tribunal) or 020B (induced/control/treatment)
4. Copies to canonical location with correct naming
5. Adds "model" field if missing for consolidation

Run with --dry-run to preview changes without modifying files.
"""

import json
import shutil
from pathlib import Path
import argparse
import re

SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
LOCAL_RESULTS = ARMADA_DIR / "11_CONTEXT_DAMPING" / "results"
RUNS_DIR = SCRIPT_DIR / "runs"
ARCHIVE_DIR = Path(r"d:\Documents\Nyquist_Consciousness\.archive\Run020_Local_Legacy")

def extract_model_from_file(filepath: Path) -> tuple:
    """Extract model, experiment type, and timestamp from a 020 file."""
    with open(filepath, 'r', encoding='utf-8') as f:
        data = json.load(f)

    # Determine experiment type
    run_type = data.get("run", "")
    arm = data.get("arm", "")

    if "020b" in run_type.lower() or "020B" in run_type or arm in ["control", "treatment", "both"]:
        experiment = "020B"
    elif "tribunal" in run_type.lower() or "v8" in run_type.lower() or "v4" in run_type.lower():
        experiment = "020A"
    else:
        experiment = "020A"  # Default to tribunal

    # Extract model/provider
    model = data.get("model")
    if not model:
        providers = data.get("providers", [])
        if providers:
            if len(providers) == 1:
                model = providers[0]
            else:
                model = "multi"  # Multiple providers in one file
        else:
            provider = data.get("provider") or data.get("witness_provider")
            if provider:
                model = provider
            else:
                # Try to extract from results
                results = data.get("results", [])
                if results and isinstance(results[0], dict):
                    subject_id = results[0].get("subject_id", "")
                    # subject_id format: tribunal_v8_XXXXXXXX or control_XXXXXXXX
                    # Try to extract provider if it's in there
                    model = "unknown"

    if not model:
        model = "unknown"

    # Extract timestamp
    timestamp = data.get("timestamp", "")
    if not timestamp:
        # Try to extract from filename: run020_v8_20251213_102500.json
        match = re.search(r'(\d{8}_\d{6})', filepath.name)
        if match:
            timestamp = match.group(1)
        else:
            timestamp = "unknown"

    return model, experiment, timestamp, data


def migrate_file(src: Path, dst: Path, data: dict, dry_run: bool = False) -> bool:
    """Migrate a single file, adding model field if needed."""
    if dry_run:
        print(f"  [DRY RUN] Would copy: {src.name} -> {dst.name}")
        return True

    # Add model field if not present
    if "model" not in data:
        model = dst.stem.split("_")[3]  # S7_run_020A_MODEL_timestamp
        data["model"] = model

    # Write to destination
    with open(dst, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, default=str)

    print(f"  Migrated: {src.name} -> {dst.name}")
    return True


def main():
    parser = argparse.ArgumentParser(description="Migrate Run 020 data to canonical location")
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without modifying")
    parser.add_argument("--archive", action="store_true", help="Archive source files after migration")
    args = parser.parse_args()

    print("=" * 60)
    print("MIGRATING RUN 020 DATA")
    print("=" * 60)
    print(f"Source: {LOCAL_RESULTS}")
    print(f"Target: {RUNS_DIR}")
    if args.dry_run:
        print("[DRY RUN MODE]")
    print()

    # Find all run020 files
    files = list(LOCAL_RESULTS.glob("run020*.json"))
    print(f"Found {len(files)} files to migrate")
    print()

    migrated = 0
    skipped = 0
    errors = []

    for src in sorted(files):
        try:
            model, experiment, timestamp, data = extract_model_from_file(src)

            # Build target filename
            target_name = f"S7_run_{experiment}_{model}_{timestamp}.json"
            dst = RUNS_DIR / target_name

            # Check if already exists
            if dst.exists() and not args.dry_run:
                print(f"  [SKIP] Already exists: {target_name}")
                skipped += 1
                continue

            if migrate_file(src, dst, data, args.dry_run):
                migrated += 1

        except Exception as e:
            print(f"  [ERROR] {src.name}: {e}")
            errors.append((src.name, str(e)))

    print()
    print("=" * 60)
    print("MIGRATION SUMMARY")
    print("=" * 60)
    print(f"Total files:   {len(files)}")
    print(f"Migrated:      {migrated}")
    print(f"Skipped:       {skipped}")
    print(f"Errors:        {len(errors)}")

    if errors:
        print("\nErrors:")
        for name, err in errors:
            print(f"  - {name}: {err}")

    if args.archive and not args.dry_run and migrated > 0:
        print(f"\nArchiving source files to: {ARCHIVE_DIR}")
        ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
        for src in sorted(files):
            shutil.move(str(src), str(ARCHIVE_DIR / src.name))
        print(f"Archived {len(files)} files")


if __name__ == "__main__":
    main()
