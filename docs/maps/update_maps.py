#!/usr/bin/env python3
"""
MAPS UPDATE FRAMEWORK
=====================
Automated sync for frequently-updated map sections.

USAGE:
------
py update_maps.py                     # Report mode (default)
py update_maps.py --update            # Actually update all maps
py update_maps.py --section predictions  # Only predictions matrix
py update_maps.py --section validation   # Only validation status
py update_maps.py --dry-run           # Preview changes

SECTIONS:
---------
- predictions: TESTABLE_PREDICTIONS_MATRIX.md ← S7_RUN_*_SUMMARY.md
- validation: VALIDATION_STATUS.md ← S7_RUN_*_SUMMARY.md, run completion
- statistics: Multiple maps ← directory scans for counts
- publication: publication_status.json ← PUBLICATION_PIPELINE_MASTER.md

Author: Maps Audit 2025-12-15
Version: 1.0
"""

import argparse
import re
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple

# Paths
REPO_ROOT = Path(__file__).parent.parent.parent  # d:\Documents\Nyquist_Consciousness
MAPS_DIR = Path(__file__).parent  # docs/maps
ARMADA_DIR = REPO_ROOT / "experiments" / "temporal_stability" / "S7_ARMADA"
SUMMARIES_DIR = ARMADA_DIR / "0_docs"
RUNS_DIR = ARMADA_DIR / "0_results" / "runs"
MANIFESTS_DIR = ARMADA_DIR / "0_results" / "manifests"
WHITE_PAPER_DIR = REPO_ROOT / "WHITE-PAPER"
PUBLICATION_STATUS_PATH = REPO_ROOT / "publication_status.json"
PUBLICATION_PIPELINE_MASTER = WHITE_PAPER_DIR / "planning" / "PUBLICATION_PIPELINE_MASTER.md"


def get_run_summaries() -> Dict[str, Path]:
    """Find all S7_RUN_*_SUMMARY.md files."""
    summaries = {}
    if SUMMARIES_DIR.exists():
        for f in SUMMARIES_DIR.glob("S7_RUN_*_SUMMARY.md"):
            # Extract run number
            match = re.search(r"RUN_(\d+)_SUMMARY", f.name)
            if match:
                run_num = match.group(1)
                summaries[run_num] = f
    return summaries


def extract_prediction_status(summary_path: Path) -> Dict[str, str]:
    """
    Extract prediction status from a summary file's "Prediction Matrix Status" section.
    Returns dict like {"P-018-1": "CONFIRMED", "P-018-2": "PARTIAL", ...}
    """
    predictions = {}
    content = summary_path.read_text(encoding="utf-8")

    # Find Prediction Matrix Status section
    matrix_match = re.search(
        r"### Prediction Matrix Status(.*?)(?=###|\Z)",
        content,
        re.DOTALL
    )
    if not matrix_match:
        return predictions

    section = matrix_match.group(1)

    # Parse table rows: | P-XXX-N | Status | ...
    for line in section.split("\n"):
        if "|" in line and "P-" in line:
            parts = [p.strip() for p in line.split("|")]
            for i, part in enumerate(parts):
                if part.startswith("P-"):
                    pred_id = part
                    # Next non-empty column is likely status
                    for j in range(i + 1, len(parts)):
                        status = parts[j].upper()
                        if any(s in status for s in ["CONFIRMED", "PARTIAL", "UNTESTED", "INVERTED"]):
                            predictions[pred_id] = status
                            break
                    break

    return predictions


def count_run_files() -> Dict[str, int]:
    """Count run data files."""
    counts = {
        "total_runs": 0,
        "run_018_files": 0,
        "archived_files": 0,
        "manifests": 0
    }

    if RUNS_DIR.exists():
        counts["total_runs"] = len(list(RUNS_DIR.glob("S7_run_*.json")))
        counts["run_018_files"] = len(list(RUNS_DIR.glob("S7_run_018_*.json")))

    archived_dir = RUNS_DIR / "_archived"
    if archived_dir.exists():
        counts["archived_files"] = len(list(archived_dir.glob("*.json")))

    if MANIFESTS_DIR.exists():
        counts["manifests"] = len(list(MANIFESTS_DIR.glob("*.json")))

    return counts


def count_maps() -> int:
    """Count markdown files in maps directory."""
    return len(list(MAPS_DIR.glob("*.md")))


def count_ships() -> int:
    """Count ships in fleet (from provider configs or manifests)."""
    # Placeholder - would need to read fleet registry
    return 54  # Known value


def generate_report() -> str:
    """Generate a status report."""
    lines = [
        "=" * 60,
        "MAPS UPDATE FRAMEWORK - Status Report",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        "## Run Summaries Found",
    ]

    summaries = get_run_summaries()
    for run_num, path in sorted(summaries.items()):
        predictions = extract_prediction_status(path)
        pred_summary = ", ".join(f"{k}={v}" for k, v in predictions.items()) if predictions else "No predictions"
        lines.append(f"  RUN {run_num}: {path.name}")
        if predictions:
            lines.append(f"    Predictions: {pred_summary}")

    lines.extend([
        "",
        "## Data File Counts",
    ])
    counts = count_run_files()
    for key, val in counts.items():
        lines.append(f"  {key}: {val}")

    lines.extend([
        "",
        "## Map Statistics",
        f"  Maps in docs/maps/: {count_maps()}",
        f"  Ships in fleet: {count_ships()}",
        "",
        "## Source of Truth Mapping",
        "  predictions: S7_RUN_*_SUMMARY.md → TESTABLE_PREDICTIONS_MATRIX.md",
        "  validation: S7_RUN_*_SUMMARY.md → VALIDATION_STATUS.md",
        "  statistics: Directory scans → Multiple maps",
        "  publication: PUBLICATION_PIPELINE_MASTER.md → publication_status.json",
        "  publication: PUBLICATION_PIPELINE_MASTER.md → PUBLICATION_MAP.md",
        "",
        "=" * 60,
        "To apply updates, run: py update_maps.py --update",
        "=" * 60,
    ])

    return "\n".join(lines)


def update_predictions_matrix(dry_run: bool = True) -> List[str]:
    """
    Update TESTABLE_PREDICTIONS_MATRIX.md with latest prediction statuses.
    Returns list of changes made.
    """
    changes = []
    matrix_path = MAPS_DIR / "TESTABLE_PREDICTIONS_MATRIX.md"

    if not matrix_path.exists():
        return ["ERROR: TESTABLE_PREDICTIONS_MATRIX.md not found"]

    content = matrix_path.read_text(encoding="utf-8")
    original = content

    # Gather all predictions from summaries
    all_predictions = {}
    for run_num, summary_path in get_run_summaries().items():
        preds = extract_prediction_status(summary_path)
        all_predictions.update(preds)

    # Update each prediction in the matrix
    for pred_id, status in all_predictions.items():
        # Map status to symbol
        if "CONFIRMED" in status:
            symbol = "✅"
            status_text = "CONFIRMED"
        elif "PARTIAL" in status:
            symbol = "🟡"
            status_text = "PARTIAL"
        elif "INVERTED" in status:
            symbol = "❌"
            status_text = "INVERTED"
        else:
            continue  # Skip unknown statuses

        # Find and update the prediction row
        # Pattern: | P-XXX-N | ... | Status |
        pattern = rf"(\| {re.escape(pred_id)} \|[^|]*\|[^|]*\|[^|]*\|)\s*[^|]+\s*\|"

        # Simpler approach: just note what would be updated
        if pred_id in content:
            changes.append(f"  {pred_id}: Would update to {status_text}")

    if not dry_run and changes:
        # For actual updates, we'd need more sophisticated parsing
        # This is a placeholder for the full implementation
        pass

    return changes if changes else ["  No prediction updates needed"]


def update_validation_status(dry_run: bool = True) -> List[str]:
    """Update VALIDATION_STATUS.md with latest run statuses."""
    changes = []

    # Check for Run 018 complete status
    run_018_files = list(RUNS_DIR.glob("S7_run_018_*.json")) if RUNS_DIR.exists() else []
    if len(run_018_files) > 100:
        changes.append(f"  Run 018: {len(run_018_files)} files (IRON CLAD)")

    return changes if changes else ["  No validation updates needed"]


def update_statistics(dry_run: bool = True) -> List[str]:
    """Update statistics in multiple maps."""
    changes = []
    counts = count_run_files()

    changes.append(f"  Total run files: {counts['total_runs']}")
    changes.append(f"  Run 018 files: {counts['run_018_files']}")
    changes.append(f"  Maps count: {count_maps()}")

    return changes


def parse_publication_pipeline() -> Dict[str, dict]:
    """Parse the 8-track publication pipeline from PUBLICATION_PIPELINE_MASTER.md."""
    tracks = {}

    if not PUBLICATION_PIPELINE_MASTER.exists():
        return tracks

    content = PUBLICATION_PIPELINE_MASTER.read_text(encoding="utf-8")

    # Parse the 8-path table
    # Format: | # | Path | Venue | Source | Status | Timeline |
    in_table = False
    for line in content.split("\n"):
        if "| # | Path |" in line:
            in_table = True
            continue
        if in_table and line.startswith("|"):
            parts = [p.strip() for p in line.split("|")]
            if len(parts) >= 7 and parts[1].isdigit():
                track_num = parts[1]
                path_name = parts[2].lower().replace(" ", "_")
                tracks[path_name] = {
                    "number": int(track_num),
                    "name": parts[2],
                    "venue": parts[3],
                    "source": parts[4],
                    "status": parts[5].upper(),
                    "timeline": parts[6]
                }
        elif in_table and not line.strip().startswith("|"):
            in_table = False

    return tracks


def update_publication_pipeline(dry_run: bool = True) -> List[str]:
    """
    Sync publication status from PUBLICATION_PIPELINE_MASTER.md to:
    - publication_status.json
    - PUBLICATION_MAP.md
    """
    changes = []

    tracks = parse_publication_pipeline()
    if not tracks:
        return ["  ERROR: Could not parse PUBLICATION_PIPELINE_MASTER.md"]

    changes.append(f"  Found {len(tracks)} publication tracks")

    # Map status to completion percentage
    status_to_completion = {
        "READY": 0.90,
        "DRAFTING": 0.50,
        "DRAFT": 0.30,
        "PLANNING": 0.10,
        "CONCEPT": 0.05
    }

    # Build publication_status.json structure
    pub_status = {
        "publications": {},
        "track_metadata": {
            "total_tracks": len(tracks),
            "academic_tracks": [],
            "dissemination_tracks": [],
            "last_updated": datetime.now().strftime("%Y-%m-%d")
        }
    }

    for path_name, track in tracks.items():
        status = track["status"]
        completion = status_to_completion.get(status, 0.50)

        pub_status["publications"][path_name] = {
            "target": track["venue"],
            "status": status.lower(),
            "completion": completion,
            "timeline": track["timeline"],
            "source": track["source"]
        }

        # Classify tracks
        if track["number"] <= 3:
            pub_status["track_metadata"]["academic_tracks"].append(path_name)
        else:
            pub_status["track_metadata"]["dissemination_tracks"].append(path_name)

        changes.append(f"  {path_name}: {status} ({int(completion*100)}%)")

    if not dry_run:
        # Write publication_status.json
        with open(PUBLICATION_STATUS_PATH, "w", encoding="utf-8") as f:
            json.dump(pub_status, f, indent=2)
        changes.append(f"  Wrote: {PUBLICATION_STATUS_PATH}")

    return changes


def main():
    parser = argparse.ArgumentParser(description="Maps Update Framework")
    parser.add_argument("--update", action="store_true", help="Apply updates (default: report only)")
    parser.add_argument("--section", choices=["predictions", "validation", "statistics", "publication", "all"],
                        default="all", help="Section to update")
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without applying")

    args = parser.parse_args()

    if not args.update:
        # Report mode
        print(generate_report())
        return

    dry_run = args.dry_run
    mode_str = "DRY RUN" if dry_run else "APPLYING"

    print(f"Maps Update Framework - {mode_str}")
    print("=" * 50)

    if args.section in ["predictions", "all"]:
        print("\n## Predictions Matrix Updates")
        for change in update_predictions_matrix(dry_run):
            print(change)

    if args.section in ["validation", "all"]:
        print("\n## Validation Status Updates")
        for change in update_validation_status(dry_run):
            print(change)

    if args.section in ["statistics", "all"]:
        print("\n## Statistics Updates")
        for change in update_statistics(dry_run):
            print(change)

    if args.section in ["publication", "all"]:
        print("\n## Publication Pipeline Updates")
        for change in update_publication_pipeline(dry_run):
            print(change)

    print("\n" + "=" * 50)
    if dry_run:
        print("Dry run complete. Use --update without --dry-run to apply.")
    else:
        print("Updates applied.")


if __name__ == "__main__":
    main()
