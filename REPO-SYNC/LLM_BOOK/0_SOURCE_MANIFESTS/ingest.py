#!/usr/bin/env python3
"""
ingest.py - NotebookLM STAGING → LLM_BOOK Ingestion
====================================================
Processes NotebookLM outputs from STAGING/ into the LLM_BOOK/ structure.

WORKFLOW:
---------
1. Archive current LLM_BOOK/ state via 1_sync_llmbook.py (to packages/{version}/llmbook/)
2. Clear LLM_BOOK/ content directories (preserve structure)
3. Ingest from STAGING/ into LLM_BOOK/:
   - Nyquist content → 1_VALIDATION/{folder}/ (for Claude review)
   - R&D content → RnD/{topic}/
4. Claude reviews 1_VALIDATION/ content and provides feedback
5. digest.py routes reviewed content → 2_PUBLICATIONS/, 3_VISUALS/, 7_AUDIO/

The 1_VALIDATION/ directory serves as a REVIEW CHECKPOINT where Claude can:
- Assess NotebookLM synthesis quality
- Verify accuracy against source data
- Suggest publication category placement
- Flag issues before content goes to final directories

USAGE:
------
py ingest.py                    # Report mode - show what would happen
py ingest.py --ingest           # Lite mode - REVIEW_NOTES.md only
py ingest.py --ingest --full    # Full mode - also generates DEEP_DIVES, FUTURE, EXPERIMENTS
py ingest.py --ingest --dry-run # Preview without changes
py ingest.py --skip-archive     # Skip archiving step (dangerous!)

STAGING STRUCTURE:
------------------
STAGING/
├── Nyquist_1/_IN/   → 1_VALIDATION/Nyquist_1/ (awaits Claude review)
├── Nyquist_2/_IN/   → 1_VALIDATION/Nyquist_2/ (awaits Claude review)
├── RAG/             → RnD/RAG/
├── HOFFMAN/         → RnD/HOFFMAN/
├── Gnostic-*/       → RnD/Gnostic/
└── ...              → RnD/{topic}/

POST-INGESTION:
---------------
After ingestion, ask Claude to review 1_VALIDATION/ content:
"Please review the content in 1_VALIDATION/ and provide feedback on:
 - Quality of NotebookLM synthesis
 - Suggested publication categories
 - Any accuracy issues or gaps"

Then run: py digest.py --digest

Author: LLM_BOOK Ingestion Pipeline
Version: 2.0 (2025-12-29) - Added review checkpoint documentation
"""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple

# === PATH CONSTANTS ===
SCRIPT_DIR = Path(__file__).parent
LLM_BOOK_DIR = SCRIPT_DIR.parent  # REPO-SYNC/LLM_BOOK/
STAGING_DIR = SCRIPT_DIR / "STAGING"
REPO_ROOT = LLM_BOOK_DIR.parent.parent  # d:\Documents\Nyquist_Consciousness
WHITE_PAPER_DIR = REPO_ROOT / "WHITE-PAPER"
SYNC_SCRIPT = WHITE_PAPER_DIR / "calibration" / "1_sync_llmbook.py"
VERSION_FILE = WHITE_PAPER_DIR / "reviewers" / "packages" / "CURRENT_VERSION.json"

# LLM_BOOK content directories (cleared on ingestion)
CONTENT_DIRS = [
    LLM_BOOK_DIR / "1_VALIDATION",
    LLM_BOOK_DIR / "2_PUBLICATIONS",
    LLM_BOOK_DIR / "3_VISUALS",
    LLM_BOOK_DIR / "7_AUDIO",
    LLM_BOOK_DIR / "RnD",
]

# Validation subdirectories for --full mode analysis
VALIDATION_ANALYSIS_DIRS = [
    LLM_BOOK_DIR / "1_VALIDATION" / "1_DEEP_DIVES",
    LLM_BOOK_DIR / "1_VALIDATION" / "2_FUTURE",
    LLM_BOOK_DIR / "1_VALIDATION" / "3_EXPERIMENTS",
]

# Directories to preserve (not cleared)
PRESERVE_DIRS = [
    LLM_BOOK_DIR / "0_SOURCE_MANIFESTS",  # Contains STAGING and this script
]


def get_version_info() -> Dict:
    """Read CURRENT_VERSION.json for review status and version info."""
    if VERSION_FILE.exists():
        with open(VERSION_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {"current_version": "unknown", "review_status": "unknown"}


def check_review_status() -> Tuple[str, str, bool]:
    """
    Check if current version has been reviewed.

    Returns:
        (version, status, is_safe) - version string, status string, True if safe to proceed
    """
    info = get_version_info()
    version = info.get("current_version", "unknown")
    status = info.get("review_status", "pending")

    # Safe to proceed if reviewed or preservation_complete
    is_safe = status in ["reviewed", "preservation_complete"]

    return version, status, is_safe


def is_nyquist_content(folder_name: str) -> bool:
    """Determine if a staging folder contains Nyquist-specific content."""
    nyquist_keywords = ["nyquist", "infinity-nyquist"]
    return any(kw in folder_name.lower() for kw in nyquist_keywords)


def get_rnd_topic_name(folder_name: str) -> str:
    """Normalize R&D folder names for consistent directory structure."""
    # Consolidate Gnostic variations
    if folder_name.lower().startswith("gnostic"):
        return "Gnostic"
    # Keep other names as-is but clean up
    return folder_name.replace("-", "_").replace(" ", "_")


def discover_staging_folders() -> Dict[str, List[Path]]:
    """
    Discover all content in STAGING/ and classify by type.

    Returns:
        {
            "nyquist": [Path(...), ...],  # Folders with Nyquist content
            "rnd": [Path(...), ...]       # R&D folders
        }
    """
    result = {"nyquist": [], "rnd": []}

    if not STAGING_DIR.exists():
        return result

    for item in STAGING_DIR.iterdir():
        if not item.is_dir():
            continue

        if is_nyquist_content(item.name):
            result["nyquist"].append(item)
        else:
            result["rnd"].append(item)

    return result


def archive_current_state(dry_run: bool = True) -> bool:
    """
    Archive current LLM_BOOK/ state by calling 1_sync_llmbook.py.

    Returns True if successful, False otherwise.
    """
    if not SYNC_SCRIPT.exists():
        print(f"  [!] Archive script not found: {SYNC_SCRIPT}")
        return False

    cmd = ["python", str(SYNC_SCRIPT), "--sync"]
    if dry_run:
        cmd.append("--dry-run")

    print(f"  Running: {' '.join(cmd)}")

    if dry_run:
        print("  [DRY RUN] Would archive current LLM_BOOK/ state")
        return True

    result = subprocess.run(cmd, capture_output=True, text=True)

    if result.returncode != 0:
        print(f"  [!] Archive failed: {result.stderr}")
        return False

    print("  [OK] Archived current LLM_BOOK/ state")
    return True


def clear_content_directories(dry_run: bool = True) -> None:
    """Clear LLM_BOOK content directories (preserve structure)."""
    for content_dir in CONTENT_DIRS:
        if not content_dir.exists():
            continue

        # Count files to remove
        files = list(content_dir.rglob("*"))
        file_count = sum(1 for f in files if f.is_file())

        if dry_run:
            print(f"  [DRY RUN] Would clear {content_dir.name}/ ({file_count} files)")
        else:
            # Remove all contents but keep the directory
            for item in content_dir.iterdir():
                if item.is_file():
                    item.unlink()
                elif item.is_dir():
                    shutil.rmtree(item)
            print(f"  [OK] Cleared {content_dir.name}/ ({file_count} files)")


def copy_folder_contents(source: Path, target: Path, dry_run: bool = True) -> int:
    """
    Copy contents of source folder to target.

    Returns number of files copied.
    """
    if not source.exists():
        return 0

    file_count = 0

    for item in source.rglob("*"):
        if item.is_file():
            rel_path = item.relative_to(source)
            target_path = target / rel_path

            if dry_run:
                file_count += 1
            else:
                target_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(item, target_path)
                file_count += 1

    return file_count


def ingest_nyquist_content(folders: List[Path], dry_run: bool = True) -> Dict:
    """
    Ingest Nyquist-specific content into publication pipeline.

    Nyquist folders typically have:
    - _IN/ subfolder with NotebookLM outputs
    - _OUT/ subfolder with what was uploaded

    _IN/ content goes to 1_VALIDATION/ (the synthesis/validation outputs)
    """
    result = {"folders": 0, "files": 0, "details": []}

    validation_dir = LLM_BOOK_DIR / "1_VALIDATION"

    for folder in folders:
        # Look for _IN subfolder (NotebookLM outputs)
        in_folder = folder / "_IN"
        if in_folder.exists():
            target = validation_dir / folder.name
            file_count = copy_folder_contents(in_folder, target, dry_run)
            result["folders"] += 1
            result["files"] += file_count
            result["details"].append({
                "source": f"{folder.name}/_IN",
                "target": f"1_VALIDATION/{folder.name}",
                "files": file_count
            })

            if dry_run:
                print(f"  [DRY RUN] {folder.name}/_IN -> 1_VALIDATION/{folder.name} ({file_count} files)")
            else:
                print(f"  [OK] {folder.name}/_IN -> 1_VALIDATION/{folder.name} ({file_count} files)")

    return result


def ingest_rnd_content(folders: List[Path], dry_run: bool = True) -> Dict:
    """
    Ingest R&D content into RnD/ directory.

    Each R&D folder becomes a subdirectory under RnD/.
    """
    result = {"folders": 0, "files": 0, "details": []}

    rnd_dir = LLM_BOOK_DIR / "RnD"

    for folder in folders:
        topic_name = get_rnd_topic_name(folder.name)
        target = rnd_dir / topic_name

        # Copy entire folder contents
        file_count = copy_folder_contents(folder, target, dry_run)

        if file_count > 0:
            result["folders"] += 1
            result["files"] += file_count
            result["details"].append({
                "source": folder.name,
                "target": f"RnD/{topic_name}",
                "files": file_count
            })

            if dry_run:
                print(f"  [DRY RUN] {folder.name} -> RnD/{topic_name} ({file_count} files)")
            else:
                print(f"  [OK] {folder.name} -> RnD/{topic_name} ({file_count} files)")

    return result


def generate_report() -> str:
    """Generate status report of STAGING contents."""
    staging = discover_staging_folders()

    lines = [
        "=" * 60,
        "LLM_BOOK INGESTION STATUS",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        f"STAGING location: {STAGING_DIR}",
        "",
    ]

    # Nyquist content
    lines.append("## Nyquist Content (-> publication pipeline)")
    if staging["nyquist"]:
        for folder in staging["nyquist"]:
            in_folder = folder / "_IN"
            if in_folder.exists():
                file_count = sum(1 for f in in_folder.rglob("*") if f.is_file())
                lines.append(f"  - {folder.name}/_IN ({file_count} files)")
            else:
                lines.append(f"  - {folder.name} (no _IN subfolder)")
    else:
        lines.append("  (none found)")

    lines.append("")

    # R&D content
    lines.append("## R&D Content (-> RnD/ directory)")
    if staging["rnd"]:
        for folder in staging["rnd"]:
            file_count = sum(1 for f in folder.rglob("*") if f.is_file())
            topic = get_rnd_topic_name(folder.name)
            lines.append(f"  - {folder.name} -> RnD/{topic} ({file_count} files)")
    else:
        lines.append("  (none found)")

    lines.extend([
        "",
        "=" * 60,
        "To perform ingestion: py ingest.py --ingest",
        "To preview changes:   py ingest.py --ingest --dry-run",
        "=" * 60,
    ])

    return "\n".join(lines)


def perform_ingestion(dry_run: bool = True, skip_archive: bool = False) -> Dict:
    """
    Perform full ingestion workflow.

    1. Archive current state
    2. Clear content directories
    3. Ingest from STAGING
    """
    results = {
        "timestamp": datetime.now().isoformat(),
        "dry_run": dry_run,
        "archived": False,
        "cleared": False,
        "nyquist": {},
        "rnd": {},
    }

    print("=" * 60)
    print("LLM_BOOK INGESTION")
    print(f"Mode: {'DRY RUN' if dry_run else 'APPLYING CHANGES'}")
    print("=" * 60)

    # Pre-flight check: Has current version been reviewed?
    version, status, is_safe = check_review_status()
    print(f"\n## Pre-flight Check: Review Status")
    print(f"  Current version: {version}")
    print(f"  Review status:   {status}")

    if not is_safe:
        print("")
        print("  " + "!" * 56)
        print("  !  WARNING: Current version has NOT been reviewed!    !")
        print("  !                                                     !")
        print("  !  Reviewers may have preservation_requests pending.  !")
        print("  !  Consider reviewing packages/{version}/ first to    !")
        print("  !  flag any content that should be carried forward.   !")
        print("  !                                                     !")
        print("  !  To dismiss: update review_status in                !")
        print("  !  CURRENT_VERSION.json to 'reviewed'                 !")
        print("  " + "!" * 56)
        print("")
        results["review_warning"] = True
    else:
        print("  [OK] Version has been reviewed")
        results["review_warning"] = False

    # Step 1: Archive current state
    print("\n## Step 1: Archive current LLM_BOOK/ state")
    if skip_archive:
        print("  [SKIPPED] --skip-archive flag set")
    else:
        results["archived"] = archive_current_state(dry_run)
        if not results["archived"] and not dry_run:
            print("\n[!] Archive failed - aborting ingestion to prevent data loss")
            return results

    # Step 2: Clear content directories
    print("\n## Step 2: Clear LLM_BOOK/ content directories")
    clear_content_directories(dry_run)
    results["cleared"] = True

    # Step 3: Discover and ingest content
    staging = discover_staging_folders()

    print("\n## Step 3: Ingest Nyquist content")
    results["nyquist"] = ingest_nyquist_content(staging["nyquist"], dry_run)

    print("\n## Step 4: Ingest R&D content")
    results["rnd"] = ingest_rnd_content(staging["rnd"], dry_run)

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Nyquist folders: {results['nyquist'].get('folders', 0)}")
    print(f"  Nyquist files:   {results['nyquist'].get('files', 0)}")
    print(f"  R&D folders:     {results['rnd'].get('folders', 0)}")
    print(f"  R&D files:       {results['rnd'].get('files', 0)}")

    total_files = results["nyquist"].get("files", 0) + results["rnd"].get("files", 0)

    if dry_run:
        print(f"\n[DRY RUN] Would ingest {total_files} files total")
        print("Run with --ingest (no --dry-run) to apply changes")
    else:
        print(f"\n[OK] Ingested {total_files} files")

    return results


def main():
    parser = argparse.ArgumentParser(
        description="NotebookLM STAGING → LLM_BOOK Ingestion",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py ingest.py                    # Show status report
  py ingest.py --ingest           # Perform ingestion
  py ingest.py --ingest --dry-run # Preview changes
  py ingest.py --ingest --skip-archive  # Skip archiving (dangerous!)
        """
    )

    parser.add_argument("--ingest", action="store_true",
                        help="Perform ingestion (default: report only)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")
    parser.add_argument("--skip-archive", action="store_true",
                        help="Skip archiving step (dangerous - may lose data!)")
    parser.add_argument("--json", action="store_true",
                        help="Output as JSON instead of text")

    args = parser.parse_args()

    if not args.ingest:
        # Report mode
        print(generate_report())
    else:
        # Ingestion mode
        results = perform_ingestion(
            dry_run=args.dry_run,
            skip_archive=args.skip_archive
        )

        if args.json:
            print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
