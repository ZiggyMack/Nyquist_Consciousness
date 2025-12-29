#!/usr/bin/env python3
"""
ingest.py - NotebookLM STAGING → LLM_BOOK Ingestion (Accumulative Model)
=========================================================================
Processes NotebookLM outputs from STAGING/ into the LLM_BOOK/ structure.

ACCUMULATIVE MODEL:
-------------------
By default, ingestion APPENDS to existing content, compounding value over time.
Each ingestion batch gets its own REVIEW_NOTES_{batch}.md file.
Use --fresh to clear everything and start over (destructive).

WORKFLOW:
---------
1. Discover un-ingested batches in STAGING/ (folders without .ingested marker)
2. For each Nyquist batch:
   - Create placeholder REVIEW_NOTES_{batch}.md in 1_VALIDATION/
   - Mark batch as ingested (create .ingested marker)
3. For R&D content: append to RnD/{topic}/
4. Claude reviews and fills in REVIEW_NOTES_{batch}.md
5. digest.py reads ALL REVIEW_NOTES_*.md and routes content accordingly

USAGE:
------
py ingest.py                    # Report mode - show staging status
py ingest.py --ingest           # Append mode (default) - add new batches
py ingest.py --ingest --full    # Full mode - also create analysis stubs
py ingest.py --ingest --fresh   # Fresh mode - clear all, then ingest
py ingest.py --ingest --dry-run # Preview without changes

REVIEW NOTES NAMING:
--------------------
Each batch gets: REVIEW_NOTES_{batch_name}.md
- REVIEW_NOTES_Nyquist_1.md
- REVIEW_NOTES_Nyquist_2.md
- REVIEW_NOTES_Nyquist_1_2.md  (combined review)

POST-INGESTION:
---------------
Ask Claude to review new content in 1_VALIDATION/:
"Please review STAGING/Nyquist_X/_IN/ and create REVIEW_NOTES_Nyquist_X.md"

Then run: py digest.py --digest

Author: LLM_BOOK Ingestion Pipeline
Version: 3.0 (2025-12-29) - Accumulative model with batch tracking
"""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional

# === PATH CONSTANTS ===
SCRIPT_DIR = Path(__file__).parent
LLM_BOOK_DIR = SCRIPT_DIR.parent  # REPO-SYNC/LLM_BOOK/
STAGING_DIR = SCRIPT_DIR / "STAGING"
REPO_ROOT = LLM_BOOK_DIR.parent.parent  # d:\Documents\Nyquist_Consciousness
WHITE_PAPER_DIR = REPO_ROOT / "WHITE-PAPER"
SYNC_SCRIPT = WHITE_PAPER_DIR / "calibration" / "1_sync_llmbook.py"
VERSION_FILE = WHITE_PAPER_DIR / "reviewers" / "packages" / "CURRENT_VERSION.json"

# Validation directory for review notes
VALIDATION_DIR = LLM_BOOK_DIR / "1_VALIDATION"

# LLM_BOOK content directories (only cleared with --fresh)
CONTENT_DIRS = [
    VALIDATION_DIR,
    LLM_BOOK_DIR / "2_PUBLICATIONS",
    LLM_BOOK_DIR / "3_VISUALS",
    LLM_BOOK_DIR / "4_AUDIO",
    LLM_BOOK_DIR / "RnD",
]

# Validation subdirectories for --full mode analysis
VALIDATION_ANALYSIS_DIRS = [
    VALIDATION_DIR / "1_DEEP_DIVES",
    VALIDATION_DIR / "2_FUTURE",
    VALIDATION_DIR / "3_EXPERIMENTS",
]

# Directories to preserve (never cleared)
PRESERVE_DIRS = [
    LLM_BOOK_DIR / "0_SOURCE_MANIFESTS",  # Contains STAGING and this script
]

# Marker file indicating a batch has been ingested
INGESTED_MARKER = ".ingested"


def get_version_info() -> Dict:
    """Read CURRENT_VERSION.json for review status and version info."""
    if VERSION_FILE.exists():
        with open(VERSION_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {"current_version": "unknown", "review_status": "unknown"}


def is_nyquist_content(folder_name: str) -> bool:
    """Determine if a staging folder contains Nyquist-specific content."""
    nyquist_keywords = ["nyquist", "infinity-nyquist"]
    return any(kw in folder_name.lower() for kw in nyquist_keywords)


def get_rnd_topic_name(folder_name: str) -> str:
    """Normalize R&D folder names for consistent directory structure."""
    if folder_name.lower().startswith("gnostic"):
        return "Gnostic"
    return folder_name.replace("-", "_").replace(" ", "_")


def is_batch_ingested(folder: Path) -> bool:
    """Check if a staging folder has already been ingested."""
    return (folder / INGESTED_MARKER).exists()


def mark_batch_ingested(folder: Path, dry_run: bool = True) -> None:
    """Mark a staging folder as ingested."""
    marker = folder / INGESTED_MARKER
    if not dry_run:
        marker.write_text(f"Ingested: {datetime.now().isoformat()}\n")


def discover_staging_folders() -> Dict[str, List[Tuple[Path, bool]]]:
    """
    Discover all content in STAGING/ and classify by type.

    Returns:
        {
            "nyquist": [(Path, is_ingested), ...],
            "rnd": [(Path, is_ingested), ...]
        }
    """
    result = {"nyquist": [], "rnd": []}

    if not STAGING_DIR.exists():
        return result

    for item in STAGING_DIR.iterdir():
        if not item.is_dir():
            continue

        ingested = is_batch_ingested(item)

        if is_nyquist_content(item.name):
            result["nyquist"].append((item, ingested))
        else:
            result["rnd"].append((item, ingested))

    return result


def get_pending_batches(staging: Dict) -> Dict[str, List[Path]]:
    """Filter to only un-ingested batches."""
    return {
        "nyquist": [p for p, ingested in staging["nyquist"] if not ingested],
        "rnd": [p for p, ingested in staging["rnd"] if not ingested],
    }


def create_review_notes_template(batch_name: str, source_folder: Path, dry_run: bool = True) -> Path:
    """
    Create a review notes template for a batch.

    Returns the path to the created file.
    """
    # List files in the _IN folder
    in_folder = source_folder / "_IN"
    files = []
    if in_folder.exists():
        files = [f.name for f in in_folder.iterdir() if f.is_file()]

    # Generate template
    template = f"""# Review Notes: {batch_name}

**Ingestion Date:** {datetime.now().strftime('%Y-%m-%d')}
**Source:** STAGING/{batch_name}/_IN/
**Status:** PENDING REVIEW

---

## Files to Review

"""
    # Add file list
    for f in sorted(files):
        ext = Path(f).suffix.lower()
        if ext == ".md":
            template += f"### {f}\n- **Category:** `pending`\n- **Accuracy:** PENDING\n- **Verdict:** PENDING\n\n"
        elif ext in [".png", ".jpg", ".jpeg", ".gif"]:
            template += f"### {f}\n- **Type:** Visual\n- **Route to:** 3_VISUALS/\n\n"
        elif ext in [".m4a", ".mp3", ".mp4", ".wav"]:
            template += f"### {f}\n- **Type:** Audio/Video\n- **Route to:** 7_AUDIO/\n\n"
        elif ext == ".pdf":
            template += f"### {f}\n- **Type:** PDF\n- **Route to:** 2_PUBLICATIONS/academic/\n\n"
        else:
            template += f"### {f}\n- **Type:** Other ({ext})\n- **Route to:** TBD\n\n"

    template += """---

## Review Summary

| File | Category | Verdict | Notes |
|------|----------|---------|-------|
| ... | ... | ... | ... |

---

## Claude's Assessment

**Quality:** PENDING
**Accuracy:** PENDING
**Recommendation:** PENDING

---

*This file is part of the reviewer feedback loop.*
*Created by ingest.py on {date}*
*Review status: PENDING*
""".format(date=datetime.now().strftime('%Y-%m-%d'))

    # Write file
    target_path = VALIDATION_DIR / f"REVIEW_NOTES_{batch_name}.md"

    if not dry_run:
        VALIDATION_DIR.mkdir(parents=True, exist_ok=True)
        target_path.write_text(template, encoding="utf-8")

    return target_path


def create_analysis_stubs(batch_name: str, dry_run: bool = True) -> List[Path]:
    """Create stub files for --full mode analysis directories."""
    created = []

    for analysis_dir in VALIDATION_ANALYSIS_DIRS:
        stub_path = analysis_dir / f"{batch_name}.md"

        if not dry_run:
            analysis_dir.mkdir(parents=True, exist_ok=True)
            stub_path.write_text(f"# {analysis_dir.name}: {batch_name}\n\n*Pending --full analysis*\n")

        created.append(stub_path)

    return created


def copy_folder_contents(source: Path, target: Path, dry_run: bool = True) -> int:
    """Copy contents of source folder to target. Returns file count."""
    if not source.exists():
        return 0

    file_count = 0

    for item in source.rglob("*"):
        if item.is_file():
            rel_path = item.relative_to(source)
            target_path = target / rel_path

            if not dry_run:
                target_path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(item, target_path)

            file_count += 1

    return file_count


def ingest_rnd_content(folders: List[Path], dry_run: bool = True) -> Dict:
    """Ingest R&D content into RnD/ directory (append mode)."""
    result = {"folders": 0, "files": 0, "details": []}

    rnd_dir = LLM_BOOK_DIR / "RnD"

    for folder in folders:
        topic_name = get_rnd_topic_name(folder.name)
        target = rnd_dir / topic_name

        file_count = copy_folder_contents(folder, target, dry_run)

        if file_count > 0:
            result["folders"] += 1
            result["files"] += file_count
            result["details"].append({
                "source": folder.name,
                "target": f"RnD/{topic_name}",
                "files": file_count
            })

            # Mark as ingested
            mark_batch_ingested(folder, dry_run)

            action = "[DRY RUN]" if dry_run else "[OK]"
            print(f"  {action} {folder.name} -> RnD/{topic_name} ({file_count} files)")

    return result


def clear_content_directories(dry_run: bool = True) -> None:
    """Clear LLM_BOOK content directories (for --fresh mode)."""
    for content_dir in CONTENT_DIRS:
        if not content_dir.exists():
            continue

        files = list(content_dir.rglob("*"))
        file_count = sum(1 for f in files if f.is_file())

        action = "[DRY RUN]" if dry_run else "[OK]"

        if not dry_run:
            for item in content_dir.iterdir():
                if item.is_file():
                    item.unlink()
                elif item.is_dir():
                    shutil.rmtree(item)

        print(f"  {action} Cleared {content_dir.name}/ ({file_count} files)")


def clear_ingestion_markers(dry_run: bool = True) -> int:
    """Clear all .ingested markers (for --fresh mode). Returns count."""
    count = 0

    if not STAGING_DIR.exists():
        return 0

    for folder in STAGING_DIR.iterdir():
        if folder.is_dir():
            marker = folder / INGESTED_MARKER
            if marker.exists():
                if not dry_run:
                    marker.unlink()
                count += 1

    return count


def generate_report() -> str:
    """Generate status report of STAGING contents."""
    staging = discover_staging_folders()
    pending = get_pending_batches(staging)

    lines = [
        "=" * 60,
        "LLM_BOOK INGESTION STATUS (Accumulative Model)",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        f"STAGING location: {STAGING_DIR}",
        "",
    ]

    # Nyquist content
    lines.append("## Nyquist Content (-> publication pipeline)")
    if staging["nyquist"]:
        for folder, ingested in staging["nyquist"]:
            in_folder = folder / "_IN"
            status = "[*] INGESTED" if ingested else "[ ] PENDING"
            if in_folder.exists():
                file_count = sum(1 for f in in_folder.rglob("*") if f.is_file())
                lines.append(f"  {status} {folder.name}/_IN ({file_count} files)")
            else:
                lines.append(f"  {status} {folder.name} (no _IN subfolder)")
    else:
        lines.append("  (none found)")

    lines.append("")

    # R&D content
    lines.append("## R&D Content (-> RnD/ directory)")
    if staging["rnd"]:
        for folder, ingested in staging["rnd"]:
            status = "[*] INGESTED" if ingested else "[ ] PENDING"
            file_count = sum(1 for f in folder.rglob("*") if f.is_file())
            topic = get_rnd_topic_name(folder.name)
            lines.append(f"  {status} {folder.name} -> RnD/{topic} ({file_count} files)")
    else:
        lines.append("  (none found)")

    lines.append("")

    # Existing review notes
    lines.append("## Existing Review Notes")
    review_notes = list(VALIDATION_DIR.glob("REVIEW_NOTES_*.md"))
    if review_notes:
        for rn in sorted(review_notes):
            lines.append(f"  - {rn.name}")
    else:
        lines.append("  (none found)")

    # Summary
    pending_nyquist = len(pending["nyquist"])
    pending_rnd = len(pending["rnd"])

    lines.extend([
        "",
        "=" * 60,
        f"Pending ingestion: {pending_nyquist} Nyquist + {pending_rnd} R&D batches",
        "",
        "Commands:",
        "  py ingest.py --ingest           # Ingest pending batches (append)",
        "  py ingest.py --ingest --fresh   # Clear all and re-ingest",
        "  py ingest.py --ingest --dry-run # Preview changes",
        "=" * 60,
    ])

    return "\n".join(lines)


def perform_ingestion(dry_run: bool = True, fresh: bool = False, full: bool = False,
                      force: bool = False, batches: List[str] = None) -> Dict:
    """
    Perform ingestion workflow.

    Args:
        dry_run: Preview without making changes
        fresh: Clear everything first (destructive)
        full: Create analysis stubs in 1_DEEP_DIVES, 2_FUTURE, 3_EXPERIMENTS
        force: Re-process batches even if already ingested
        batches: Specific batch names to process (None = all pending)
    """
    results = {
        "timestamp": datetime.now().isoformat(),
        "dry_run": dry_run,
        "fresh": fresh,
        "full": full,
        "force": force,
        "batches_filter": batches,
        "nyquist": {"batches": [], "review_notes": []},
        "rnd": {},
    }

    mode_str = "DRY RUN" if dry_run else "APPLYING"
    fresh_str = " (FRESH)" if fresh else " (APPEND)"
    force_str = " --force" if force else ""
    batch_str = f" --batch {' '.join(batches)}" if batches else ""

    print("=" * 60)
    print(f"LLM_BOOK INGESTION - {mode_str}{fresh_str}{force_str}{batch_str}")
    print("=" * 60)

    # Fresh mode: clear everything first
    if fresh:
        print("\n## Step 1: Clear existing content (--fresh)")
        clear_content_directories(dry_run)
        markers_cleared = clear_ingestion_markers(dry_run)
        print(f"  Cleared {markers_cleared} ingestion markers")
        results["cleared"] = True
    else:
        print("\n## Step 1: Append mode - preserving existing content")
        results["cleared"] = False

    # Discover batches
    staging = discover_staging_folders()

    # Determine which batches to process
    if fresh:
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"]],
            "rnd": [p for p, _ in staging["rnd"]],
        }
    elif force and batches:
        # Force mode with specific batches: process those regardless of .ingested
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"] if p.name in batches],
            "rnd": [p for p, _ in staging["rnd"] if p.name in batches],
        }
    elif force:
        # Force mode without batch filter: process ALL batches
        pending = {
            "nyquist": [p for p, _ in staging["nyquist"]],
            "rnd": [p for p, _ in staging["rnd"]],
        }
    else:
        # Normal append mode: only pending batches
        pending = get_pending_batches(staging)
        if batches:
            # Filter to specified batches
            pending = {
                "nyquist": [p for p in pending["nyquist"] if p.name in batches],
                "rnd": [p for p in pending["rnd"] if p.name in batches],
            }

    # Ingest Nyquist batches
    print("\n## Step 2: Process Nyquist batches")
    if pending["nyquist"]:
        for folder in pending["nyquist"]:
            batch_name = folder.name

            # Create review notes template
            rn_path = create_review_notes_template(batch_name, folder, dry_run)
            results["nyquist"]["review_notes"].append(str(rn_path))

            action = "[DRY RUN]" if dry_run else "[OK]"
            print(f"  {action} Created REVIEW_NOTES_{batch_name}.md")

            # Create analysis stubs if --full
            if full:
                stubs = create_analysis_stubs(batch_name, dry_run)
                print(f"  {action} Created {len(stubs)} analysis stubs")

            # Mark as ingested
            mark_batch_ingested(folder, dry_run)
            results["nyquist"]["batches"].append(batch_name)
    else:
        print("  No pending Nyquist batches")

    # Ingest R&D content
    print("\n## Step 3: Process R&D content")
    if pending["rnd"]:
        results["rnd"] = ingest_rnd_content(pending["rnd"], dry_run)
    else:
        print("  No pending R&D batches")

    # Summary
    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Nyquist batches processed: {len(results['nyquist']['batches'])}")
    print(f"  Review notes created:      {len(results['nyquist']['review_notes'])}")
    print(f"  R&D folders processed:     {results['rnd'].get('folders', 0)}")
    print(f"  R&D files copied:          {results['rnd'].get('files', 0)}")

    if dry_run:
        print("\n[DRY RUN] No changes made. Run without --dry-run to apply.")
    else:
        print("\n[OK] Ingestion complete!")
        if results["nyquist"]["batches"]:
            print("\nNext steps:")
            for batch in results["nyquist"]["batches"]:
                print(f"  1. Review STAGING/{batch}/_IN/ content")
                print(f"  2. Fill in 1_VALIDATION/REVIEW_NOTES_{batch}.md")
            print("  3. Run: py digest.py --digest")

    return results


def main():
    parser = argparse.ArgumentParser(
        description="NotebookLM STAGING → LLM_BOOK Ingestion (Accumulative Model)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Accumulative Model:
  By default, ingestion APPENDS to existing content.
  Each batch gets its own REVIEW_NOTES_{batch}.md file.
  Use --fresh to clear everything and start over.

Examples:
  py ingest.py                    # Show staging status
  py ingest.py --ingest           # Ingest pending batches (append)
  py ingest.py --ingest --full    # Also create analysis stubs
  py ingest.py --ingest --fresh   # Clear all, then ingest
  py ingest.py --ingest --dry-run # Preview changes
  py ingest.py --ingest --full --force --batch Nyquist_1 Nyquist_2  # Re-ingest specific batches
        """
    )

    parser.add_argument("--ingest", action="store_true",
                        help="Perform ingestion (default: report only)")
    parser.add_argument("--fresh", action="store_true",
                        help="Clear all content before ingesting (destructive!)")
    parser.add_argument("--full", action="store_true",
                        help="Create analysis stubs in DEEP_DIVES, FUTURE, EXPERIMENTS")
    parser.add_argument("--force", action="store_true",
                        help="Re-process batches even if already ingested")
    parser.add_argument("--batch", type=str, nargs='+', default=None,
                        help="Process specific batch folder(s)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")
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
            fresh=args.fresh,
            full=args.full,
            force=args.force,
            batches=args.batch
        )

        if args.json:
            print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
