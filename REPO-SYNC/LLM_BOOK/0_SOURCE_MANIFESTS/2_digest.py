#!/usr/bin/env python3
"""
digest.py - Curate NotebookLM content from STAGING to LLM_BOOK/ structure
=========================================================================
Routes NotebookLM outputs directly from STAGING/_IN folders to appropriate
LLM_BOOK directories based on file type and content.

ACCUMULATIVE MODEL:
-------------------
Reads ALL REVIEW_NOTES_*.md files in 1_VALIDATION/ to understand what's been
reviewed. Media files route directly from STAGING (source of truth), not from
1_VALIDATION (which only holds review notes).

WORKFLOW POSITION:
------------------
STAGING/_IN/ → ingest.py (creates REVIEW_NOTES_*.md) → Claude reviews →
digest.py (routes from STAGING) → LLM_BOOK/{2-7}_*/ → 1_sync_llmbook.py → packages/

USAGE:
------
py digest.py                    # Report mode - show what would happen
py digest.py --digest           # Actually perform digestion (copy files)
py digest.py --digest --dry-run # Preview without changes
py digest.py --batch Nyquist_1  # Only digest specific batch

ROUTING RULES:
--------------
By file extension (routes from STAGING/_IN/):
- .png, .jpg, .jpeg, .gif, .svg  → 3_VISUALS/
- .m4a, .mp3, .wav, .mp4         → 4_AUDIO/

By filename patterns (for .md/.pdf):
- 2_PUBLICATIONS/academic/       : "Technical Report", "Empirical", "Analysis", "Framework"
- 2_PUBLICATIONS/popular_science/: "Engineer's Toolkit", "Charting", "How to"
- 2_PUBLICATIONS/education/      : "Guide", "Student", "Learner", "Glossary", "Visual Guide"
- 2_PUBLICATIONS/policy/         : "Briefing", "Brief", "Policy"
- 2_PUBLICATIONS/funding/        : "Proposal", "Project", "Grant"
- 2_PUBLICATIONS/media/          : "Paradigm", "New Era", "Press", "TED"

Author: LLM_BOOK Digestion Pipeline
Version: 2.0 (2025-12-29) - Accumulative model, routes from STAGING
"""

import argparse
import json
import shutil
import re
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional

# === PATH CONSTANTS ===
SCRIPT_DIR = Path(__file__).parent
LLM_BOOK_DIR = SCRIPT_DIR.parent  # REPO-SYNC/LLM_BOOK/
STAGING_DIR = SCRIPT_DIR / "STAGING"  # Source of truth for media files
VALIDATION_DIR = LLM_BOOK_DIR / "1_VALIDATION"
PUBLICATIONS_DIR = LLM_BOOK_DIR / "2_PUBLICATIONS"
VISUALS_DIR = LLM_BOOK_DIR / "3_VISUALS"
AUDIO_DIR = LLM_BOOK_DIR / "4_AUDIO"

# Marker file indicating a batch has been ingested
INGESTED_MARKER = ".ingested"

# Publication categories (subdirectories of 2_PUBLICATIONS/)
PUBLICATION_CATEGORIES = [
    "academic",
    "popular_science",
    "education",
    "policy",
    "funding",
    "media",
]

# Top-level content categories (non-publication)
CONTENT_CATEGORIES = [
    "visuals",    # 3_VISUALS/
    "audio",      # 4_AUDIO/
]

# All categories for reporting
ALL_CATEGORIES = PUBLICATION_CATEGORIES + CONTENT_CATEGORIES

# === CLASSIFICATION RULES ===
# Priority order: first match wins
# Each rule: (category, patterns) where patterns are case-insensitive regex

CLASSIFICATION_RULES = [
    # Funding - very specific patterns (check first)
    ("funding", [
        r"proposal",
        r"project\s+nyquist",
        r"grant",
        r"funding",
        r"phase\s+of\s+research",
    ]),

    # Policy - briefing documents
    ("policy", [
        r"briefing\s+document",
        r"briefing",
        r"policy\s+brief",
        r"executive\s+summary",
    ]),

    # Education - learning materials
    ("education", [
        r"student'?s?\s+guide",
        r"learner'?s?\s+glossary",
        r"visual\s+guide",
        r"five\s+discoveries",
        r"beginner'?s?\s+guide",
        r"study\s+guide",
        r"quiz",
        r"flashcard",
    ]),

    # Popular science - accessible narratives
    ("popular_science", [
        r"engineer'?s?\s+toolkit",
        r"charting\s+personality",
        r"how\s+to",
        r"simple\s+guide",
    ]),

    # Media - press-ready content
    ("media", [
        r"new\s+paradigm",
        r"new\s+era",
        r"press",
        r"ted\s+talk",
        r"measuring\s+and\s+engineering",
    ]),

    # Academic - technical/empirical (default for formal papers)
    ("academic", [
        r"technical\s+report",
        r"empirical\s+analysis",
        r"empirical\s+framework",
        r"comparative\s+analysis",
        r"dynamical\s+system",
        r"scholarly",
        r"monograph",
    ]),
]

# Default category for files that don't match any rule
DEFAULT_CATEGORY = "academic"

# File extension mappings (checked before pattern matching)
EXTENSION_ROUTING = {
    # Visual files → 3_VISUALS/
    ".png": "visuals",
    ".jpg": "visuals",
    ".jpeg": "visuals",
    ".gif": "visuals",
    ".svg": "visuals",
    ".webp": "visuals",
    # Audio/video files → 4_AUDIO/
    ".m4a": "audio",
    ".mp3": "audio",
    ".wav": "audio",
    ".mp4": "audio",
    ".webm": "audio",
}

# Files to skip (not content)
SKIP_PATTERNS = [
    r"^README\.md$",
    r"^REVIEW_NOTES.*\.md$",  # Review notes stay in 1_VALIDATION/
    r"^\.ingested$",          # Marker files
]


def discover_ingested_batches() -> List[str]:
    """
    Discover all ingested batch names from STAGING/.

    Returns list of batch names (folder names with .ingested marker).
    """
    batches = []

    if not STAGING_DIR.exists():
        return batches

    for folder in STAGING_DIR.iterdir():
        if folder.is_dir() and (folder / INGESTED_MARKER).exists():
            batches.append(folder.name)

    return sorted(batches)


def discover_review_notes() -> List[Path]:
    """
    Discover all REVIEW_NOTES_*.md files in 1_VALIDATION/.

    Returns list of review notes files (accumulative model).
    """
    if not VALIDATION_DIR.exists():
        return []

    return sorted(VALIDATION_DIR.glob("REVIEW_NOTES_*.md"))


def discover_staging_content(batch_name: Optional[str] = None) -> Dict[str, List[Path]]:
    """
    Discover all content in STAGING/_IN folders (source of truth).

    Args:
        batch_name: If specified, only scan that batch folder

    Returns:
        {
            "academic": [Path(...), ...],
            "education": [Path(...), ...],
            "visuals": [Path(...), ...],
            "audio": [Path(...), ...],
            ...
        }
    """
    result = {cat: [] for cat in ALL_CATEGORIES}
    result["_skip"] = []
    result["_unknown"] = []

    if not STAGING_DIR.exists():
        return result

    # Determine which folders to scan
    if batch_name:
        folders_to_scan = [STAGING_DIR / batch_name]
    else:
        # Scan all ingested batches
        folders_to_scan = [
            STAGING_DIR / name for name in discover_ingested_batches()
        ]

    for folder in folders_to_scan:
        in_folder = folder / "_IN"
        if not in_folder.exists():
            continue

        for item in in_folder.iterdir():
            if not item.is_file():
                continue

            category, _ = classify_file(item.name)

            if category in result:
                result[category].append(item)
            elif category == "_skip":
                result["_skip"].append(item)
            else:
                result["_unknown"].append(item)

    return result


def classify_file(filename: str) -> Tuple[str, Optional[str]]:
    """
    Classify a file into a category.

    Returns:
        (category, matched_pattern) - category name and the pattern that matched
    """
    # Check skip patterns first
    for pattern in SKIP_PATTERNS:
        if re.search(pattern, filename, re.IGNORECASE):
            return ("_skip", pattern)

    # Check extension routing (visuals, audio)
    ext = Path(filename).suffix.lower()
    if ext in EXTENSION_ROUTING:
        return (EXTENSION_ROUTING[ext], f"extension:{ext}")

    # Check classification rules in priority order (for .md/.pdf)
    for category, patterns in CLASSIFICATION_RULES:
        for pattern in patterns:
            if re.search(pattern, filename, re.IGNORECASE):
                return (category, pattern)

    # Default classification for .md and .pdf files
    if filename.lower().endswith(('.md', '.pdf')):
        return (DEFAULT_CATEGORY, "_default")

    # Unknown file types
    return ("_unknown", None)




def get_target_dir(category: str) -> Path:
    """Get target directory for a category."""
    if category in PUBLICATION_CATEGORIES:
        return PUBLICATIONS_DIR / category
    elif category == "visuals":
        return VISUALS_DIR
    elif category == "audio":
        return AUDIO_DIR
    else:
        return PUBLICATIONS_DIR / "academic"  # default


def ensure_category_dirs():
    """Create all category directories if they don't exist."""
    # Publication subcategories
    for category in PUBLICATION_CATEGORIES:
        cat_dir = PUBLICATIONS_DIR / category
        cat_dir.mkdir(parents=True, exist_ok=True)

    # Top-level content directories
    VISUALS_DIR.mkdir(parents=True, exist_ok=True)
    AUDIO_DIR.mkdir(parents=True, exist_ok=True)


def copy_file_to_category(source: Path, category: str, dry_run: bool = True) -> bool:
    """
    Copy a file to its category directory.

    Returns True if successful.
    """
    target_dir = get_target_dir(category)
    target_path = target_dir / source.name

    if dry_run:
        print(f"  [DRY RUN] {source.name} -> {category}/")
        return True

    target_dir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target_path)
    print(f"  [OK] {source.name} -> {category}/")
    return True


def generate_report(batch_name: Optional[str] = None) -> str:
    """Generate status report of staging content classification."""
    content = discover_staging_content(batch_name)
    review_notes = discover_review_notes()
    ingested_batches = discover_ingested_batches()

    lines = [
        "=" * 60,
        "LLM_BOOK DIGEST STATUS (Accumulative Model)",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        f"Source: {STAGING_DIR}/_IN folders",
        "",
        "## Ingested Batches",
    ]

    if ingested_batches:
        for batch in ingested_batches:
            lines.append(f"  - {batch}")
    else:
        lines.append("  (none - run ingest.py first)")

    lines.extend([
        "",
        "## Review Notes (1_VALIDATION/)",
    ])

    if review_notes:
        for rn in review_notes:
            lines.append(f"  - {rn.name}")
    else:
        lines.append("  (none found)")

    lines.extend([
        "",
        "Target directories:",
        f"  2_PUBLICATIONS/ - Text content by audience",
        f"  3_VISUALS/      - Images and diagrams",
        f"  4_AUDIO/        - Audio and video files",
        "",
    ])

    total_files = 0

    # Report publication categories
    lines.append("## PUBLICATIONS (2_PUBLICATIONS/)")
    for category in PUBLICATION_CATEGORIES:
        files = content.get(category, [])
        if files:
            lines.append(f"  ### {category}/ ({len(files)} files)")
            for f in files:
                _, pattern = classify_file(f.name)
                lines.append(f"    - {f.name}")
                lines.append(f"      (matched: {pattern})")
            total_files += len(files)
    lines.append("")

    # Report content categories (visuals, audio)
    for category in CONTENT_CATEGORIES:
        files = content.get(category, [])
        if files:
            target_name = "3_VISUALS" if category == "visuals" else "4_AUDIO"
            lines.append(f"## {target_name}/ ({len(files)} files)")
            for f in files:
                _, pattern = classify_file(f.name)
                lines.append(f"  - {f.name}")
                lines.append(f"    (matched: {pattern})")
            lines.append("")
            total_files += len(files)

    # Report skipped
    skipped = content.get("_skip", [])
    if skipped:
        lines.append(f"## SKIPPED ({len(skipped)} files)")
        for f in skipped:
            lines.append(f"  - {f.name}")
        lines.append("")

    # Report unknown
    unknown = content.get("_unknown", [])
    if unknown:
        lines.append(f"## UNKNOWN (unclassified) ({len(unknown)} files)")
        for f in unknown:
            lines.append(f"  - {f.name}")
        lines.append("")

    lines.extend([
        "=" * 60,
        f"Total routable files: {total_files}",
        f"Skipped: {len(skipped)}",
        f"Unknown: {len(unknown)}",
        "",
        "To perform digestion: py digest.py --digest",
        "To preview changes:   py digest.py --digest --dry-run",
        "To digest one batch:  py digest.py --digest --batch Nyquist_1",
        "=" * 60,
    ])

    return "\n".join(lines)


def perform_digestion(dry_run: bool = True, batch_name: Optional[str] = None) -> Dict:
    """
    Perform digestion: route files from STAGING/_IN to LLM_BOOK/{2-7}_*/.

    Accumulative model:
    - Routes media from STAGING (source of truth), not from 1_VALIDATION
    - Publication content (.md, .pdf) goes to 2_PUBLICATIONS/{category}/
    - Visuals (.png, .jpg, etc.) go to 3_VISUALS/
    - Audio (.m4a, .mp3, .mp4, etc.) goes to 4_AUDIO/

    Args:
        dry_run: If True, only preview changes
        batch_name: If specified, only digest that batch
    """
    results = {
        "timestamp": datetime.now().isoformat(),
        "dry_run": dry_run,
        "batch": batch_name or "all",
        "categories": {},
        "skipped": [],
    }

    print("=" * 60)
    print("LLM_BOOK DIGESTION (Accumulative Model)")
    print(f"Mode: {'DRY RUN' if dry_run else 'COPY'}")
    if batch_name:
        print(f"Batch: {batch_name}")
    print("=" * 60)

    content = discover_staging_content(batch_name)

    # Ensure target directories exist
    if not dry_run:
        ensure_category_dirs()

    # Process publication categories
    for category in PUBLICATION_CATEGORIES:
        files = content.get(category, [])
        if not files:
            continue

        print(f"\n## 2_PUBLICATIONS/{category}/ ({len(files)} files)")
        results["categories"][category] = {"count": len(files), "files": []}

        target_dir = PUBLICATIONS_DIR / category

        for source in files:
            if dry_run:
                print(f"  [DRY RUN] {source.name}")
            else:
                target_path = target_dir / source.name
                shutil.copy2(source, target_path)
                print(f"  [OK] {source.name}")

            results["categories"][category]["files"].append(source.name)

    # Process visuals
    visuals = content.get("visuals", [])
    if visuals:
        print(f"\n## 3_VISUALS/ ({len(visuals)} files)")
        results["categories"]["visuals"] = {"count": len(visuals), "files": []}

        for source in visuals:
            if dry_run:
                print(f"  [DRY RUN] {source.name}")
            else:
                VISUALS_DIR.mkdir(parents=True, exist_ok=True)
                target_path = VISUALS_DIR / source.name
                shutil.copy2(source, target_path)
                print(f"  [OK] {source.name}")

            results["categories"]["visuals"]["files"].append(source.name)

    # Process audio
    audio = content.get("audio", [])
    if audio:
        print(f"\n## 4_AUDIO/ ({len(audio)} files)")
        results["categories"]["audio"] = {"count": len(audio), "files": []}

        for source in audio:
            if dry_run:
                print(f"  [DRY RUN] {source.name}")
            else:
                AUDIO_DIR.mkdir(parents=True, exist_ok=True)
                target_path = AUDIO_DIR / source.name
                shutil.copy2(source, target_path)
                print(f"  [OK] {source.name}")

            results["categories"]["audio"]["files"].append(source.name)

    # Report skipped
    skipped = content.get("_skip", [])
    if skipped:
        print(f"\n## Skipped ({len(skipped)} files)")
        for f in skipped:
            print(f"  - {f.name}")
            results["skipped"].append(f.name)

    # Report unknown
    unknown = content.get("_unknown", [])
    if unknown:
        print(f"\n## Unknown ({len(unknown)} files)")
        for f in unknown:
            print(f"  - {f.name}")
            results["skipped"].append(f.name)

    # Summary
    total_processed = sum(
        len(results["categories"].get(c, {}).get("files", []))
        for c in ALL_CATEGORIES
    )

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    for category in ALL_CATEGORIES:
        count = len(results["categories"].get(category, {}).get("files", []))
        if count > 0:
            if category in PUBLICATION_CATEGORIES:
                print(f"  2_PUBLICATIONS/{category}/: {count} files")
            elif category == "visuals":
                print(f"  3_VISUALS/: {count} files")
            elif category == "audio":
                print(f"  4_AUDIO/: {count} files")

    print(f"  TOTAL: {total_processed} files")
    print(f"  Skipped: {len(results['skipped'])}")

    if dry_run:
        print(f"\n[DRY RUN] Would process {total_processed} files")
        print("Run with --digest (no --dry-run) to apply changes")
    else:
        print(f"\n[OK] Copied {total_processed} files to LLM_BOOK/")

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Curate STAGING/_IN content into LLM_BOOK/ categories (Accumulative Model)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Accumulative Model:
  Routes from STAGING/_IN (source of truth), not from 1_VALIDATION.
  Review notes stay in 1_VALIDATION/ and are synced separately.

Examples:
  py digest.py                      # Show classification report
  py digest.py --digest             # Copy files to categories
  py digest.py --digest --dry-run   # Preview changes
  py digest.py --digest --batch Nyquist_1  # Digest specific batch
        """
    )

    parser.add_argument("--digest", action="store_true",
                        help="Perform digestion (default: report only)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")
    parser.add_argument("--batch", type=str, default=None,
                        help="Only digest specific batch folder")
    parser.add_argument("--json", action="store_true",
                        help="Output as JSON instead of text")

    args = parser.parse_args()

    if not args.digest:
        # Report mode
        print(generate_report(args.batch))
    else:
        # Digestion mode
        results = perform_digestion(
            dry_run=args.dry_run,
            batch_name=args.batch
        )

        if args.json:
            print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
