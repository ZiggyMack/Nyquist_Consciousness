#!/usr/bin/env python3
"""
digest.py - Curate 1_VALIDATION/ content into LLM_BOOK/ structure
==================================================================
Routes ingested NotebookLM outputs from validation staging to appropriate
LLM_BOOK directories based on file type and content.

WORKFLOW POSITION:
------------------
STAGING/ → ingest.py → 1_VALIDATION/ → digest.py → LLM_BOOK/{2-7}_*/ → 1_sync_llmbook.py → packages/

USAGE:
------
py digest.py                    # Report mode - show what would happen
py digest.py --digest           # Actually perform digestion (copy files)
py digest.py --digest --dry-run # Preview without changes
py digest.py --move             # Move instead of copy (clears 1_VALIDATION/)

ROUTING RULES:
--------------
By file extension:
- .png, .jpg, .jpeg, .gif, .svg  → 3_VISUALS/
- .m4a, .mp3, .wav, .mp4         → 7_AUDIO/

By filename patterns (for .md/.pdf):
- 2_PUBLICATIONS/academic/       : "Technical Report", "Empirical", "Analysis", "Framework"
- 2_PUBLICATIONS/popular_science/: "Engineer's Toolkit", "Charting", "How to"
- 2_PUBLICATIONS/education/      : "Guide", "Student", "Learner", "Glossary", "Visual Guide"
- 2_PUBLICATIONS/policy/         : "Briefing", "Brief", "Policy"
- 2_PUBLICATIONS/funding/        : "Proposal", "Project", "Grant"
- 2_PUBLICATIONS/media/          : "Paradigm", "New Era", "Press", "TED"
- 4_DEEP_DIVES/                  : Extended analyses (manual placement)
- 5_FUTURE/                      : Future research (manual placement)
- 6_EXPERIMENTS/                 : Experiment logs (manual placement)

Author: LLM_BOOK Digestion Pipeline
Version: 1.1 (2025-12-29) - Added 3_VISUALS, 7_AUDIO routing
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
VALIDATION_DIR = LLM_BOOK_DIR / "1_VALIDATION"
PUBLICATIONS_DIR = LLM_BOOK_DIR / "2_PUBLICATIONS"
VISUALS_DIR = LLM_BOOK_DIR / "3_VISUALS"
DEEP_DIVES_DIR = LLM_BOOK_DIR / "4_DEEP_DIVES"
FUTURE_DIR = LLM_BOOK_DIR / "5_FUTURE"
EXPERIMENTS_DIR = LLM_BOOK_DIR / "6_EXPERIMENTS"
AUDIO_DIR = LLM_BOOK_DIR / "7_AUDIO"

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
    "audio",      # 7_AUDIO/
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
    # Audio/video files → 7_AUDIO/
    ".m4a": "audio",
    ".mp3": "audio",
    ".wav": "audio",
    ".mp4": "audio",
    ".webm": "audio",
}

# Files to skip (not content)
SKIP_PATTERNS = [
    r"^README\.md$",
]


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


def discover_validation_content() -> Dict[str, List[Path]]:
    """
    Discover all content in 1_VALIDATION/ and classify by category.

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

    if not VALIDATION_DIR.exists():
        return result

    for item in VALIDATION_DIR.rglob("*"):
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


def generate_report() -> str:
    """Generate status report of validation content classification."""
    content = discover_validation_content()

    lines = [
        "=" * 60,
        "LLM_BOOK DIGEST STATUS",
        f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        "=" * 60,
        "",
        f"Source: {VALIDATION_DIR}",
        "",
        "Target directories:",
        f"  2_PUBLICATIONS/ - Text content by audience",
        f"  3_VISUALS/      - Images and diagrams",
        f"  7_AUDIO/        - Audio and video files",
        "",
    ]

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
            target_name = "3_VISUALS" if category == "visuals" else "7_AUDIO"
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
        "=" * 60,
    ])

    return "\n".join(lines)


def perform_digestion(dry_run: bool = True, move: bool = False) -> Dict:
    """
    Perform digestion: route files from 1_VALIDATION/ to 2_PUBLICATIONS/{category}/.

    Args:
        dry_run: If True, only preview changes
        move: If True, move files instead of copying
    """
    results = {
        "timestamp": datetime.now().isoformat(),
        "dry_run": dry_run,
        "move": move,
        "categories": {},
        "skipped": [],
        "assets": [],
    }

    print("=" * 60)
    print("LLM_BOOK DIGESTION")
    print(f"Mode: {'DRY RUN' if dry_run else ('MOVE' if move else 'COPY')}")
    print("=" * 60)

    content = discover_validation_content()

    # Ensure target directories exist
    if not dry_run:
        ensure_category_dirs()

    # Process each category
    for category in CATEGORIES:
        files = content.get(category, [])
        if not files:
            continue

        print(f"\n## {category}/ ({len(files)} files)")
        results["categories"][category] = {"count": len(files), "files": []}

        for source in files:
            if dry_run:
                print(f"  [DRY RUN] {source.name}")
                results["categories"][category]["files"].append(source.name)
            else:
                target_dir = PUBLICATIONS_DIR / category
                target_path = target_dir / source.name

                if move:
                    shutil.move(str(source), str(target_path))
                    print(f"  [MOVED] {source.name}")
                else:
                    shutil.copy2(source, target_path)
                    print(f"  [COPIED] {source.name}")

                results["categories"][category]["files"].append(source.name)

    # Handle assets - copy to same category as related .md file
    assets = content.get("_asset", [])
    if assets:
        print(f"\n## Assets ({len(assets)} files)")
        for asset in assets:
            # Find what category the parent .md files went to
            parent_dir = asset.parent
            # Check if any .md file in same dir was classified
            sibling_mds = list(parent_dir.glob("*.md"))
            target_category = None

            for md in sibling_mds:
                if md.name.lower() != "readme.md":
                    cat, _ = classify_file(md.name)
                    if cat in CATEGORIES:
                        target_category = cat
                        break

            if target_category:
                if dry_run:
                    print(f"  [DRY RUN] {asset.name} -> {target_category}/ (follows siblings)")
                else:
                    target_dir = PUBLICATIONS_DIR / target_category
                    target_path = target_dir / asset.name

                    if move:
                        shutil.move(str(asset), str(target_path))
                    else:
                        shutil.copy2(asset, target_path)

                    print(f"  [{'MOVED' if move else 'COPIED'}] {asset.name} -> {target_category}/")
                results["assets"].append({"file": asset.name, "category": target_category})
            else:
                print(f"  [SKIP] {asset.name} (no category determined)")
                results["assets"].append({"file": asset.name, "category": None})

    # Report skipped
    skipped = content.get("_skip", [])
    if skipped:
        print(f"\n## Skipped ({len(skipped)} files)")
        for f in skipped:
            print(f"  - {f.name}")
            results["skipped"].append(f.name)

    # Summary
    total_processed = sum(len(results["categories"].get(c, {}).get("files", [])) for c in CATEGORIES)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    for category in CATEGORIES:
        count = len(results["categories"].get(category, {}).get("files", []))
        if count > 0:
            print(f"  {category}: {count} files")
    print(f"  TOTAL: {total_processed} files")
    print(f"  Skipped: {len(results['skipped'])}")

    if dry_run:
        print(f"\n[DRY RUN] Would process {total_processed} files")
        print("Run with --digest (no --dry-run) to apply changes")
    else:
        action = "moved" if move else "copied"
        print(f"\n[OK] {action.title()} {total_processed} files to 2_PUBLICATIONS/")

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Curate 1_VALIDATION/ content into 2_PUBLICATIONS/ categories",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py digest.py                    # Show classification report
  py digest.py --digest           # Copy files to categories
  py digest.py --digest --dry-run # Preview changes
  py digest.py --digest --move    # Move files (clears source)
        """
    )

    parser.add_argument("--digest", action="store_true",
                        help="Perform digestion (default: report only)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Preview changes without applying")
    parser.add_argument("--move", action="store_true",
                        help="Move files instead of copying")
    parser.add_argument("--json", action="store_true",
                        help="Output as JSON instead of text")

    args = parser.parse_args()

    if not args.digest:
        # Report mode
        print(generate_report())
    else:
        # Digestion mode
        results = perform_digestion(
            dry_run=args.dry_run,
            move=args.move
        )

        if args.json:
            print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
