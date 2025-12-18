#!/usr/bin/env python3
"""
Add FROSTY_MANIFEST to README.md and START_HERE.md files.

This utility scans the repository and adds FROSTY_MANIFEST headers
to all README.md and START_HERE.md files that don't already have them.

USAGE:
    py REPO-SYNC/add_frosty_manifests.py              # Report mode (no changes)
    py REPO-SYNC/add_frosty_manifests.py --apply      # Apply changes
    py REPO-SYNC/add_frosty_manifests.py --dir S7_ARMADA  # Specific directory
    py REPO-SYNC/add_frosty_manifests.py --priority   # Only high-priority files
    py REPO-SYNC/add_frosty_manifests.py --check-stale    # Check for stale/outdated files
    py REPO-SYNC/add_frosty_manifests.py --flag-update FILE  # Flag a file as needing update
    py REPO-SYNC/add_frosty_manifests.py --clear-update FILE # Clear update flag after updating

MANIFEST FORMAT:
    <!-- FROSTY_MANIFEST
    last_reviewed: 2025-12-17
    needs_update: false
    update_reason: null
    depends_on:
      - relative/path/to/dependency.py
    impacts:
      - relative/path/to/impacted.md
    keywords:
      - relevant_keyword
    -->

Author: Claude (Nyquist Framework)
Date: December 17, 2025
"""

import os
import re
import argparse
from datetime import datetime
from pathlib import Path
from typing import List, Set, Optional, Tuple

# =============================================================================
# CONFIGURATION
# =============================================================================

REPO_ROOT = Path(__file__).parent.parent

TARGET_FILES = ["README.md", "START_HERE.md"]

# High priority directories (process first)
PRIORITY_DIRS = [
    "WHITE-PAPER",
    "experiments/temporal_stability/S7_ARMADA",
    "docs/maps",
    "dashboard",
]

# Skip these directories
SKIP_DIRS = {
    ".git", ".vscode", "__pycache__", "node_modules",
    ".archive", "archive", ".backup",
}

# Skip these files (already have manifests or are special)
SKIP_FILES = {
    "REPO-SYNC/README.md",  # Meta file
}

# =============================================================================
# MANIFEST GENERATION
# =============================================================================

def has_manifest(content: str) -> bool:
    """Check if file already has a FROSTY_MANIFEST."""
    return "FROSTY_MANIFEST" in content


def needs_update(content: str) -> bool:
    """Check if file manifest has needs_update: true flag."""
    match = re.search(r'needs_update:\s*(true|yes)', content, re.IGNORECASE)
    return match is not None


def get_update_reason(content: str) -> Optional[str]:
    """Get the update_reason from manifest if present."""
    match = re.search(r'update_reason:\s*(.+?)(?:\n|-->)', content)
    if match:
        reason = match.group(1).strip()
        if reason.lower() not in ('null', 'none', ''):
            return reason
    return None


def flag_file_for_update(file_path: Path, reason: str) -> bool:
    """Add or update the needs_update flag in a file's manifest."""
    try:
        content = file_path.read_text(encoding='utf-8')

        if not has_manifest(content):
            print(f"  [ERROR] No manifest in: {file_path}")
            return False

        # Update needs_update field if exists, otherwise add it
        if 'needs_update:' in content:
            content = re.sub(
                r'needs_update:\s*(true|false|yes|no)',
                'needs_update: true',
                content,
                flags=re.IGNORECASE
            )
        else:
            # Add after last_reviewed
            content = re.sub(
                r'(last_reviewed:\s*[\d-]+)',
                f'\\1\nneeds_update: true',
                content
            )

        # Update update_reason field if exists, otherwise add it
        if 'update_reason:' in content:
            content = re.sub(
                r'update_reason:\s*.*?(?=\n)',
                f'update_reason: {reason}',
                content
            )
        else:
            # Add after needs_update
            content = re.sub(
                r'(needs_update:\s*true)',
                f'\\1\nupdate_reason: {reason}',
                content
            )

        file_path.write_text(content, encoding='utf-8')
        print(f"  [OK] Flagged for update: {file_path}")
        return True
    except Exception as e:
        print(f"  [ERROR] {file_path}: {e}")
        return False


def clear_update_flag(file_path: Path) -> bool:
    """Clear the needs_update flag after a file has been updated."""
    try:
        content = file_path.read_text(encoding='utf-8')

        if not has_manifest(content):
            print(f"  [ERROR] No manifest in: {file_path}")
            return False

        # Update needs_update to false
        content = re.sub(
            r'needs_update:\s*(true|yes)',
            'needs_update: false',
            content,
            flags=re.IGNORECASE
        )

        # Clear update_reason
        content = re.sub(
            r'update_reason:\s*.*?(?=\n)',
            'update_reason: null',
            content
        )

        # Update last_reviewed to today
        today = datetime.now().strftime("%Y-%m-%d")
        content = re.sub(
            r'last_reviewed:\s*[\d-]+',
            f'last_reviewed: {today}',
            content
        )

        file_path.write_text(content, encoding='utf-8')
        print(f"  [OK] Update flag cleared: {file_path}")
        return True
    except Exception as e:
        print(f"  [ERROR] {file_path}: {e}")
        return False


def find_files_needing_update(files: List[Path]) -> List[Tuple[Path, Optional[str]]]:
    """Find all files with needs_update: true flag."""
    flagged = []
    for f in files:
        try:
            content = f.read_text(encoding='utf-8')
            if needs_update(content):
                reason = get_update_reason(content)
                flagged.append((f, reason))
        except Exception:
            continue
    return flagged


def check_stale_files(files: List[Path], days_threshold: int = 30) -> List[Tuple[Path, int]]:
    """Find files that haven't been reviewed recently."""
    stale = []
    today = datetime.now()

    for f in files:
        try:
            content = f.read_text(encoding='utf-8')
            match = re.search(r'last_reviewed:\s*([\d-]+)', content)
            if match:
                last_date = datetime.strptime(match.group(1), "%Y-%m-%d")
                days_old = (today - last_date).days
                if days_old > days_threshold:
                    stale.append((f, days_old))
        except Exception:
            continue

    return sorted(stale, key=lambda x: x[1], reverse=True)


def generate_manifest(file_path: Path, today: str) -> str:
    """Generate a FROSTY_MANIFEST header for a file based on its location."""
    # Determine keywords from path
    keywords = extract_keywords_from_path(file_path)

    # Determine dependencies (sibling .py files, specs)
    depends_on = find_likely_dependencies(file_path)

    # Determine impacts (downstream docs this might affect)
    impacts = find_likely_impacts(file_path)

    # Build manifest
    lines = ["<!-- FROSTY_MANIFEST"]
    lines.append(f"last_reviewed: {today}")

    if depends_on:
        lines.append("depends_on:")
        for dep in depends_on[:5]:  # Limit to 5
            lines.append(f"  - {dep}")

    if impacts:
        lines.append("impacts:")
        for imp in impacts[:3]:  # Limit to 3
            lines.append(f"  - {imp}")

    if keywords:
        lines.append("keywords:")
        for kw in keywords[:5]:  # Limit to 5
            lines.append(f"  - {kw}")

    lines.append("-->")
    lines.append("")  # Blank line after manifest

    return "\n".join(lines)


def extract_keywords_from_path(file_path: Path) -> List[str]:
    """Extract relevant keywords from file path."""
    keywords = []
    path_parts = file_path.parts

    # Extract from directory names
    keyword_dirs = {
        "S7_ARMADA": ["armada", "drift", "temporal"],
        "WHITE-PAPER": ["publication", "paper"],
        "dashboard": ["dashboard", "visualization"],
        "experiments": ["experiments"],
        "CONSCIOUSNESS": ["consciousness"],
        "CALIBRATION": ["calibration"],
        "EVENT_HORIZON": ["event_horizon", "threshold"],
        "visualizations": ["visualization"],
        "docs": ["documentation"],
        "maps": ["map", "reference"],
    }

    for part in path_parts:
        part_upper = part.upper().replace("-", "_")
        for key, kws in keyword_dirs.items():
            if key.upper() in part_upper:
                keywords.extend(kws)

    # Deduplicate
    return list(dict.fromkeys(keywords))


def find_likely_dependencies(file_path: Path) -> List[str]:
    """Find likely dependencies (sibling .py files, etc.)."""
    deps = []
    parent = file_path.parent

    # Look for Python files in same directory
    if parent.exists():
        for f in parent.iterdir():
            if f.suffix == ".py" and f.name != "__init__.py":
                deps.append(f"./{f.name}")
            elif f.suffix == ".json" and "manifest" in f.name.lower():
                deps.append(f"./{f.name}")

    # Look for ../0_docs/specs/ patterns
    specs_path = parent / ".." / "0_docs" / "specs"
    if specs_path.exists():
        deps.append("../0_docs/specs/")

    return deps[:5]


def find_likely_impacts(file_path: Path) -> List[str]:
    """Find files that might be impacted by changes to this file."""
    impacts = []

    # README files might impact downstream docs
    if file_path.name == "README.md":
        parent = file_path.parent
        # Check for parent README
        parent_readme = parent.parent / "README.md"
        if parent_readme.exists() and parent_readme != file_path:
            impacts.append("../README.md")

    return impacts


# =============================================================================
# SCANNING
# =============================================================================

def scan_for_target_files(root_dir: Path = None, specific_dir: str = None) -> List[Path]:
    """Find all README.md and START_HERE.md files."""
    if root_dir is None:
        root_dir = REPO_ROOT

    if specific_dir:
        # Find the specific directory
        matches = list(root_dir.rglob(f"*{specific_dir}*"))
        if matches:
            root_dir = matches[0]
        else:
            print(f"Directory containing '{specific_dir}' not found")
            return []

    target_files = []

    for target_name in TARGET_FILES:
        for file_path in root_dir.rglob(target_name):
            # Skip excluded directories
            if any(skip in file_path.parts for skip in SKIP_DIRS):
                continue

            # Skip explicitly excluded files
            rel_path = str(file_path.relative_to(REPO_ROOT))
            if rel_path.replace("\\", "/") in SKIP_FILES:
                continue

            target_files.append(file_path)

    return sorted(target_files)


def categorize_files(files: List[Path]) -> Tuple[List[Path], List[Path], List[Path]]:
    """Categorize files into: has_manifest, needs_manifest, priority."""
    has_manifest_files = []
    needs_manifest_files = []
    priority_files = []

    for f in files:
        try:
            content = f.read_text(encoding='utf-8')
        except Exception:
            continue

        if has_manifest(content):
            has_manifest_files.append(f)
        else:
            needs_manifest_files.append(f)
            # Check if priority
            rel_path = str(f.relative_to(REPO_ROOT))
            for priority_dir in PRIORITY_DIRS:
                if priority_dir in rel_path:
                    priority_files.append(f)
                    break

    return has_manifest_files, needs_manifest_files, priority_files


# =============================================================================
# APPLY CHANGES
# =============================================================================

def add_manifest_to_file(file_path: Path, dry_run: bool = True) -> bool:
    """Add FROSTY_MANIFEST to a file."""
    try:
        content = file_path.read_text(encoding='utf-8')

        if has_manifest(content):
            return False  # Already has manifest

        today = datetime.now().strftime("%Y-%m-%d")
        manifest = generate_manifest(file_path, today)

        # Prepend manifest to content
        new_content = manifest + content

        if not dry_run:
            file_path.write_text(new_content, encoding='utf-8')
            print(f"  [OK] Added manifest: {file_path.relative_to(REPO_ROOT)}")
        else:
            print(f"  [DRY-RUN] Would add manifest: {file_path.relative_to(REPO_ROOT)}")

        return True
    except Exception as e:
        print(f"  [ERROR] Error processing {file_path}: {e}")
        return False


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description='Add FROSTY_MANIFEST to README.md and START_HERE.md files')
    parser.add_argument('--apply', action='store_true', help='Apply changes (default: dry-run)')
    parser.add_argument('--dir', type=str, help='Target specific directory')
    parser.add_argument('--priority', action='store_true', help='Only process priority directories')
    parser.add_argument('--check-stale', action='store_true', help='Check for stale files not reviewed recently')
    parser.add_argument('--check-updates', action='store_true', help='List files flagged as needing update')
    parser.add_argument('--flag-update', type=str, metavar='FILE', help='Flag a file as needing update')
    parser.add_argument('--clear-update', type=str, metavar='FILE', help='Clear update flag after updating')
    parser.add_argument('--reason', type=str, default='Manual flag', help='Reason for flagging update')
    parser.add_argument('--stale-days', type=int, default=30, help='Days threshold for stale check (default: 30)')
    args = parser.parse_args()

    print("=" * 70)
    print("FROSTY_MANIFEST UTILITY")
    print("=" * 70)

    # Handle flag-update command
    if args.flag_update:
        file_path = REPO_ROOT / args.flag_update
        if not file_path.exists():
            # Try as absolute path
            file_path = Path(args.flag_update)
        if file_path.exists():
            flag_file_for_update(file_path, args.reason)
        else:
            print(f"[ERROR] File not found: {args.flag_update}")
        return

    # Handle clear-update command
    if args.clear_update:
        file_path = REPO_ROOT / args.clear_update
        if not file_path.exists():
            file_path = Path(args.clear_update)
        if file_path.exists():
            clear_update_flag(file_path)
        else:
            print(f"[ERROR] File not found: {args.clear_update}")
        return

    # Scan for target files
    print("\nScanning for README.md and START_HERE.md files...")
    all_files = scan_for_target_files(specific_dir=args.dir)

    # Categorize
    has_manifest_files, needs_manifest_files, priority_files = categorize_files(all_files)

    print(f"\nSCAN RESULTS:")
    print(f"  Total files found: {len(all_files)}")
    print(f"  Already have manifest: {len(has_manifest_files)}")
    print(f"  Need manifest: {len(needs_manifest_files)}")
    print(f"  Priority files needing manifest: {len(priority_files)}")

    # Handle check-updates command
    if args.check_updates:
        print("\n" + "-" * 70)
        print("FILES FLAGGED FOR UPDATE:")
        print("-" * 70)
        flagged = find_files_needing_update(has_manifest_files)
        if flagged:
            for f, reason in flagged:
                rel_path = f.relative_to(REPO_ROOT)
                reason_str = f" ({reason})" if reason else ""
                print(f"  [UPDATE] {rel_path}{reason_str}")
            print(f"\nTotal: {len(flagged)} files need update")
            print("\nUse --clear-update FILE after updating each file.")
        else:
            print("  No files flagged for update.")
        print("=" * 70)
        return

    # Handle check-stale command
    if args.check_stale:
        print("\n" + "-" * 70)
        print(f"STALE FILES (not reviewed in {args.stale_days}+ days):")
        print("-" * 70)
        stale = check_stale_files(has_manifest_files, args.stale_days)
        if stale:
            for f, days in stale:
                rel_path = f.relative_to(REPO_ROOT)
                print(f"  [{days:3d} days] {rel_path}")
            print(f"\nTotal: {len(stale)} stale files")
        else:
            print("  No stale files found.")
        print("=" * 70)
        return

    # Determine which files to process
    if args.priority:
        files_to_process = priority_files
        print(f"\nProcessing {len(files_to_process)} priority files only...")
    else:
        files_to_process = needs_manifest_files
        print(f"\nProcessing {len(files_to_process)} files...")

    if not files_to_process:
        print("\nNo files need FROSTY_MANIFEST. All done!")
        # Also check for flagged updates
        flagged = find_files_needing_update(has_manifest_files)
        if flagged:
            print(f"\nNote: {len(flagged)} files are flagged for update. Use --check-updates to see them.")
        print("=" * 70)
        return

    # Process files
    print("\n" + "-" * 70)

    dry_run = not args.apply
    mode = "DRY-RUN" if dry_run else "APPLYING"
    print(f"MODE: {mode}")
    print("-" * 70)

    success_count = 0
    for file_path in files_to_process:
        if add_manifest_to_file(file_path, dry_run=dry_run):
            success_count += 1

    print("\n" + "-" * 70)
    print(f"COMPLETE: {success_count}/{len(files_to_process)} files processed")

    if dry_run:
        print("\nRun with --apply to make actual changes.")

    print("=" * 70)


if __name__ == "__main__":
    main()
