"""
OPERATION FROSTY - Cold-Boot Documentation Automation
=====================================================

Automates the process of keeping documentation fresh for cold-started Claude instances.

USAGE:
    py REPO-SYNC/frosty.py                    # Full scan and report
    py REPO-SYNC/frosty.py --commits 10       # Check against last 10 commits
    py REPO-SYNC/frosty.py --dir S7_ARMADA    # Scan specific directory
    py REPO-SYNC/frosty.py --update-manifests # Refresh manifest timestamps

PHILOSOPHY:
    Phase 0: Status updates (what's done, what's next)
    Phase 1: Context updates (structural changes, new patterns)

    The real value is Phase 1 - ensuring files reflect current reality.

MANIFEST FORMAT (embedded in markdown files):
    <!-- FROSTY_MANIFEST
    last_reviewed: 2025-12-17
    depends_on:
      - ../1_CALIBRATION/lib/triple_dip.py
      - ../0_docs/specs/0_RUN_METHODOLOGY.md
    impacts:
      - ../14_CONSCIOUSNESS/README.md
    keywords:
      - exit_survey
      - triple_dip
    -->

Author: Claude (Nyquist Framework)
Date: December 17, 2025
"""

import os
import sys
import re
import argparse
import subprocess
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Set

# =============================================================================
# CONFIGURATION
# =============================================================================

REPO_ROOT = Path(__file__).parent.parent

COLD_BOOT_PATTERNS = [
    "README.md",
    "START_HERE.md",
    "*_METHODOLOGY.md",
    "*_INTENTIONALITY.md",
    "*_MAP.md",
    "*_MATRIX.md",
]

PRIORITY_DIRS = [
    "experiments/temporal_stability/S7_ARMADA",
    "Consciousness",
    "docs/maps",
]

# How many commits back to check by default
DEFAULT_COMMIT_DEPTH = 5

# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class FrostyManifest:
    """Embedded manifest parsed from markdown files."""
    last_reviewed: Optional[datetime] = None
    depends_on: List[str] = field(default_factory=list)
    impacts: List[str] = field(default_factory=list)
    keywords: List[str] = field(default_factory=list)

@dataclass
class FlaggedFile:
    """A file flagged for documentation update."""
    path: Path
    priority: str  # HIGH, MEDIUM, LOW
    reasons: List[str] = field(default_factory=list)
    last_reviewed: Optional[datetime] = None
    commits_since: int = 0
    checklist: List[str] = field(default_factory=list)

# =============================================================================
# GIT OPERATIONS
# =============================================================================

def get_recent_commits(n: int = 5) -> List[Dict]:
    """Get last N commit messages and changed files."""
    commits = []
    try:
        # Get commit hashes and messages
        result = subprocess.run(
            ["git", "log", f"-{n}", "--format=%H|%s|%ai"],
            capture_output=True, text=True, cwd=REPO_ROOT
        )
        if result.returncode != 0:
            print(f"[WARNING] Git log failed: {result.stderr}")
            return commits

        for line in result.stdout.strip().split("\n"):
            if not line:
                continue
            parts = line.split("|", 2)
            if len(parts) >= 3:
                commit_hash, message, date_str = parts

                # Get files changed in this commit
                files_result = subprocess.run(
                    ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit_hash],
                    capture_output=True, text=True, cwd=REPO_ROOT
                )
                changed_files = files_result.stdout.strip().split("\n") if files_result.returncode == 0 else []

                commits.append({
                    "hash": commit_hash[:7],
                    "message": message,
                    "date": date_str,
                    "files": [f for f in changed_files if f]
                })
    except Exception as e:
        print(f"[ERROR] Failed to get commits: {e}")

    return commits

def get_file_last_modified(path: Path) -> Optional[datetime]:
    """Get last modified time of a file from git or filesystem."""
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%ai", "--", str(path)],
            capture_output=True, text=True, cwd=REPO_ROOT
        )
        if result.returncode == 0 and result.stdout.strip():
            date_str = result.stdout.strip()
            # Parse git date format: "2025-12-17 01:45:25 -0800"
            return datetime.strptime(date_str[:19], "%Y-%m-%d %H:%M:%S")
    except:
        pass

    # Fallback to filesystem mtime
    try:
        return datetime.fromtimestamp(path.stat().st_mtime)
    except:
        return None

# =============================================================================
# MANIFEST PARSING
# =============================================================================

def parse_frosty_manifest(file_path: Path) -> Optional[FrostyManifest]:
    """Extract FROSTY_MANIFEST from markdown file."""
    try:
        content = file_path.read_text(encoding='utf-8', errors='replace')
    except:
        return None

    # Look for manifest block
    pattern = r'<!--\s*FROSTY_MANIFEST\s*(.*?)\s*-->'
    match = re.search(pattern, content, re.DOTALL | re.IGNORECASE)

    if not match:
        return None

    manifest = FrostyManifest()
    manifest_text = match.group(1)

    # Parse YAML-like content
    current_key = None
    current_list = []

    for line in manifest_text.split('\n'):
        line = line.strip()
        if not line:
            continue

        # Key: value or Key:
        key_match = re.match(r'^(\w+):\s*(.*)$', line)
        if key_match:
            # Save previous list if any
            if current_key and current_list:
                setattr(manifest, current_key, current_list)
                current_list = []

            key = key_match.group(1)
            value = key_match.group(2).strip()

            if key == 'last_reviewed' and value:
                try:
                    manifest.last_reviewed = datetime.strptime(value, "%Y-%m-%d")
                except:
                    pass
            elif value:
                setattr(manifest, key, [value])
                current_key = None
            else:
                current_key = key
        elif line.startswith('-'):
            item = line[1:].strip()
            current_list.append(item)

    # Save final list
    if current_key and current_list:
        setattr(manifest, current_key, current_list)

    return manifest

# =============================================================================
# FILE SCANNING
# =============================================================================

def scan_cold_boot_docs(root: Path, subdir: Optional[str] = None) -> List[Path]:
    """Find all README.md, START_HERE.md, etc."""
    search_root = root / subdir if subdir else root
    found = []

    for pattern in COLD_BOOT_PATTERNS:
        found.extend(search_root.rglob(pattern))

    # Filter out common exclusions
    exclusions = ['.git', '__pycache__', 'node_modules', 'venv', '.venv']
    filtered = [
        f for f in found
        if not any(ex in str(f) for ex in exclusions)
    ]

    return sorted(set(filtered))

def check_file_staleness(doc_path: Path, commits: List[Dict]) -> FlaggedFile:
    """Determine if a doc file needs updating based on changes."""
    flagged = FlaggedFile(path=doc_path, priority="NONE")

    # Parse manifest
    manifest = parse_frosty_manifest(doc_path)
    if manifest:
        flagged.last_reviewed = manifest.last_reviewed

    # Check if doc itself was modified recently
    doc_rel_path = doc_path.relative_to(REPO_ROOT)
    doc_modified_in_commits = 0

    for commit in commits:
        if str(doc_rel_path) in commit['files']:
            doc_modified_in_commits += 1

    # Check dependencies
    if manifest and manifest.depends_on:
        for dep in manifest.depends_on:
            dep_path = str((doc_path.parent / dep).resolve())
            for commit in commits:
                for changed in commit['files']:
                    if dep in changed or changed.endswith(Path(dep).name):
                        flagged.reasons.append(f"Dependency changed: {Path(dep).name}")
                        flagged.commits_since += 1

    # Check for keyword matches in commit messages
    if manifest and manifest.keywords:
        for commit in commits:
            for keyword in manifest.keywords:
                if keyword.lower() in commit['message'].lower():
                    flagged.reasons.append(f"Commit mentions '{keyword}': {commit['hash']}")
                    flagged.commits_since += 1

    # Check if sibling files changed (same directory)
    doc_dir = doc_path.parent
    for commit in commits:
        for changed in commit['files']:
            changed_path = REPO_ROOT / changed
            if changed_path.parent == doc_dir and changed_path != doc_path:
                if changed.endswith('.py') or changed.endswith('.md'):
                    flagged.reasons.append(f"Sibling changed: {Path(changed).name}")
                    flagged.commits_since += 1

    # Determine priority
    unique_reasons = list(set(flagged.reasons))
    flagged.reasons = unique_reasons

    if len(unique_reasons) >= 3:
        flagged.priority = "HIGH"
    elif len(unique_reasons) >= 1:
        flagged.priority = "MEDIUM"
    elif not manifest:
        flagged.priority = "LOW"
        flagged.reasons.append("No FROSTY_MANIFEST found")

    # Generate checklist based on file type
    flagged.checklist = generate_checklist(doc_path, flagged.reasons)

    return flagged

def generate_checklist(doc_path: Path, reasons: List[str]) -> List[str]:
    """Generate context-aware update checklist for a file."""
    checklist = []
    name = doc_path.name.lower()

    if name == "readme.md":
        checklist = [
            "[ ] Update status section (what's completed, in-progress, planned)",
            "[ ] Verify cross-references to other docs still valid",
            "[ ] Check for outdated patterns or deprecated approaches",
            "[ ] Update 'Last Updated' timestamp in FROSTY_MANIFEST"
        ]
    elif name == "start_here.md":
        checklist = [
            "[ ] Verify operational instructions still accurate",
            "[ ] Check example commands work",
            "[ ] Update prerequisite list",
            "[ ] Update 'Last Updated' timestamp"
        ]
    elif "methodology" in name:
        checklist = [
            "[ ] Verify code examples match current implementation",
            "[ ] Check cross-references to spec files",
            "[ ] Update library locations (agnostic paths)",
            "[ ] Update lessons learned section"
        ]
    elif "map" in name or "matrix" in name:
        checklist = [
            "[ ] Verify counts/statistics still accurate",
            "[ ] Check for new entries needed",
            "[ ] Update cross-references"
        ]
    else:
        checklist = [
            "[ ] Review for outdated information",
            "[ ] Update references if needed",
            "[ ] Update timestamp"
        ]

    return checklist

# =============================================================================
# REPORT GENERATION
# =============================================================================

def print_frosty_report(flagged_files: List[FlaggedFile], commits: List[Dict]):
    """Print the Operation Frosty report."""
    print("=" * 80)
    print("                    OPERATION FROSTY - Documentation Refresh")
    print("=" * 80)
    print()

    # Show recent commits
    print("Last commits analyzed:")
    for commit in commits[:5]:
        print(f"  {commit['hash']} {commit['message'][:60]}")
    print()

    # Filter to only flagged files
    flagged = [f for f in flagged_files if f.priority != "NONE"]

    if not flagged:
        print("No files flagged for update. Documentation appears current.")
        return

    print("=" * 80)
    print("FILES FLAGGED FOR UPDATE (by priority)")
    print("=" * 80)
    print()

    # Sort by priority
    priority_order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2}
    flagged.sort(key=lambda f: priority_order.get(f.priority, 3))

    for f in flagged:
        rel_path = f.path.relative_to(REPO_ROOT)
        print(f"[{f.priority}] {rel_path}")

        if f.last_reviewed:
            print(f"  Last reviewed: {f.last_reviewed.strftime('%Y-%m-%d')}")
        else:
            print("  Last reviewed: NEVER (no manifest)")

        if f.commits_since > 0:
            print(f"  Related commits: {f.commits_since}")

        if f.reasons:
            print("  Reasons:")
            for reason in f.reasons[:5]:  # Limit to 5 reasons
                print(f"    - {reason}")

        print("  Checklist:")
        for item in f.checklist:
            print(f"    {item}")
        print()

    print("=" * 80)
    print("SUGGESTED UPDATE ORDER")
    print("=" * 80)
    print()

    high_priority = [f for f in flagged if f.priority == "HIGH"]
    medium_priority = [f for f in flagged if f.priority == "MEDIUM"]

    order = 1
    for f in high_priority + medium_priority:
        rel_path = f.path.relative_to(REPO_ROOT)
        print(f"{order}. {rel_path}")
        order += 1

    print()
    print(f"Total files flagged: {len(flagged)}")
    print(f"  HIGH: {len(high_priority)}")
    print(f"  MEDIUM: {len(medium_priority)}")
    print(f"  LOW: {len([f for f in flagged if f.priority == 'LOW'])}")

# =============================================================================
# MANIFEST UPDATE
# =============================================================================

def update_manifest_timestamp(file_path: Path) -> bool:
    """Update the last_reviewed timestamp in a file's manifest."""
    try:
        content = file_path.read_text(encoding='utf-8')
    except:
        return False

    today = datetime.now().strftime("%Y-%m-%d")

    # Find and update manifest
    pattern = r'(<!--\s*FROSTY_MANIFEST\s*\n)(.*?)(-->)'

    def replace_timestamp(match):
        prefix = match.group(1)
        manifest_content = match.group(2)
        suffix = match.group(3)

        # Update or add last_reviewed
        if 'last_reviewed:' in manifest_content:
            manifest_content = re.sub(
                r'last_reviewed:\s*\d{4}-\d{2}-\d{2}',
                f'last_reviewed: {today}',
                manifest_content
            )
        else:
            manifest_content = f'last_reviewed: {today}\n' + manifest_content

        return prefix + manifest_content + suffix

    new_content, count = re.subn(pattern, replace_timestamp, content, flags=re.DOTALL)

    if count > 0:
        file_path.write_text(new_content, encoding='utf-8')
        print(f"  Updated: {file_path.relative_to(REPO_ROOT)}")
        return True
    else:
        print(f"  No manifest found: {file_path.relative_to(REPO_ROOT)}")
        return False

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Operation Frosty - Cold-Boot Documentation Automation"
    )
    parser.add_argument(
        "--commits", "-c", type=int, default=DEFAULT_COMMIT_DEPTH,
        help=f"Number of commits to analyze (default: {DEFAULT_COMMIT_DEPTH})"
    )
    parser.add_argument(
        "--dir", "-d", type=str, default=None,
        help="Scan specific subdirectory (relative to repo root)"
    )
    parser.add_argument(
        "--update-manifests", "-u", action="store_true",
        help="Update last_reviewed timestamps in all manifests"
    )
    args = parser.parse_args()

    print(f"\nOperation Frosty - Scanning from: {REPO_ROOT}")
    print(f"Analyzing last {args.commits} commits...")
    print()

    # Get recent commits
    commits = get_recent_commits(args.commits)

    if not commits:
        print("[WARNING] No git commits found or git unavailable")

    # Scan for cold-boot docs
    docs = scan_cold_boot_docs(REPO_ROOT, args.dir)
    print(f"Found {len(docs)} cold-boot documentation files")
    print()

    if args.update_manifests:
        print("Updating manifest timestamps...")
        for doc in docs:
            update_manifest_timestamp(doc)
        return

    # Check each for staleness
    flagged = []
    for doc in docs:
        result = check_file_staleness(doc, commits)
        flagged.append(result)

    # Print report
    print_frosty_report(flagged, commits)

if __name__ == "__main__":
    main()
