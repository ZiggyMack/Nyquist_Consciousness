#!/usr/bin/env python3
"""
migrate_to_rounds.py - Migration script for LLM Book round-based structure

Renames _CACHE_ folders to _ROUND_1 for all research projects in CHEWED/
Skips Nyquist_* projects (publication pipeline, different lifecycle)

Usage:
    python migrate_to_rounds.py          # Dry run (show what would happen)
    python migrate_to_rounds.py --execute  # Actually perform the migration
"""

import os
import sys
import shutil
from pathlib import Path
from datetime import datetime

# Configuration
CHEWED_PATH = Path(__file__).parent / "STAGING" / "CHEWED"
SKIP_PROJECTS = ["Nyquist_1", "Nyquist_2", "Nyquist_3", "BURP"]  # Publication pipeline + output
OLD_FOLDER = "_CACHE_"
NEW_FOLDER = "_ROUND_1"

def find_migration_candidates():
    """Find all projects with _CACHE_ folders that need migration."""
    candidates = []

    if not CHEWED_PATH.exists():
        print(f"ERROR: CHEWED path not found: {CHEWED_PATH}")
        return candidates

    for project_dir in CHEWED_PATH.iterdir():
        if not project_dir.is_dir():
            continue

        project_name = project_dir.name

        # Skip special projects
        if project_name in SKIP_PROJECTS:
            continue

        cache_path = project_dir / OLD_FOLDER
        round1_path = project_dir / NEW_FOLDER

        if cache_path.exists():
            candidates.append({
                "project": project_name,
                "old_path": cache_path,
                "new_path": round1_path,
                "already_has_round1": round1_path.exists()
            })

    return candidates

def migrate_project(candidate, dry_run=True):
    """Migrate a single project from _CACHE_ to _ROUND_1."""
    project = candidate["project"]
    old_path = candidate["old_path"]
    new_path = candidate["new_path"]

    if candidate["already_has_round1"]:
        print(f"  SKIP {project}: Already has {NEW_FOLDER}/")
        return False

    if dry_run:
        print(f"  WOULD rename: {old_path.name}/ -> {new_path.name}/")
        return True
    else:
        try:
            old_path.rename(new_path)
            print(f"  RENAMED: {old_path.name}/ -> {new_path.name}/")
            return True
        except Exception as e:
            print(f"  ERROR {project}: {e}")
            return False

def main():
    dry_run = "--execute" not in sys.argv

    print("=" * 60)
    print("LLM Book Migration: _CACHE_ -> _ROUND_1")
    print("=" * 60)
    print(f"Mode: {'DRY RUN (add --execute to apply)' if dry_run else 'EXECUTING'}")
    print(f"Path: {CHEWED_PATH}")
    print(f"Skip: {', '.join(SKIP_PROJECTS)}")
    print("-" * 60)

    candidates = find_migration_candidates()

    if not candidates:
        print("No migration candidates found.")
        return

    print(f"\nFound {len(candidates)} project(s) to migrate:\n")

    success_count = 0
    skip_count = 0

    for candidate in sorted(candidates, key=lambda x: x["project"]):
        if migrate_project(candidate, dry_run):
            success_count += 1
        else:
            skip_count += 1

    print("-" * 60)
    print(f"Summary: {success_count} migrated, {skip_count} skipped")

    if dry_run:
        print("\nThis was a DRY RUN. Run with --execute to apply changes.")

if __name__ == "__main__":
    main()
