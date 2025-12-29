#!/usr/bin/env python3
"""
_convert_to_reviewer.py - GUIDES PATH TRANSLATOR
=================================================
Converts repo-facing paths to reviewer-package paths in markdown files.

Called by 2_package_review.py when extracting review packages.

USAGE:
------
# As module (from 2_package_review.py)
from guides._convert_to_reviewer import convert_content

converted = convert_content(markdown_text)

# Standalone
py _convert_to_reviewer.py REPRODUCIBILITY_README.md --output converted.md
py _convert_to_reviewer.py MANIFEST.md --dry-run

PATH TRANSLATION MAP:
--------------------
Repo paths are converted to reviewer package (.shared/) relative paths.

| Repo Path | Reviewer Path |
|-----------|---------------|
| experiments/temporal_stability/S7_ARMADA/... | (preserved for repo reference) |
| WHITE-PAPER/guides/ | guides/ |
| WHITE-PAPER/planning/ | ../planning/ |
| WHITE-PAPER/figures/ | ../figures/ |
| WHITE-PAPER/theory/ | ../theory/ |
| WHITE-PAPER/references/ | ../references/ |
| ../planning/ | ../planning/ |
| ../figures/ | ../figures/ |

Author: WHITE-PAPER Calibration
Version: 1.0 (2025-12-29) - Initial implementation
"""

import re
import argparse
from pathlib import Path
from typing import Tuple, List

# === PATH TRANSLATION MAP ===
# (pattern, replacement) tuples - ORDER MATTERS (more specific first)

REPO_TO_REVIEWER_MAP: List[Tuple[str, str]] = [
    # Links from guides/ to other WHITE-PAPER directories
    # These use ../ because reviewer guides/ is at .shared/guides/

    # Already correct relative paths (no change needed)
    # ("../planning/", "../planning/"),  # Already correct
    # ("../figures/", "../figures/"),    # Already correct
    # ("../START_HERE.md", "../START_HERE.md"),  # Already correct

    # Absolute repo paths that need conversion
    # (From repo root perspective to reviewer package perspective)

    # Experiment paths - leave as repo reference (informational only)
    # Reviewers won't have access to experiments/, so we keep for context

    # WHITE-PAPER internal paths that might appear
    ("WHITE-PAPER/guides/", "guides/"),
    ("WHITE-PAPER/planning/", "../planning/"),
    ("WHITE-PAPER/figures/", "../figures/"),
    ("WHITE-PAPER/theory/", "../theory/"),
    ("WHITE-PAPER/references/", "../references/"),
    ("WHITE-PAPER/submissions/", "../submissions/"),

    # Paths starting from guides/ perspective (same-level)
    # These are already relative and correct for reviewer packages
]


def convert_content(content: str) -> str:
    """
    Convert repo paths in markdown content to reviewer package paths.

    Args:
        content: Raw markdown content with repo paths

    Returns:
        Converted content with reviewer-friendly paths
    """
    result = content

    for repo_pattern, reviewer_pattern in REPO_TO_REVIEWER_MAP:
        # Replace in markdown links: [text](path)
        # Be careful not to replace partial matches
        result = result.replace(repo_pattern, reviewer_pattern)

    return result


def convert_file(input_path: Path, output_path: Path = None, dry_run: bool = False) -> Tuple[str, int]:
    """
    Convert a single markdown file.

    Args:
        input_path: Path to source file
        output_path: Path to write converted file (default: overwrite input)
        dry_run: Preview changes without writing

    Returns:
        Tuple of (converted_content, num_changes)
    """
    if not input_path.exists():
        raise FileNotFoundError(f"Input file not found: {input_path}")

    original = input_path.read_text(encoding="utf-8")
    converted = convert_content(original)

    # Count changes
    num_changes = sum(
        original.count(pattern)
        for pattern, _ in REPO_TO_REVIEWER_MAP
        if original.count(pattern) > 0
    )

    if not dry_run and output_path:
        output_path.write_text(converted, encoding="utf-8")
    elif not dry_run and not output_path:
        input_path.write_text(converted, encoding="utf-8")

    return converted, num_changes


def show_diff(original: str, converted: str) -> None:
    """Show a simple diff of changes."""
    import sys
    sys.stdout.reconfigure(encoding='utf-8')

    orig_lines = original.splitlines()
    conv_lines = converted.splitlines()

    for i, (orig, conv) in enumerate(zip(orig_lines, conv_lines), 1):
        if orig != conv:
            print(f"Line {i}:")
            print(f"  - {orig}")
            print(f"  + {conv}")
            print()


def main():
    parser = argparse.ArgumentParser(
        description="Convert repo paths to reviewer package paths in markdown files"
    )
    parser.add_argument("input", type=Path, help="Input markdown file")
    parser.add_argument("--output", "-o", type=Path, help="Output file (default: overwrite input)")
    parser.add_argument("--dry-run", "-n", action="store_true", help="Preview without writing")
    parser.add_argument("--show-diff", "-d", action="store_true", help="Show line-by-line diff")

    args = parser.parse_args()

    original = args.input.read_text(encoding="utf-8")
    converted, num_changes = convert_file(args.input, args.output, args.dry_run)

    if args.show_diff:
        show_diff(original, converted)

    print(f"File: {args.input}")
    print(f"Changes: {num_changes} path conversions")

    if args.dry_run:
        print("Dry run - no files written")
    else:
        output = args.output if args.output else args.input
        print(f"Output: {output}")


if __name__ == "__main__":
    main()
