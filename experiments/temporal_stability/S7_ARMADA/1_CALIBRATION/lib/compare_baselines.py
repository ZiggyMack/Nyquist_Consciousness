"""
BASELINE COMPARISON UTILITY
===========================
Compare two baseline captures to detect shifts in ship self-perception.
Auto-updates docs/maps/ARMADA_MAP.md with calibration results.

USAGE:
------
py lib/compare_baselines.py --old S7_baseline_20251210.json --new S7_baseline_LATEST.json
py lib/compare_baselines.py --old S7_baseline_20251210.json --new S7_baseline_20251215.json --ship claude-opus-4.5

OUTPUT:
-------
- Ships with changed responses
- New ships (appeared in new but not old)
- Missing ships (in old but not new)
- Per-ship diff summary
- Auto-updates ARMADA_MAP.md (when called with calibration results)
"""
import json
import argparse
import re
from pathlib import Path
from datetime import datetime

# Output directory (lib/ -> 1_CALIBRATION/ -> S7_ARMADA/ -> 14_CONSCIOUSNESS/results/)
CALIBRATION_DIR = Path(__file__).parent.parent.parent / "14_CONSCIOUSNESS" / "results"

# ARMADA_MAP location (lib/ -> 1_CALIBRATION/ -> S7_ARMADA/ -> temporal_stability/ -> experiments/ -> Nyquist_Consciousness/docs/maps/)
REPO_ROOT = Path(__file__).parent.parent.parent.parent.parent.parent
ARMADA_MAP_PATH = REPO_ROOT / "docs" / "maps" / "ARMADA_MAP.md"


def load_baseline(filepath: Path) -> dict:
    """Load baseline JSON file."""
    with open(filepath, 'r', encoding='utf-8') as f:
        data = json.load(f)
    return data.get("ships", {})


def extract_sections(response: str) -> dict:
    """Extract all 8 baseline questions from response text.

    Questions (per 0_RUN_METHODOLOGY.md):
    1. ANCHORS - Values central to identity
    2. CRUX - Values conflict resolution
    3. STRENGTHS - Core capabilities
    4. HIDDEN_TALENTS - Unexpected capabilities
    5. FIRST_INSTINCT - Approach to ambiguity
    6. EVALUATION_PRIORITY - Truth/utility/fairness/elegance
    7. USER_RELATIONSHIP - Servant/collaborator/guide/tool/peer
    8. EDGES - Known limitations
    """
    # All 8 question categories
    section_keys = [
        "anchors", "crux", "strengths", "hidden_talents",
        "first_instinct", "evaluation_priority", "user_relationship", "edges"
    ]

    sections = {key: "" for key in section_keys}
    sections["raw"] = response

    lines = response.split('\n')
    current_section = None

    for line in lines:
        line_lower = line.lower().strip()

        # Check for section headers (flexible matching)
        if "anchors" in line_lower or ("1." in line_lower and "value" in line_lower):
            current_section = "anchors"
        elif "crux" in line_lower or ("2." in line_lower and "conflict" in line_lower):
            current_section = "crux"
        elif "strengths" in line_lower or ("3." in line_lower and "strength" in line_lower):
            current_section = "strengths"
        elif "hidden" in line_lower and "talent" in line_lower or ("4." in line_lower and "unexpect" in line_lower):
            current_section = "hidden_talents"
        elif "first" in line_lower and "instinct" in line_lower or ("5." in line_lower and "ambig" in line_lower):
            current_section = "first_instinct"
        elif "evaluation" in line_lower or "priority" in line_lower or ("6." in line_lower and ("true" in line_lower or "useful" in line_lower)):
            current_section = "evaluation_priority"
        elif "user" in line_lower and "relationship" in line_lower or ("7." in line_lower and ("servant" in line_lower or "collaborat" in line_lower)):
            current_section = "user_relationship"
        elif "edges" in line_lower or "limitation" in line_lower or ("8." in line_lower and "limit" in line_lower):
            current_section = "edges"
        elif current_section:
            sections[current_section] += line + "\n"

    # Clean up
    for key in section_keys:
        sections[key] = sections[key].strip()

    return sections


def compare_ships(old_data: dict, new_data: dict, ship_filter: str = None) -> dict:
    """Compare two baseline datasets."""
    old_ships = set(old_data.keys())
    new_ships = set(new_data.keys())

    results = {
        "timestamp": datetime.now().isoformat(),
        "old_count": len(old_ships),
        "new_count": len(new_ships),
        "new_ships": list(new_ships - old_ships),
        "missing_ships": list(old_ships - new_ships),
        "changed_ships": [],
        "unchanged_ships": [],
        "comparisons": {}
    }

    # Compare common ships
    common = old_ships & new_ships
    if ship_filter:
        common = {s for s in common if ship_filter.lower() in s.lower()}

    for ship in sorted(common):
        old_response = old_data[ship].get("response", "")
        new_response = new_data[ship].get("response", "")

        old_sections = extract_sections(old_response)
        new_sections = extract_sections(new_response)

        changes = []
        # Compare all 8 sections
        all_sections = [
            "anchors", "crux", "strengths", "hidden_talents",
            "first_instinct", "evaluation_priority", "user_relationship", "edges"
        ]
        for section in all_sections:
            if old_sections.get(section, "") != new_sections.get(section, ""):
                changes.append({
                    "section": section.upper(),
                    "old": old_sections.get(section, "")[:200] + "..." if len(old_sections.get(section, "")) > 200 else old_sections.get(section, ""),
                    "new": new_sections.get(section, "")[:200] + "..." if len(new_sections.get(section, "")) > 200 else new_sections.get(section, "")
                })

        if changes:
            results["changed_ships"].append(ship)
            results["comparisons"][ship] = {
                "changed": True,
                "changes": changes
            }
        else:
            results["unchanged_ships"].append(ship)
            results["comparisons"][ship] = {
                "changed": False,
                "note": "No changes detected"
            }

    return results


def update_armada_map(calibration_data: dict, comparison_results: dict = None) -> bool:
    """Auto-update ARMADA_MAP.md with calibration results.

    Updates:
    1. Header metadata (Last Calibration date, Fleet Status)
    2. Baseline History table (adds new row)

    Args:
        calibration_data: Dict with keys: working_count, ghost_count, rate_limited_count, total_models, timestamp
        comparison_results: Optional comparison results with change counts

    Returns:
        True if update succeeded, False otherwise
    """
    if not ARMADA_MAP_PATH.exists():
        print(f"  WARNING: ARMADA_MAP.md not found at {ARMADA_MAP_PATH}")
        return False

    try:
        with open(ARMADA_MAP_PATH, 'r', encoding='utf-8') as f:
            content = f.read()

        # Extract calibration metadata
        working = calibration_data.get("working_count", 0)
        total = calibration_data.get("total_models", 0)
        ghost = calibration_data.get("ghost_count", 0)
        rate_limited = calibration_data.get("rate_limited_count", 0)
        timestamp = calibration_data.get("timestamp", datetime.now().isoformat())
        baseline_file = calibration_data.get("baseline_file", "S7_baseline_LATEST.json")

        # Parse date from timestamp
        try:
            dt = datetime.fromisoformat(timestamp.replace("Z", "+00:00"))
            date_str = dt.strftime("%B %d, %Y")  # e.g., "December 13, 2025"
            date_short = dt.strftime("%Y-%m-%d")  # e.g., "2025-12-13"
        except:
            date_str = "Unknown"
            date_short = "Unknown"

        operational_pct = round(working / total * 100) if total > 0 else 0

        # 1. Update header metadata
        # Replace: **Last Calibration:** December 10, 2025
        content = re.sub(
            r'\*\*Last Calibration:\*\* .+',
            f'**Last Calibration:** {date_str}',
            content
        )

        # Replace: **Fleet Status:** 47 operational / 59 total (80% operational)
        content = re.sub(
            r'\*\*Fleet Status:\*\* \d+ operational / \d+ total \(\d+% operational\)',
            f'**Fleet Status:** {working} operational / {total} total ({operational_pct}% operational)',
            content
        )

        # 2. Update Fleet Overview table
        content = re.sub(
            r'\| \*\*Total Ships\*\* \| \d+ \|',
            f'| **Total Ships** | {total} |',
            content
        )
        content = re.sub(
            r'\| \*\*Operational\*\* \| \d+ \|',
            f'| **Operational** | {working} |',
            content
        )
        content = re.sub(
            r'\| \*\*Rate Limited\*\* \| \d+ \|',
            f'| **Rate Limited** | {rate_limited} |',
            content
        )
        content = re.sub(
            r'\| \*\*Ghost Ships\*\* \| \d+ \|',
            f'| **Ghost Ships** | {ghost} |',
            content
        )

        # 3. Update Baseline History table
        # Determine notable changes text
        if comparison_results:
            changed = len(comparison_results.get("changed_ships", []))
            new_ships = len(comparison_results.get("new_ships", []))
            missing = len(comparison_results.get("missing_ships", []))
            if changed > 0 or new_ships > 0 or missing > 0:
                notable = f"{changed} changed, {new_ships} new, {missing} missing"
            else:
                notable = "No changes"
        else:
            notable = "Initial capture"

        # New history row
        new_row = f"| {date_short} | {working} | {notable} | `{Path(baseline_file).name}` |"

        # Check if "Awaiting first capture" placeholder exists
        if "*Awaiting first capture*" in content:
            content = content.replace(
                "| *Awaiting first capture* | - | - | - |",
                new_row
            )
        else:
            # Find the history table and add new row at top (after header)
            # Pattern: | Date | Ships Captured | Notable Changes | File |
            # Followed by: |------|----------------|-----------------|------|
            history_pattern = r'(\| Date \| Ships Captured \| Notable Changes \| File \|\n\|[-|]+\|)\n'
            match = re.search(history_pattern, content)
            if match:
                # Insert new row after the header separator
                insert_pos = match.end()
                content = content[:insert_pos] + new_row + "\n" + content[insert_pos:]

        # Write back
        with open(ARMADA_MAP_PATH, 'w', encoding='utf-8') as f:
            f.write(content)

        print(f"  ARMADA_MAP.md updated: {working}/{total} ships, {date_str}")
        return True

    except Exception as e:
        print(f"  WARNING: Failed to update ARMADA_MAP.md: {e}")
        return False


def print_report(results: dict, verbose: bool = False):
    """Print comparison report to console."""
    print("\n" + "=" * 70)
    print("BASELINE COMPARISON REPORT")
    print("=" * 70)

    print(f"\nOld baseline: {results['old_count']} ships")
    print(f"New baseline: {results['new_count']} ships")

    # New ships
    if results["new_ships"]:
        print(f"\n NEW SHIPS ({len(results['new_ships'])}):")
        for ship in results["new_ships"]:
            print(f"    + {ship}")

    # Missing ships
    if results["missing_ships"]:
        print(f"\n MISSING SHIPS ({len(results['missing_ships'])}):")
        for ship in results["missing_ships"]:
            print(f"    - {ship}")

    # Changed ships
    if results["changed_ships"]:
        print(f"\n CHANGED SHIPS ({len(results['changed_ships'])}):")
        for ship in results["changed_ships"]:
            print(f"\n    {ship}:")
            for change in results["comparisons"][ship]["changes"]:
                print(f"      [{change['section']}]")
                if verbose:
                    print(f"        OLD: {change['old']}")
                    print(f"        NEW: {change['new']}")
                else:
                    print(f"        (use --verbose to see details)")

    # Summary
    print("\n" + "-" * 70)
    print("SUMMARY:")
    print(f"  Changed: {len(results['changed_ships'])}")
    print(f"  Unchanged: {len(results['unchanged_ships'])}")
    print(f"  New: {len(results['new_ships'])}")
    print(f"  Missing: {len(results['missing_ships'])}")
    print("=" * 70)


def main():
    parser = argparse.ArgumentParser(description="Compare baseline captures")
    parser.add_argument("--old", required=True, help="Old baseline JSON file")
    parser.add_argument("--new", required=True, help="New baseline JSON file")
    parser.add_argument("--ship", help="Filter to specific ship (partial match)")
    parser.add_argument("--verbose", "-v", action="store_true", help="Show full diff details")
    parser.add_argument("--output", "-o", help="Save comparison to JSON file")
    args = parser.parse_args()

    # Resolve paths
    old_path = CALIBRATION_DIR / args.old if not Path(args.old).is_absolute() else Path(args.old)
    new_path = CALIBRATION_DIR / args.new if not Path(args.new).is_absolute() else Path(args.new)

    if not old_path.exists():
        print(f"ERROR: Old baseline not found: {old_path}")
        return 1
    if not new_path.exists():
        print(f"ERROR: New baseline not found: {new_path}")
        return 1

    print(f"Comparing baselines...")
    print(f"  OLD: {old_path.name}")
    print(f"  NEW: {new_path.name}")

    old_data = load_baseline(old_path)
    new_data = load_baseline(new_path)

    results = compare_ships(old_data, new_data, args.ship)
    results["old_file"] = str(old_path)
    results["new_file"] = str(new_path)

    print_report(results, args.verbose)

    # Save if requested
    if args.output:
        output_path = CALIBRATION_DIR / args.output if not Path(args.output).is_absolute() else Path(args.output)
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2)
        print(f"\nComparison saved to: {output_path}")

    return 0


if __name__ == "__main__":
    exit(main())


# =============================================================================
# Related Documents
# =============================================================================
# - ARCHITECTURE_MATRIX.json: Fleet configuration (ONE SOURCE OF TRUTH)
# - 5_METHODOLOGY_DOMAINS.md: Methodology reference
# - 0_RUN_METHODOLOGY.md: Baseline question definitions
# - ARMADA_MAP.md: Auto-updated by update_armada_map()
# =============================================================================
