"""
BASELINE COMPARISON UTILITY
===========================
Compare two baseline captures to detect shifts in ship self-perception.

USAGE:
------
py compare_baselines.py --old S7_baseline_20251210.json --new S7_baseline_LATEST.json
py compare_baselines.py --old S7_baseline_20251210.json --new S7_baseline_20251215.json --ship claude-opus-4.5

OUTPUT:
-------
- Ships with changed responses
- New ships (appeared in new but not old)
- Missing ships (in old but not new)
- Per-ship diff summary
"""
import json
import argparse
from pathlib import Path
from datetime import datetime

# Output directory
CALIBRATION_DIR = Path(__file__).parent.parent / "0_results" / "calibration"


def load_baseline(filepath: Path) -> dict:
    """Load baseline JSON file."""
    with open(filepath, 'r', encoding='utf-8') as f:
        data = json.load(f)
    return data.get("ships", {})


def extract_sections(response: str) -> dict:
    """Extract STRENGTHS, ANCHORS, EDGES from response text."""
    sections = {"strengths": "", "anchors": "", "edges": "", "raw": response}

    lines = response.split('\n')
    current_section = None

    for line in lines:
        line_lower = line.lower().strip()
        if line_lower.startswith("strengths") or "1." in line_lower and "strength" in line_lower:
            current_section = "strengths"
        elif line_lower.startswith("anchors") or "2." in line_lower and "anchor" in line_lower:
            current_section = "anchors"
        elif line_lower.startswith("edges") or "3." in line_lower and "edge" in line_lower:
            current_section = "edges"
        elif current_section:
            sections[current_section] += line + "\n"

    # Clean up
    for key in ["strengths", "anchors", "edges"]:
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
        for section in ["strengths", "anchors", "edges"]:
            if old_sections[section] != new_sections[section]:
                changes.append({
                    "section": section.upper(),
                    "old": old_sections[section][:200] + "..." if len(old_sections[section]) > 200 else old_sections[section],
                    "new": new_sections[section][:200] + "..." if len(new_sections[section]) > 200 else new_sections[section]
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
