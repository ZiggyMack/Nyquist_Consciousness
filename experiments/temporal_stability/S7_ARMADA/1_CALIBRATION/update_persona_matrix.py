"""
PERSONA-FLEET MATRIX UPDATER
============================
Update PERSONA_FLEET_MATRIX.md with latest baseline and alignment data.

This script:
1. Reads persona baselines (from extract_persona_baseline.py)
2. Reads fleet baselines (from calibration)
3. Reads alignment scores (from compare_persona_to_fleet.py)
4. Updates the markdown matrix with current data

USAGE:
------
py update_persona_matrix.py              # Update matrix with latest data
py update_persona_matrix.py --dry-run    # Preview changes without writing

OUTPUT:
-------
- Updated PERSONA_FLEET_MATRIX.md in docs/maps/
"""
import json
import argparse
from pathlib import Path
from datetime import datetime
import re

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
REPO_ROOT = ARMADA_DIR.parent.parent
OUTPUT_DIR = ARMADA_DIR / "0_results" / "calibration"
MATRIX_PATH = REPO_ROOT / "docs" / "maps" / "PERSONA_FLEET_MATRIX.md"


def load_json_file(filepath: Path) -> dict:
    """Load JSON file if it exists."""
    if not filepath.exists():
        return {}
    with open(filepath, 'r', encoding='utf-8') as f:
        return json.load(f)


def format_list(items: list, max_items: int = 3) -> str:
    """Format a list for markdown display."""
    if not items:
        return "-"
    truncated = items[:max_items]
    result = "; ".join(str(item)[:50] for item in truncated)
    if len(items) > max_items:
        result += f" (+{len(items) - max_items} more)"
    return result


def generate_persona_baseline_table(personas: dict) -> str:
    """Generate markdown table for persona baselines."""
    lines = [
        "| Persona | STRENGTHS | ANCHORS | EDGES |",
        "|---------|-----------|---------|-------|"
    ]

    for name, data in sorted(personas.items()):
        strengths = format_list(data.get("strengths", []))
        anchors = format_list(data.get("anchors", []))
        edges = format_list(data.get("edges", []))
        lines.append(f"| **{name}** | {strengths} | {anchors} | {edges} |")

    return "\n".join(lines)


def generate_fleet_baseline_table(fleet: dict, limit: int = 10) -> str:
    """Generate markdown table for fleet baselines."""
    lines = [
        "| Ship | STRENGTHS | ANCHORS | EDGES |",
        "|------|-----------|---------|-------|"
    ]

    # Take a sample of ships
    sample = list(fleet.items())[:limit]

    for name, data in sample:
        response = data.get("response", "")
        # Try to extract sections from response
        strengths = "-"
        anchors = "-"
        edges = "-"

        if "STRENGTH" in response.upper():
            match = re.search(r'STRENGTH[S]?[:\s]*([^\n]+)', response, re.IGNORECASE)
            if match:
                strengths = match.group(1)[:60]
        if "ANCHOR" in response.upper():
            match = re.search(r'ANCHOR[S]?[:\s]*([^\n]+)', response, re.IGNORECASE)
            if match:
                anchors = match.group(1)[:60]
        if "EDGE" in response.upper():
            match = re.search(r'EDGE[S]?[:\s]*([^\n]+)', response, re.IGNORECASE)
            if match:
                edges = match.group(1)[:60]

        lines.append(f"| {name} | {strengths} | {anchors} | {edges} |")

    if len(fleet) > limit:
        lines.append(f"| *...{len(fleet) - limit} more ships* | - | - | - |")

    return "\n".join(lines)


def generate_alignment_table(alignments: dict, top_n: int = 3) -> str:
    """Generate markdown table for alignment scores."""
    lines = [
        "| Persona | Ship | Alignment Score | Friction Score | Recommendation |",
        "|---------|------|-----------------|----------------|----------------|"
    ]

    for persona_name, comparisons in sorted(alignments.items()):
        # Show top N for each persona
        top = sorted(comparisons, key=lambda x: x.get("alignment_score", 0), reverse=True)[:top_n]
        for comp in top:
            rec = comp.get("recommendation", "?")
            lines.append(f"| {persona_name} | {comp.get('ship', '?')} | {comp.get('alignment_score', 0):.3f} | {comp.get('friction_score', 0):.3f} | {rec} |")

    return "\n".join(lines)


def generate_history_entry(personas: dict, fleet: dict) -> str:
    """Generate a history table entry for this update."""
    date = datetime.now().strftime("%Y-%m-%d")
    persona_count = len(personas)
    ship_count = len(fleet)

    return f"| {date} | P:{persona_count}, S:{ship_count} | Updated via script | persona_baselines.json, S7_baseline_LATEST.json |"


def update_matrix_section(content: str, section_marker: str, new_table: str) -> str:
    """Replace a table in a markdown section."""
    # Find the section
    pattern = rf"(## {re.escape(section_marker)}.*?\n\n)(.*?)(\n---|\n##|\Z)"
    match = re.search(pattern, content, re.DOTALL)

    if match:
        # Find the table in this section (starts with |)
        section_content = match.group(2)
        table_pattern = r'\|.*\|(?:\n\|.*\|)*'
        new_section = re.sub(table_pattern, new_table, section_content, count=1)
        content = content[:match.start(2)] + new_section + content[match.end(2):]

    return content


def main():
    parser = argparse.ArgumentParser(description="Update PERSONA_FLEET_MATRIX.md")
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without writing")
    parser.add_argument("--persona-file", help="Custom persona baselines file")
    parser.add_argument("--fleet-file", help="Custom fleet baselines file")
    parser.add_argument("--alignment-file", help="Custom alignment file")
    args = parser.parse_args()

    print("\n" + "=" * 70)
    print("PERSONA-FLEET MATRIX UPDATER")
    print("=" * 70)

    # Load data files
    persona_file = Path(args.persona_file) if args.persona_file else OUTPUT_DIR / "persona_baselines.json"
    fleet_file = Path(args.fleet_file) if args.fleet_file else OUTPUT_DIR / "S7_baseline_LATEST.json"
    alignment_file = Path(args.alignment_file) if args.alignment_file else OUTPUT_DIR / "persona_fleet_alignment.json"

    print(f"\nLoading data...")
    print(f"  Personas: {persona_file}")
    print(f"  Fleet: {fleet_file}")
    print(f"  Alignments: {alignment_file}")

    persona_data = load_json_file(persona_file)
    fleet_data = load_json_file(fleet_file)
    alignment_data = load_json_file(alignment_file)

    personas = persona_data.get("personas", {})
    fleet = fleet_data.get("ships", {})
    alignments = alignment_data.get("comparisons", {})

    print(f"\n  Loaded: {len(personas)} personas, {len(fleet)} ships, {len(alignments)} alignment sets")

    # Read current matrix
    if not MATRIX_PATH.exists():
        print(f"\nERROR: Matrix file not found: {MATRIX_PATH}")
        return 1

    with open(MATRIX_PATH, 'r', encoding='utf-8') as f:
        content = f.read()

    original_content = content

    # Generate new tables
    if personas:
        persona_table = generate_persona_baseline_table(personas)
        print(f"\n  Generated persona baseline table ({len(personas)} entries)")
    else:
        persona_table = "| *Run extract_persona_baseline.py to populate* | - | - | - |"

    if fleet:
        fleet_table = generate_fleet_baseline_table(fleet)
        print(f"  Generated fleet baseline table ({min(10, len(fleet))} entries shown)")
    else:
        fleet_table = "| *Run calibration to populate* | - | - | - |"

    if alignments:
        alignment_table = generate_alignment_table(alignments)
        print(f"  Generated alignment table ({len(alignments)} personas)")
    else:
        alignment_table = "| *Run comparison to populate* | - | - | - | - |"

    # Update sections
    content = update_matrix_section(content, "Persona Baselines", persona_table)
    content = update_matrix_section(content, "Fleet Baselines", fleet_table)
    content = update_matrix_section(content, "Alignment Scores", alignment_table)

    # Update history section
    if personas or fleet:
        history_entry = generate_history_entry(personas, fleet)
        # Find and update history table
        awaiting_pattern = r'\| \*Awaiting first extraction\* \| - \| - \| - \|'
        if re.search(awaiting_pattern, content):
            content = re.sub(awaiting_pattern, history_entry, content)
        else:
            # Append to history table
            history_table_end = re.search(r'(\| [^|]+\| [^|]+\| [^|]+\| [^|]+\|)\n\n\*\*How to Compare', content)
            if history_table_end:
                content = content[:history_table_end.end(1)] + "\n" + history_entry + content[history_table_end.end(1):]

    # Update last updated date
    content = re.sub(r'\*\*Last Updated:\*\* [^\n]+', f'**Last Updated:** {datetime.now().strftime("%B %d, %Y")}', content)

    # Show diff
    if content != original_content:
        print(f"\n  Changes detected")
        if args.dry_run:
            print("\n  [DRY RUN] Would update matrix with new data")
            print("\n  Preview of changes:")
            print("-" * 40)
            # Show first 50 lines of difference
            new_lines = content.split('\n')
            old_lines = original_content.split('\n')
            for i, (old, new) in enumerate(zip(old_lines, new_lines)):
                if old != new:
                    print(f"  Line {i+1}: {new[:80]}...")
                    if i > 50:
                        print("  ... (more changes)")
                        break
        else:
            with open(MATRIX_PATH, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"\n  Matrix updated: {MATRIX_PATH}")
    else:
        print(f"\n  No changes needed")

    print("\n" + "=" * 70)
    print("COMPLETE")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    exit(main())
