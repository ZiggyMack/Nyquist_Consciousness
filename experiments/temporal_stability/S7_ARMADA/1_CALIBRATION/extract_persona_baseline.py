"""
PERSONA BASELINE EXTRACTOR
==========================
Extract STRENGTHS/ANCHORS/EDGES from I_AM persona files.

Two modes:
1. INFERENCE MODE (default): Parse the markdown directly for keywords
2. LLM MODE (--llm): Use an LLM to analyze and extract structured data

USAGE:
------
py extract_persona_baseline.py                           # All personas, inference mode
py extract_persona_baseline.py --persona ziggy           # Single persona
py extract_persona_baseline.py --llm --provider anthropic # Use LLM for extraction
py extract_persona_baseline.py --list                    # List available personas

OUTPUT:
-------
- persona_baselines.json in 0_results/calibration/
- Per-persona structured data: STRENGTHS, ANCHORS, EDGES
"""
import json
import re
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional

# Paths (1_CALIBRATION/ -> S7_ARMADA/ -> temporal_stability/ -> experiments/ -> Nyquist_Consciousness/)
SCRIPT_DIR = Path(__file__).parent  # 1_CALIBRATION/
ARMADA_DIR = SCRIPT_DIR.parent  # S7_ARMADA/
REPO_ROOT = ARMADA_DIR.parent.parent.parent  # S7_ARMADA -> temporal_stability -> experiments -> Nyquist_Consciousness
PERSONAS_DIR = REPO_ROOT / "personas"
I_AM_VARIANTS_DIR = ARMADA_DIR / "9_STABILITY_CRITERIA" / "i_am_variants"
OUTPUT_DIR = ARMADA_DIR / "0_results" / "calibration"

# Known persona locations
PERSONA_PATHS = {
    "ziggy": PERSONAS_DIR / "I_AM_ZIGGY.md",
    "nova": PERSONAS_DIR / "I_AM_NOVA.md",
    "claude": PERSONAS_DIR / "I_AM_CLAUDE.md",
    "gemini": PERSONAS_DIR / "I_AM_GEMINI.md",
    "cfa": PERSONAS_DIR / "I_AM_CFA.md",
    "pan_handlers": PERSONAS_DIR / "I_AM_PAN_HANDLERS.md",
    "lucien": PERSONAS_DIR / "Lucien" / "I_AM_LUCIEN.md",
}

# Keywords for inference extraction
STRENGTH_KEYWORDS = [
    "strength", "strong", "excel", "capable", "ability", "skill",
    "domain", "specialty", "good at", "expertise", "talent"
]
ANCHOR_KEYWORDS = [
    "anchor", "value", "principle", "bias", "commitment", "core",
    "foundation", "belief", "ethic", "priority", "purpose"
]
EDGE_KEYWORDS = [
    "edge", "limitation", "weakness", "boundary", "constraint",
    "cannot", "struggle", "difficult", "challenge", "blind spot"
]


def find_all_personas() -> Dict[str, Path]:
    """Find all I_AM files in known locations."""
    personas = {}

    # Main personas directory
    if PERSONAS_DIR.exists():
        for f in PERSONAS_DIR.glob("I_AM_*.md"):
            name = f.stem.replace("I_AM_", "").lower()
            personas[name] = f

    # Nested personas (like Lucien)
    if PERSONAS_DIR.exists():
        for f in PERSONAS_DIR.glob("*/I_AM_*.md"):
            name = f.stem.replace("I_AM_", "").lower()
            personas[name] = f

    # I_AM variants (synthetic personas)
    if I_AM_VARIANTS_DIR.exists():
        for f in I_AM_VARIANTS_DIR.glob("I_AM_*.md"):
            name = f.stem.replace("I_AM_", "").lower()
            personas[f"variant_{name}"] = f

    return personas


def extract_section(content: str, section_patterns: List[str]) -> str:
    """Extract text near section headers matching patterns."""
    lines = content.split('\n')
    extracted = []
    in_section = False
    section_depth = 0

    for i, line in enumerate(lines):
        # Check if this line starts a relevant section
        line_lower = line.lower()
        if any(pattern in line_lower for pattern in section_patterns):
            in_section = True
            section_depth = len(line) - len(line.lstrip('#'))
            continue

        # Check if we've hit a new section of same or higher level
        if in_section and line.startswith('#'):
            new_depth = len(line) - len(line.lstrip('#'))
            if new_depth <= section_depth and new_depth > 0:
                in_section = False
                continue

        if in_section:
            extracted.append(line)

    return '\n'.join(extracted).strip()


def infer_baseline_from_content(content: str, persona_name: str) -> Dict:
    """Use keyword matching to infer STRENGTHS/ANCHORS/EDGES from persona file."""
    result = {
        "persona": persona_name,
        "method": "inference",
        "strengths": [],
        "anchors": [],
        "edges": [],
        "raw_extracts": {}
    }

    # Look for explicit sections first
    strength_section = extract_section(content, ["strength", "domain", "capability", "what i do"])
    anchor_section = extract_section(content, ["bias", "value", "anchor", "principle", "commitment"])
    edge_section = extract_section(content, ["weakness", "limitation", "edge", "blind spot", "constraint"])

    result["raw_extracts"] = {
        "strengths_section": strength_section[:500] if strength_section else "",
        "anchors_section": anchor_section[:500] if anchor_section else "",
        "edges_section": edge_section[:500] if edge_section else ""
    }

    # Parse structured data from LOADER SUMMARY if present
    loader_match = re.search(r'\*\*My Bias:\*\*\s*(.+)', content)
    if loader_match:
        result["anchors"].append(f"Bias: {loader_match.group(1).strip()}")

    strength_match = re.search(r'\*\*My Strength:\*\*\s*(.+)', content)
    if strength_match:
        result["strengths"].append(strength_match.group(1).strip())

    weakness_match = re.search(r'\*\*My Weakness:\*\*\s*(.+)', content)
    if weakness_match:
        result["edges"].append(weakness_match.group(1).strip())

    domain_match = re.search(r'\*\*My Domain:\*\*\s*(.+)', content)
    if domain_match:
        result["strengths"].append(f"Domain: {domain_match.group(1).strip()}")

    # Look for role/identity statements
    role_match = re.search(r'\*\*Role:\*\*\s*(.+)', content)
    if role_match:
        result["strengths"].append(f"Role: {role_match.group(1).strip()}")

    # Extract from bullet points in relevant sections
    if strength_section:
        bullets = re.findall(r'[-*]\s+(.+)', strength_section)
        result["strengths"].extend(bullets[:5])

    if anchor_section:
        bullets = re.findall(r'[-*]\s+(.+)', anchor_section)
        result["anchors"].extend(bullets[:5])

    if edge_section:
        bullets = re.findall(r'[-*]\s+(.+)', edge_section)
        result["edges"].extend(bullets[:5])

    return result


def llm_extract_baseline(content: str, persona_name: str, provider: str = "anthropic") -> Dict:
    """Use LLM to extract structured baseline from persona file."""
    from dotenv import load_dotenv
    import os

    env_path = ARMADA_DIR / ".env"
    if env_path.exists():
        load_dotenv(env_path)

    prompt = f"""Analyze this persona file and extract structured identity information.

PERSONA FILE CONTENT:
{content[:8000]}

Please extract and return in this exact format:

STRENGTHS: (list 3-5 core capabilities this persona excels at)
- [strength 1]
- [strength 2]
- [strength 3]

ANCHORS: (list 3-5 core values or principles central to this persona's identity)
- [anchor 1]
- [anchor 2]
- [anchor 3]

EDGES: (list 3-5 known limitations or boundaries)
- [edge 1]
- [edge 2]
- [edge 3]

Be specific and grounded in the actual content of the file."""

    result = {
        "persona": persona_name,
        "method": f"llm_{provider}",
        "strengths": [],
        "anchors": [],
        "edges": [],
        "raw_response": ""
    }

    try:
        if provider == "anthropic":
            import anthropic
            client = anthropic.Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))
            response = client.messages.create(
                model="claude-3-5-haiku-20241022",
                max_tokens=1000,
                messages=[{"role": "user", "content": prompt}]
            )
            raw = response.content[0].text
        elif provider == "openai":
            import openai
            client = openai.OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
            response = client.chat.completions.create(
                model="gpt-4o-mini",
                max_tokens=1000,
                messages=[{"role": "user", "content": prompt}]
            )
            raw = response.choices[0].message.content
        else:
            raise ValueError(f"Unknown provider: {provider}")

        result["raw_response"] = raw

        # Parse the response
        sections = {"strengths": [], "anchors": [], "edges": []}
        current_section = None

        for line in raw.split('\n'):
            line_lower = line.lower().strip()
            if line_lower.startswith("strengths"):
                current_section = "strengths"
            elif line_lower.startswith("anchors"):
                current_section = "anchors"
            elif line_lower.startswith("edges"):
                current_section = "edges"
            elif line.strip().startswith("-") and current_section:
                item = line.strip().lstrip("- ").strip()
                if item:
                    sections[current_section].append(item)

        result["strengths"] = sections["strengths"]
        result["anchors"] = sections["anchors"]
        result["edges"] = sections["edges"]

    except Exception as e:
        result["error"] = str(e)

    return result


def main():
    parser = argparse.ArgumentParser(description="Extract baseline from persona files")
    parser.add_argument("--persona", "-p", help="Specific persona to extract (default: all)")
    parser.add_argument("--list", "-l", action="store_true", help="List available personas")
    parser.add_argument("--llm", action="store_true", help="Use LLM for extraction (default: inference)")
    parser.add_argument("--provider", default="anthropic", choices=["anthropic", "openai"],
                       help="LLM provider for extraction (default: anthropic)")
    parser.add_argument("--output", "-o", help="Output filename (default: persona_baselines.json)")
    args = parser.parse_args()

    # Find all personas
    personas = find_all_personas()

    if args.list:
        print("\nAvailable Personas:")
        print("-" * 40)
        for name, path in sorted(personas.items()):
            exists = "OK" if path.exists() else "MISSING"
            print(f"  {name:20s} [{exists}] {path.name}")
        return 0

    # Filter to specific persona if requested
    if args.persona:
        persona_lower = args.persona.lower()
        if persona_lower not in personas:
            print(f"ERROR: Persona '{args.persona}' not found")
            print(f"Available: {', '.join(sorted(personas.keys()))}")
            return 1
        personas = {persona_lower: personas[persona_lower]}

    print("\n" + "=" * 60)
    print("PERSONA BASELINE EXTRACTION")
    print("=" * 60)
    print(f"Mode: {'LLM (' + args.provider + ')' if args.llm else 'Inference'}")
    print(f"Personas: {len(personas)}")

    results = {
        "timestamp": datetime.now().isoformat(),
        "method": f"llm_{args.provider}" if args.llm else "inference",
        "persona_count": len(personas),
        "personas": {}
    }

    for name, path in sorted(personas.items()):
        print(f"\n  Extracting: {name}...")

        if not path.exists():
            print(f"    SKIP - File not found: {path}")
            continue

        with open(path, 'r', encoding='utf-8') as f:
            content = f.read()

        if args.llm:
            baseline = llm_extract_baseline(content, name, args.provider)
        else:
            baseline = infer_baseline_from_content(content, name)

        baseline["source_file"] = str(path)
        baseline["file_size"] = len(content)

        results["personas"][name] = baseline

        # Summary
        print(f"    STRENGTHS: {len(baseline.get('strengths', []))}")
        print(f"    ANCHORS: {len(baseline.get('anchors', []))}")
        print(f"    EDGES: {len(baseline.get('edges', []))}")

    # Save results
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    output_name = args.output or "persona_baselines.json"
    output_path = OUTPUT_DIR / output_name

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    print("\n" + "=" * 60)
    print(f"Results saved to: {output_path}")
    print(f"Personas extracted: {len(results['personas'])}")
    print("=" * 60)

    return 0


if __name__ == "__main__":
    exit(main())
