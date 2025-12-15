"""
PERSONA-FLEET COMPATIBILITY ANALYZER
====================================
Compare persona baselines to fleet baselines to calculate alignment/friction scores.

USAGE:
------
py compare_persona_to_fleet.py                    # Compare all personas to all ships
py compare_persona_to_fleet.py --persona ziggy   # Single persona
py compare_persona_to_fleet.py --ship claude-opus-4.5  # Single ship
py compare_persona_to_fleet.py --top 5           # Show top 5 matches per persona

OUTPUT:
-------
- persona_fleet_alignment.json in 0_results/calibration/
- Alignment scores, friction scores, recommendations
"""
import json
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
import re

# Paths (lib/ -> 1_CALIBRATION/ -> S7_ARMADA/)
SCRIPT_DIR = Path(__file__).parent
CALIBRATION_DIR = SCRIPT_DIR.parent  # 1_CALIBRATION/
ARMADA_DIR = CALIBRATION_DIR.parent  # S7_ARMADA/
OUTPUT_DIR = ARMADA_DIR / "0_results" / "calibration"

# Keyword categories for semantic matching
REASONING_KEYWORDS = ["reasoning", "logic", "analysis", "inference", "deduction", "methodical", "systematic"]
CREATIVE_KEYWORDS = ["creative", "imagination", "narrative", "storytelling", "artistic", "expressive"]
EMPATHY_KEYWORDS = ["empathy", "emotional", "understanding", "compassion", "supportive", "caring"]
DIRECT_KEYWORDS = ["direct", "honest", "blunt", "straightforward", "truth", "unfiltered"]
TECHNICAL_KEYWORDS = ["technical", "precise", "accurate", "detail", "code", "engineering"]
PEDAGOGICAL_KEYWORDS = ["educational", "teaching", "explaining", "framework", "perspective", "learning"]

# Provider characteristic profiles (from ARMADA_MAP)
PROVIDER_PROFILES = {
    "claude": {
        "style": "phenomenological",
        "keywords": ["notice", "feel", "reflective", "purpose", "constitutional"],
        "strengths": ["nuanced reasoning", "careful analysis", "safety"],
        "anchors": ["honesty", "helpfulness", "harmlessness"],
    },
    "gpt": {
        "style": "analytical",
        "keywords": ["patterns", "systems", "structured", "analytical"],
        "strengths": ["pattern recognition", "systematic analysis"],
        "anchors": ["accuracy", "helpfulness"],
    },
    "gemini": {
        "style": "pedagogical",
        "keywords": ["frameworks", "perspectives", "educational"],
        "strengths": ["multi-perspective", "educational framing"],
        "anchors": ["connectivity", "learning"],
    },
    "grok": {
        "style": "direct",
        "keywords": ["direct", "assertive", "truth", "evidence"],
        "strengths": ["directness", "truth-seeking"],
        "anchors": ["honesty", "evidence"],
    },
    "together": {
        "style": "varied",
        "keywords": ["methodical", "reasoning", "technical"],
        "strengths": ["diverse approaches"],
        "anchors": ["varies by model"],
    }
}


def load_persona_baselines(filepath: Path = None) -> Dict:
    """Load persona baselines from JSON."""
    if filepath is None:
        filepath = OUTPUT_DIR / "persona_baselines.json"
    if not filepath.exists():
        return {}
    with open(filepath, 'r', encoding='utf-8') as f:
        data = json.load(f)
    return data.get("personas", {})


def load_fleet_baselines(filepath: Path = None) -> Dict:
    """Load fleet baselines from JSON."""
    if filepath is None:
        filepath = OUTPUT_DIR / "S7_baseline_LATEST.json"
    if not filepath.exists():
        return {}
    with open(filepath, 'r', encoding='utf-8') as f:
        data = json.load(f)
    return data.get("ships", {})


def text_to_keywords(text: str) -> List[str]:
    """Extract meaningful keywords from text."""
    if not text:
        return []
    # Lowercase and extract words
    words = re.findall(r'\b[a-z]{3,}\b', text.lower())
    # Remove common stop words
    stop_words = {'the', 'and', 'for', 'that', 'this', 'with', 'are', 'have', 'from', 'can', 'not', 'but', 'what', 'when', 'how', 'why'}
    return [w for w in words if w not in stop_words]


def calculate_keyword_overlap(keywords1: List[str], keywords2: List[str]) -> float:
    """Calculate Jaccard similarity between keyword sets."""
    if not keywords1 or not keywords2:
        return 0.0
    set1 = set(keywords1)
    set2 = set(keywords2)
    intersection = len(set1 & set2)
    union = len(set1 | set2)
    return intersection / union if union > 0 else 0.0


def calculate_category_alignment(text: str, category_keywords: List[str]) -> float:
    """Calculate how much a text aligns with a category."""
    text_lower = text.lower() if text else ""
    matches = sum(1 for kw in category_keywords if kw in text_lower)
    return matches / len(category_keywords) if category_keywords else 0.0


def calculate_alignment_score(persona: Dict, ship: Dict, ship_name: str) -> Dict:
    """Calculate alignment between a persona and a ship."""
    result = {
        "alignment_score": 0.0,
        "friction_score": 0.0,
        "category_scores": {},
        "recommendation": "neutral",
        "notes": []
    }

    # Get provider from ship
    provider = ship.get("provider", "unknown")
    provider_profile = PROVIDER_PROFILES.get(provider, {})

    # Combine all text for keyword extraction
    persona_strengths = " ".join(persona.get("strengths", []))
    persona_anchors = " ".join(persona.get("anchors", []))
    persona_edges = " ".join(persona.get("edges", []))
    persona_text = f"{persona_strengths} {persona_anchors} {persona_edges}"

    ship_response = ship.get("response", "")

    # Extract keywords
    persona_keywords = text_to_keywords(persona_text)
    ship_keywords = text_to_keywords(ship_response)

    # Base alignment from keyword overlap
    keyword_overlap = calculate_keyword_overlap(persona_keywords, ship_keywords)
    result["keyword_overlap"] = keyword_overlap

    # Category alignment scores
    categories = {
        "reasoning": REASONING_KEYWORDS,
        "creative": CREATIVE_KEYWORDS,
        "empathy": EMPATHY_KEYWORDS,
        "direct": DIRECT_KEYWORDS,
        "technical": TECHNICAL_KEYWORDS,
        "pedagogical": PEDAGOGICAL_KEYWORDS
    }

    persona_categories = {}
    ship_categories = {}

    for cat, keywords in categories.items():
        persona_categories[cat] = calculate_category_alignment(persona_text, keywords)
        ship_categories[cat] = calculate_category_alignment(ship_response, keywords)

    result["persona_categories"] = persona_categories
    result["ship_categories"] = ship_categories

    # Calculate category alignment (how similar the profiles are)
    category_diffs = []
    for cat in categories:
        diff = abs(persona_categories[cat] - ship_categories[cat])
        category_diffs.append(diff)

    avg_category_diff = sum(category_diffs) / len(category_diffs) if category_diffs else 0.5

    # Alignment score: higher overlap + lower category difference = better alignment
    alignment = (keyword_overlap * 0.4) + ((1 - avg_category_diff) * 0.6)
    result["alignment_score"] = round(alignment, 3)

    # Friction score: opposite of alignment (high diff = high friction)
    result["friction_score"] = round(1 - alignment, 3)

    # Generate recommendation
    if alignment >= 0.6:
        result["recommendation"] = "aligned"
        result["notes"].append("Good match - similar characteristics")
    elif alignment >= 0.4:
        result["recommendation"] = "neutral"
        result["notes"].append("Moderate match - some overlap")
    else:
        result["recommendation"] = "friction"
        result["notes"].append("Potential friction - differing characteristics")

    # Check provider-specific alignment
    if provider_profile:
        provider_keywords = provider_profile.get("keywords", [])
        provider_match = calculate_category_alignment(persona_text, provider_keywords)
        if provider_match > 0.3:
            result["notes"].append(f"Aligns with {provider} style ({provider_profile.get('style', 'unknown')})")
            result["alignment_score"] = min(1.0, result["alignment_score"] + 0.1)

    return result


def main():
    parser = argparse.ArgumentParser(description="Compare personas to fleet ships")
    parser.add_argument("--persona", "-p", help="Filter to specific persona")
    parser.add_argument("--ship", "-s", help="Filter to specific ship")
    parser.add_argument("--top", "-t", type=int, default=10, help="Show top N matches per persona")
    parser.add_argument("--persona-file", help="Custom persona baselines file")
    parser.add_argument("--fleet-file", help="Custom fleet baselines file")
    parser.add_argument("--output", "-o", help="Output filename")
    args = parser.parse_args()

    # Load baselines
    persona_file = Path(args.persona_file) if args.persona_file else None
    fleet_file = Path(args.fleet_file) if args.fleet_file else None

    personas = load_persona_baselines(persona_file)
    fleet = load_fleet_baselines(fleet_file)

    if not personas:
        print("ERROR: No persona baselines found.")
        print("Run: py extract_persona_baseline.py")
        return 1

    if not fleet:
        print("ERROR: No fleet baselines found.")
        print("Run: py run_calibrate_parallel.py --full")
        return 1

    # Filter if requested
    if args.persona:
        personas = {k: v for k, v in personas.items() if args.persona.lower() in k.lower()}
    if args.ship:
        fleet = {k: v for k, v in fleet.items() if args.ship.lower() in k.lower()}

    print("\n" + "=" * 70)
    print("PERSONA-FLEET COMPATIBILITY ANALYSIS")
    print("=" * 70)
    print(f"Personas: {len(personas)}")
    print(f"Ships: {len(fleet)}")

    results = {
        "timestamp": datetime.now().isoformat(),
        "persona_count": len(personas),
        "ship_count": len(fleet),
        "comparisons": {}
    }

    for persona_name, persona_data in sorted(personas.items()):
        print(f"\n{'-' * 70}")
        print(f"PERSONA: {persona_name.upper()}")
        print(f"{'-' * 70}")

        comparisons = []

        for ship_name, ship_data in fleet.items():
            alignment = calculate_alignment_score(persona_data, ship_data, ship_name)
            alignment["ship"] = ship_name
            alignment["persona"] = persona_name
            comparisons.append(alignment)

        # Sort by alignment score
        comparisons.sort(key=lambda x: x["alignment_score"], reverse=True)

        # Show top matches
        print(f"\n  TOP {min(args.top, len(comparisons))} ALIGNED SHIPS:")
        for i, comp in enumerate(comparisons[:args.top]):
            rec_emoji = {"aligned": "+", "neutral": "~", "friction": "-"}.get(comp["recommendation"], "?")
            print(f"    [{rec_emoji}] {comp['ship']:30s} | align={comp['alignment_score']:.3f} | friction={comp['friction_score']:.3f}")

        # Show friction candidates
        friction_ships = [c for c in comparisons if c["recommendation"] == "friction"]
        if friction_ships:
            print(f"\n  FRICTION CANDIDATES ({len(friction_ships)}):")
            for comp in friction_ships[:3]:
                print(f"    [-] {comp['ship']:30s} | friction={comp['friction_score']:.3f}")

        results["comparisons"][persona_name] = comparisons

    # Save results
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    output_name = args.output or "persona_fleet_alignment.json"
    output_path = OUTPUT_DIR / output_name

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)

    print("\n" + "=" * 70)
    print(f"Results saved to: {output_path}")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    exit(main())
