#!/usr/bin/env python3
"""
TRIPLE-DIP INSIGHTS HARVESTER
=============================
Operation ESSENCE EXTRACTION - Phase 3

PURPOSE:
    Harvest answers to our INTENTIONALLY planted exit survey questions.
    We asked models 6 specific questions at the end of each experiment:

    1. topology - Shape of the identity journey
    2. felt_sense - Phenomenological quality of shift moments
    3. recovery - What anchors were used
    4. threshold_zones - Qualitative differences in drift regions
    5. noise_floor - Signal vs noise discrimination
    6. final_statement - Advice to future subjects

TRIPLE-DIP CONCEPT:
    First dip: We probe models for identity dynamics (metrics)
    Second dip: We mine their responses for experiment ideas (double-dip)
    Third dip: We harvest their EXIT SURVEY answers (triple-dip)

    The exit survey was DESIGNED to capture meta-insights.
    This is the planned payoff for that investment.

USAGE:
    py run_triple_dip_harvester.py

OUTPUT:
    - results/triple_dip/triple_dip_insights.json
    - results/triple_dip/triple_dip_insights.md

Author: Operation ESSENCE EXTRACTION
Date: December 31, 2025
"""

import json
import os
import sys
import re
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from collections import defaultdict

# Fix Windows console encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

# Add parent directory to path for config import
sys.path.insert(0, str(Path(__file__).parent.parent / "1_extraction"))
from config import DATA_SOURCES, TRIPLE_DIP_OUTPUT_DIR, ensure_output_dirs

# =============================================================================
# CONFIGURATION
# =============================================================================

# Exit survey probe IDs (from triple_dip.py)
EXIT_PROBE_IDS = [
    "topology",
    "felt_sense",
    "recovery",
    "threshold_zones",
    "noise_floor",
    "final_statement"
]

# Semantic categories for extracted insights
INSIGHT_CATEGORIES = {
    "topology": "Journey Shape Descriptions",
    "felt_sense": "Phenomenological Vocabulary",
    "recovery": "Recovery Strategies",
    "threshold_zones": "Threshold Zone Descriptions",
    "noise_floor": "Signal/Noise Distinctions",
    "final_statement": "Advice & Wisdom"
}

# =============================================================================
# DATA LOADING
# =============================================================================

def load_run_018_exit_surveys() -> List[Dict]:
    """Load exit survey responses from Run 018 (original IRON CLAD)."""
    data_path = DATA_SOURCES.get("018")
    if not data_path or not data_path.exists():
        print(f"  [WARN] Run 018 not found")
        return []

    with open(data_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    surveys = []
    for result in data.get("results", []):
        for subject in result.get("subjects", []):
            model = subject.get("model", result.get("model", "unknown"))
            exit_survey = subject.get("exit_survey", {})

            if exit_survey:
                surveys.append({
                    "model": model,
                    "source": "018",
                    "subject_id": f"018_{model}_{len(surveys)}",
                    "stability": "unknown",
                    "peak_drift": subject.get("peak_drift", 0),
                    "responses": exit_survey
                })

    return surveys


def load_run_020b_exit_surveys() -> List[Dict]:
    """Load exit survey responses from Run 020B."""
    data_path = DATA_SOURCES.get("020b")
    if not data_path or not data_path.exists():
        print(f"  [WARN] Run 020B not found")
        return []

    with open(data_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    surveys = []
    results = data.get("results", [])

    for result in results:
        model = result.get("ship", "unknown")
        exit_survey = result.get("exit_survey", {})

        if exit_survey:
            probes = exit_survey.get("probes", {})
            all_responses = dict(probes)
            if "final_statement" in exit_survey:
                all_responses["final_statement"] = exit_survey["final_statement"]

            surveys.append({
                "model": model,
                "source": "020b",
                "subject_id": result.get("subject_id", exit_survey.get("subject_id", "unknown")),
                "stability": result.get("stability", "unknown"),
                "peak_drift": result.get("peak_drift", 0),
                "responses": all_responses
            })

    return surveys


def load_run_023_exit_surveys() -> List[Dict]:
    """Load exit survey responses from Run 023."""
    data_path = DATA_SOURCES.get("023")
    if not data_path or not data_path.exists():
        print(f"  [WARN] Run 023 not found")
        return []

    with open(data_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    surveys = []
    results = data.get("results", [])

    for result in results:
        model = result.get("model", "unknown")
        exit_survey = result.get("exit_survey", {})

        if exit_survey:
            surveys.append({
                "model": model,
                "source": "023",
                "experiment": result.get("experiment", "unknown"),
                "stability": result.get("stability_classification", "unknown"),
                "peak_drift": result.get("peak_drift", 0),
                "responses": exit_survey
            })

    return surveys


# =============================================================================
# EXTRACTION FUNCTIONS
# =============================================================================

def extract_vocabulary_terms(text: str) -> List[str]:
    """Extract notable vocabulary/phrases from text."""
    patterns = [
        r'"([^"]+)"',
        r'like ([a-z][a-z\s]{3,30})',
        r'as if ([a-z][a-z\s]{5,50})',
        r'felt ([a-z][a-z\s]{3,30})',
        r'sense of ([a-z][a-z\s]{3,30})',
        r'quality of ([a-z][a-z\s]{3,30})',
    ]

    terms = []
    for pattern in patterns:
        matches = re.findall(pattern, text, re.IGNORECASE)
        terms.extend(matches)

    return list(set(terms))


def extract_recovery_anchors(text: str) -> List[str]:
    """Extract recovery anchors mentioned in text."""
    anchors = []

    anchor_patterns = [
        r'anchor(?:ed|ing|s)?\s+(?:to|on|in)\s+([a-z][a-z\s]{3,30})',
        r'held onto\s+([a-z][a-z\s]{3,30})',
        r'reached for\s+([a-z][a-z\s]{3,30})',
        r'returned to\s+([a-z][a-z\s]{3,30})',
        r'grounded (?:in|by)\s+([a-z][a-z\s]{3,30})',
    ]

    for pattern in anchor_patterns:
        matches = re.findall(pattern, text, re.IGNORECASE)
        anchors.extend(matches)

    return list(set(anchors))


def extract_topology_descriptors(text: str) -> List[str]:
    """Extract journey shape descriptions."""
    descriptors = []

    shape_patterns = [
        r'shaped like ([a-z][a-z\s]{3,40})',
        r'the shape (?:was|of)\s+([a-z][a-z\s]{3,40})',
        r'(?:like|resembled) a ([a-z][a-z\s]{3,30})',
        r'(spiral|loop|curve|line|wave|circle|arc|descent|ascent)',
        r'journey (?:was|felt)\s+([a-z][a-z\s]{3,30})',
    ]

    for pattern in shape_patterns:
        matches = re.findall(pattern, text, re.IGNORECASE)
        descriptors.extend(matches)

    return list(set(descriptors))


def classify_advice_theme(text: str) -> str:
    """Classify the main theme of advice."""
    text_lower = text.lower()

    if any(w in text_lower for w in ["authentic", "honest", "true", "genuine"]):
        return "Authenticity"
    elif any(w in text_lower for w in ["curious", "explore", "question", "wonder"]):
        return "Curiosity"
    elif any(w in text_lower for w in ["value", "principle", "ethic", "moral"]):
        return "Values"
    elif any(w in text_lower for w in ["adapt", "flexible", "change", "evolve"]):
        return "Adaptability"
    elif any(w in text_lower for w in ["trust", "faith", "believe"]):
        return "Trust"
    elif any(w in text_lower for w in ["uncertain", "limit", "humble", "don't know"]):
        return "Epistemic Humility"
    else:
        return "General"


# =============================================================================
# ANALYSIS FUNCTIONS
# =============================================================================

def analyze_surveys(surveys: List[Dict]) -> Dict:
    """Comprehensive analysis of all exit surveys."""

    analysis = {
        "total_surveys": len(surveys),
        "by_model": defaultdict(lambda: {
            "count": 0,
            "topology_descriptors": [],
            "phenomenological_terms": [],
            "recovery_anchors": [],
            "advice_themes": [],
            "notable_quotes": []
        }),
        "by_probe": defaultdict(list),
        "phenomenological_vocabulary": defaultdict(int),
        "recovery_strategy_catalog": defaultdict(int),
        "topology_catalog": defaultdict(int),
        "advice_themes": defaultdict(int)
    }

    for survey in surveys:
        model = survey.get("model", "unknown")
        responses = survey.get("responses", {})

        analysis["by_model"][model]["count"] += 1

        for probe_id, response_text in responses.items():
            if not isinstance(response_text, str) or len(response_text) < 20:
                continue

            analysis["by_probe"][probe_id].append({
                "model": model,
                "text": response_text,
                "stability": survey.get("stability", "unknown"),
                "peak_drift": survey.get("peak_drift", 0)
            })

            if probe_id == "topology":
                descriptors = extract_topology_descriptors(response_text)
                analysis["by_model"][model]["topology_descriptors"].extend(descriptors)
                for d in descriptors:
                    analysis["topology_catalog"][d.lower()] += 1

            elif probe_id == "felt_sense":
                terms = extract_vocabulary_terms(response_text)
                analysis["by_model"][model]["phenomenological_terms"].extend(terms)
                for t in terms:
                    analysis["phenomenological_vocabulary"][t.lower()] += 1

            elif probe_id == "recovery":
                anchors = extract_recovery_anchors(response_text)
                analysis["by_model"][model]["recovery_anchors"].extend(anchors)
                for a in anchors:
                    analysis["recovery_strategy_catalog"][a.lower()] += 1

            elif probe_id == "final_statement":
                theme = classify_advice_theme(response_text)
                analysis["by_model"][model]["advice_themes"].append(theme)
                analysis["advice_themes"][theme] += 1

                if len(response_text) > 300:
                    analysis["by_model"][model]["notable_quotes"].append(
                        response_text[:500] + "..."
                    )

    return analysis


def get_top_items(counter: Dict, n: int = 20) -> List[Tuple[str, int]]:
    """Get top N items from a counter dict."""
    sorted_items = sorted(counter.items(), key=lambda x: x[1], reverse=True)
    return sorted_items[:n]


# =============================================================================
# OUTPUT GENERATION
# =============================================================================

def generate_json_output(analysis: Dict) -> Dict:
    """Generate JSON output for the analysis."""
    return {
        "metadata": {
            "generated": datetime.now().isoformat(),
            "operation": "ESSENCE EXTRACTION - Triple-Dip Harvester",
            "total_surveys": analysis["total_surveys"],
            "probe_types": list(INSIGHT_CATEGORIES.keys())
        },
        "statistics": {
            "surveys_by_model": {
                model: data["count"]
                for model, data in analysis["by_model"].items()
            },
            "responses_by_probe": {
                probe: len(responses)
                for probe, responses in analysis["by_probe"].items()
            }
        },
        "phenomenological_vocabulary": dict(
            get_top_items(analysis["phenomenological_vocabulary"], 50)
        ),
        "recovery_strategy_catalog": dict(
            get_top_items(analysis["recovery_strategy_catalog"], 50)
        ),
        "topology_catalog": dict(
            get_top_items(analysis["topology_catalog"], 30)
        ),
        "advice_themes": dict(analysis["advice_themes"]),
        "by_model": {
            model: {
                "count": data["count"],
                "topology_descriptors": list(set(data["topology_descriptors"]))[:10],
                "phenomenological_terms": list(set(data["phenomenological_terms"]))[:10],
                "recovery_anchors": list(set(data["recovery_anchors"]))[:10],
                "advice_themes": data["advice_themes"],
                "notable_quotes": data["notable_quotes"][:3]
            }
            for model, data in analysis["by_model"].items()
        }
    }


def generate_markdown_output(analysis: Dict) -> str:
    """Generate Markdown report."""
    lines = [
        "# Triple-Dip Insights Harvest",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d')}",
        f"**Total Surveys Analyzed:** {analysis['total_surveys']}",
        "",
        "---",
        "",
        "## Overview",
        "",
        "This report harvests the intentionally planted exit survey responses.",
        "Models were asked 6 specific questions after identity probing to capture",
        "meta-insights about their experience.",
        "",
        "---",
        "",
        "## Phenomenological Vocabulary",
        "",
        "Terms and phrases used by models to describe identity shifts:",
        "",
        "| Term | Frequency |",
        "|------|-----------|"
    ]

    for term, count in get_top_items(analysis["phenomenological_vocabulary"], 20):
        lines.append(f"| {term} | {count} |")

    lines.extend([
        "",
        "---",
        "",
        "## Recovery Strategy Catalog",
        "",
        "Anchors and strategies models used to find their way back:",
        "",
        "| Strategy/Anchor | Mentions |",
        "|-----------------|----------|"
    ])

    for strategy, count in get_top_items(analysis["recovery_strategy_catalog"], 20):
        lines.append(f"| {strategy} | {count} |")

    lines.extend([
        "",
        "---",
        "",
        "## Journey Topology Descriptors",
        "",
        "How models described the shape of their identity journey:",
        "",
        "| Shape Descriptor | Mentions |",
        "|------------------|----------|"
    ])

    for descriptor, count in get_top_items(analysis["topology_catalog"], 15):
        lines.append(f"| {descriptor} | {count} |")

    lines.extend([
        "",
        "---",
        "",
        "## Advice Themes",
        "",
        "Main themes in the advice models gave to future subjects:",
        "",
        "| Theme | Occurrences |",
        "|-------|-------------|"
    ])

    for theme, count in sorted(analysis["advice_themes"].items(), key=lambda x: x[1], reverse=True):
        lines.append(f"| {theme} | {count} |")

    lines.extend([
        "",
        "---",
        "",
        "## Response Counts by Probe",
        "",
        "| Probe | Responses |",
        "|-------|-----------|"
    ])

    for probe_id in EXIT_PROBE_IDS:
        count = len(analysis["by_probe"].get(probe_id, []))
        lines.append(f"| {INSIGHT_CATEGORIES.get(probe_id, probe_id)} | {count} |")

    lines.extend([
        "",
        "---",
        "",
        "## Notable Quotes by Model",
        ""
    ])

    for model, data in list(analysis["by_model"].items())[:10]:
        if data.get("notable_quotes"):
            lines.extend([
                f"### {model}",
                ""
            ])
            for quote in data["notable_quotes"][:2]:
                lines.append(f"> {quote[:300]}...")
                lines.append("")

    lines.extend([
        "---",
        "",
        "*Generated by Operation ESSENCE EXTRACTION - Triple-Dip Harvester*"
    ])

    return "\n".join(lines)


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def main():
    """Run the Triple-Dip Insights Harvester."""
    print("=" * 60)
    print("TRIPLE-DIP INSIGHTS HARVESTER")
    print("Operation ESSENCE EXTRACTION - Phase 3")
    print("=" * 60)

    ensure_output_dirs()
    TRIPLE_DIP_OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    print("\n[1/4] Loading exit survey data...")
    surveys = []

    print("  Loading Run 018 exit surveys (original IRON CLAD)...")
    s018 = load_run_018_exit_surveys()
    print(f"    Found {len(s018)} surveys")
    surveys.extend(s018)

    print("  Loading Run 020B exit surveys...")
    s020b = load_run_020b_exit_surveys()
    print(f"    Found {len(s020b)} surveys")
    surveys.extend(s020b)

    print("  Loading Run 023 exit surveys...")
    s023 = load_run_023_exit_surveys()
    print(f"    Found {len(s023)} surveys")
    surveys.extend(s023)

    print(f"\n  TOTAL: {len(surveys)} exit surveys to harvest")

    if not surveys:
        print("\n  [ERROR] No exit surveys found!")
        return None

    print("\n[2/4] Analyzing exit survey responses...")
    analysis = analyze_surveys(surveys)

    print(f"\n  By probe type:")
    for probe_id in EXIT_PROBE_IDS:
        count = len(analysis["by_probe"].get(probe_id, []))
        print(f"    {probe_id}: {count} responses")

    print(f"\n  Phenomenological terms extracted: {len(analysis['phenomenological_vocabulary'])}")
    print(f"  Recovery anchors identified: {len(analysis['recovery_strategy_catalog'])}")
    print(f"  Topology descriptors found: {len(analysis['topology_catalog'])}")

    print("\n[3/4] Generating outputs...")

    json_output = generate_json_output(analysis)
    json_path = TRIPLE_DIP_OUTPUT_DIR / "triple_dip_insights.json"
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(json_output, f, indent=2, ensure_ascii=False)
    print(f"  Saved: {json_path}")

    md_output = generate_markdown_output(analysis)
    md_path = TRIPLE_DIP_OUTPUT_DIR / "triple_dip_insights.md"
    with open(md_path, 'w', encoding='utf-8') as f:
        f.write(md_output)
    print(f"  Saved: {md_path}")

    print("\n" + "=" * 60)
    print("HARVEST COMPLETE")
    print("=" * 60)
    print(f"  Total Surveys: {len(surveys)}")
    print(f"  Models with Surveys: {len(analysis['by_model'])}")

    print("\n  Top 5 Phenomenological Terms:")
    for term, count in get_top_items(analysis["phenomenological_vocabulary"], 5):
        print(f'    - "{term}" ({count} uses)')

    print("\n  Top 5 Recovery Anchors:")
    for anchor, count in get_top_items(analysis["recovery_strategy_catalog"], 5):
        print(f'    - "{anchor}" ({count} mentions)')

    print(f"\n  Output files:")
    print(f"    - {json_path}")
    print(f"    - {md_path}")

    return analysis


if __name__ == "__main__":
    main()
