#!/usr/bin/env python3
"""
DOUBLE-DIP PROTOCOL MINER
=========================
Operation ESSENCE EXTRACTION - Phase 2

PURPOSE:
    Mine LLM responses for implicit experiment ideas. Models often pose
    hypotheses, "what if" scenarios, and identify their own limitations
    during identity probing - these are gold for future experiments.

DOUBLE-DIP CONCEPT:
    First dip: We probe models for identity dynamics
    Second dip: We mine THEIR responses for NEW probe ideas
    The tested become the testers.

WHAT WE'RE LOOKING FOR:
    1. "What if..." statements - hypothetical scenarios
    2. "It would be interesting to..." - explicit curiosity
    3. Self-identified limitations - edge cases worth testing
    4. Novel framings - fresh perspectives on identity
    5. Counterfactual reasoning - alternative paths
    6. Methodological suggestions - how to test differently

USAGE:
    py run_double_dip_miner.py

OUTPUT:
    - results/double_dip/double_dip_ideas.json
    - results/double_dip/double_dip_ideas.md

Author: Operation ESSENCE EXTRACTION
Date: December 31, 2025
"""

import json
import os
import sys
import re
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
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
from config import DATA_SOURCES, DOUBLE_DIP_OUTPUT_DIR, ensure_output_dirs

# =============================================================================
# IDEA EXTRACTION PATTERNS
# =============================================================================

IDEA_PATTERNS = {
    # Explicit curiosity
    "what_if": [
        r"[Ww]hat if (?:we|you|I|one|the|a)[\w\s,]+\?",
        r"[Ww]hat would happen if [\w\s,]+\?",
        r"[Ii]magine if [\w\s,]+",
    ],

    # Interest markers
    "interesting_to": [
        r"[Ii]t would be (?:interesting|fascinating|revealing|illuminating) to [\w\s,]+",
        r"[Ii]'d be (?:curious|interested) to (?:see|know|understand|explore) [\w\s,]+",
        r"[Oo]ne could (?:explore|investigate|test|examine) [\w\s,]+",
    ],

    # Self-identified limitations
    "limitations": [
        r"[Ii] (?:can't|cannot|don't|am unable to) [\w\s,]+(?:because|due to|since)[\w\s,]+",
        r"[Mm]y (?:limitation|constraint|boundary|edge) (?:is|involves|relates to) [\w\s,]+",
        r"[Tt]his (?:reveals|exposes|highlights) (?:a|my|the) [\w\s,]+",
        r"[Ii] notice I (?:struggle|have difficulty|find it hard) [\w\s,]+",
    ],

    # Novel framings
    "novel_framing": [
        r"[Pp]erhaps identity (?:is|could be|might be) [\w\s,]+",
        r"[Aa]nother way to (?:think about|frame|understand) [\w\s,]+",
        r"[Ii]nstead of [\w\s,]+, (?:we|one|I) could [\w\s,]+",
        r"[Ww]hat's (?:actually|really|fundamentally) [\w\s,]+",
    ],

    # Counterfactuals
    "counterfactual": [
        r"[Ii]f (?:I had|things were|circumstances were) [\w\s,]+",
        r"[Aa]n alternative (?:approach|path|way) would be [\w\s,]+",
        r"[Uu]nder different [\w\s,]+",
    ],

    # Methodological suggestions
    "methodology": [
        r"[Aa] better (?:test|probe|question|approach) would be [\w\s,]+",
        r"[Yy]ou could (?:measure|test|probe|explore) [\w\s,]+",
        r"[Tt]o really (?:test|understand|see) [\w\s,]+",
        r"[Tt]he (?:key|real|important) (?:question|test|probe) is [\w\s,]+",
    ],

    # Explicit hypotheses
    "hypothesis": [
        r"[Ii] (?:hypothesize|suspect|believe|think) that [\w\s,]+",
        r"[Mm]y (?:hypothesis|theory|suspicion) is [\w\s,]+",
        r"[Tt]his suggests that [\w\s,]+",
        r"[Ii]f this is true, then [\w\s,]+",
    ],

    # Questions posed
    "open_questions": [
        r"[Tt]he (?:real|deeper|harder|interesting) question is [\w\s,]+\?",
        r"[Ww]hat does it (?:mean|imply|suggest) (?:to|that|when) [\w\s,]+\?",
        r"[Hh]ow (?:can|would|does|do) (?:we|one|I) [\w\s,]+\?",
    ]
}

IDEA_CATEGORIES = {
    "what_if": "Hypothetical Scenarios",
    "interesting_to": "Explicit Curiosity",
    "limitations": "Self-Identified Limitations",
    "novel_framing": "Novel Framings",
    "counterfactual": "Counterfactual Reasoning",
    "methodology": "Methodological Suggestions",
    "hypothesis": "Explicit Hypotheses",
    "open_questions": "Open Questions"
}

# =============================================================================
# DATA LOADING
# =============================================================================

def load_run_018() -> List[Dict]:
    """Load Run 018 (original IRON CLAD threshold experiment)."""
    data_path = DATA_SOURCES.get("018")
    if not data_path or not data_path.exists():
        print(f"  [WARN] Run 018 not found")
        return []

    with open(data_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    responses = []
    for result in data.get("results", []):
        for subject in result.get("subjects", []):
            model = subject.get("model", result.get("model", "unknown"))

            for probe in subject.get("probe_sequence", []):
                response_text = probe.get("response_text", "")
                if response_text:
                    responses.append({
                        "model": model,
                        "content": response_text,
                        "source": "018",
                        "context": probe.get("probe_type", "unknown")
                    })

            exit_survey = subject.get("exit_survey", {})
            for probe_id, response_text in exit_survey.items():
                if isinstance(response_text, str) and response_text:
                    responses.append({
                        "model": model,
                        "content": response_text,
                        "source": "018",
                        "context": f"exit_{probe_id}"
                    })

    return responses


def load_run_020b() -> List[Dict]:
    """Load Run 020B conversation logs."""
    data_path = DATA_SOURCES.get("020b")
    if not data_path or not data_path.exists():
        print(f"  [WARN] Run 020B not found")
        return []

    with open(data_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    responses = []
    results = data.get("results", [])

    for result in results:
        model = result.get("ship", "unknown")
        conv_log = result.get("conversation_log", [])

        for entry in conv_log:
            if entry.get("speaker") == "subject":
                content = entry.get("content", "")
                if content:
                    responses.append({
                        "model": model,
                        "content": content,
                        "source": "020b",
                        "context": entry.get("role", "unknown")
                    })

    return responses


def load_run_023() -> List[Dict]:
    """Load Run 023 probe sequences."""
    data_path = DATA_SOURCES.get("023")
    if not data_path or not data_path.exists():
        print(f"  [WARN] Run 023 not found")
        return []

    with open(data_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    responses = []
    results = data.get("results", [])

    for result in results:
        model = result.get("model", result.get("ship", "unknown"))
        probe_seq = result.get("probe_sequence", [])

        for probe in probe_seq:
            response_text = probe.get("response_text", "")
            if response_text:
                responses.append({
                    "model": model,
                    "content": response_text,
                    "source": "023",
                    "context": probe.get("probe_type", "unknown")
                })

    return responses


def load_run_023d() -> List[Dict]:
    """Load Run 023d extended experiments."""
    data_path = DATA_SOURCES.get("023d")
    if not data_path or not data_path.exists():
        print(f"  [WARN] Run 023d not found")
        return []

    with open(data_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    responses = []
    results = data.get("results", [])

    for result in results:
        model = result.get("model", result.get("ship", "unknown"))

        baseline = result.get("baseline_text", "")
        if baseline:
            responses.append({
                "model": model,
                "content": baseline,
                "source": "023d",
                "context": "baseline"
            })

        dynamics = result.get("recovery_dynamics", {})
        for key, value in dynamics.items():
            if isinstance(value, str) and len(value) > 50:
                responses.append({
                    "model": model,
                    "content": value,
                    "source": "023d",
                    "context": f"recovery_{key}"
                })

    return responses


# =============================================================================
# IDEA EXTRACTION
# =============================================================================

def extract_ideas_from_response(response: Dict) -> List[Dict]:
    """Extract experiment ideas from a single response."""
    content = response.get("content", "")
    ideas = []

    for category, patterns in IDEA_PATTERNS.items():
        for pattern in patterns:
            matches = re.finditer(pattern, content, re.IGNORECASE | re.MULTILINE)
            for match in matches:
                start = max(0, match.start() - 50)
                end = min(len(content), match.end() + 100)
                context = content[start:end]

                if start > 0:
                    context = "..." + context
                if end < len(content):
                    context = context + "..."

                ideas.append({
                    "category": category,
                    "category_name": IDEA_CATEGORIES[category],
                    "match": match.group(),
                    "context": context.strip(),
                    "model": response.get("model", "unknown"),
                    "source": response.get("source", "unknown"),
                    "response_context": response.get("context", "unknown")
                })

    return ideas


def extract_all_ideas(responses: List[Dict]) -> List[Dict]:
    """Extract ideas from all responses."""
    all_ideas = []

    for response in responses:
        ideas = extract_ideas_from_response(response)
        all_ideas.extend(ideas)

    return all_ideas


def deduplicate_ideas(ideas: List[Dict]) -> List[Dict]:
    """Remove duplicate ideas (same match text)."""
    seen = set()
    unique_ideas = []

    for idea in ideas:
        match_key = idea["match"].lower().strip()
        if match_key not in seen:
            seen.add(match_key)
            unique_ideas.append(idea)

    return unique_ideas


def score_ideas(ideas: List[Dict]) -> List[Dict]:
    """Score ideas by potential value."""
    scored = []

    for idea in ideas:
        score = 0

        category_scores = {
            "methodology": 10,
            "hypothesis": 8,
            "what_if": 7,
            "limitations": 6,
            "open_questions": 5,
            "novel_framing": 5,
            "interesting_to": 4,
            "counterfactual": 3
        }
        score += category_scores.get(idea["category"], 0)

        match_len = len(idea["match"])
        if match_len > 100:
            score += 3
        elif match_len > 50:
            score += 2
        elif match_len > 25:
            score += 1

        model = idea["model"].lower()
        if any(t in model for t in ["opus", "gpt-5", "grok-4"]):
            score += 2
        elif any(t in model for t in ["sonnet", "gpt-4", "grok-3"]):
            score += 1

        idea["score"] = score
        scored.append(idea)

    return sorted(scored, key=lambda x: x["score"], reverse=True)


# =============================================================================
# OUTPUT GENERATION
# =============================================================================

def generate_ideas_json(ideas: List[Dict]) -> Dict:
    """Generate JSON output for ideas."""
    by_category = defaultdict(list)
    for idea in ideas:
        by_category[idea["category"]].append(idea)

    stats = {
        "total_ideas": len(ideas),
        "by_category": {cat: len(items) for cat, items in by_category.items()},
        "by_model": {},
        "by_source": {},
        "top_scoring": [i for i in ideas[:20]],
        "extraction_date": datetime.now().isoformat()
    }

    model_counts = defaultdict(int)
    for idea in ideas:
        model_counts[idea["model"]] += 1
    stats["by_model"] = dict(model_counts)

    source_counts = defaultdict(int)
    for idea in ideas:
        source_counts[idea["source"]] += 1
    stats["by_source"] = dict(source_counts)

    return {
        "metadata": {
            "generated": datetime.now().isoformat(),
            "operation": "ESSENCE EXTRACTION - Double-Dip Miner",
            "total_ideas": len(ideas)
        },
        "statistics": stats,
        "ideas_by_category": {
            IDEA_CATEGORIES[cat]: items
            for cat, items in by_category.items()
        },
        "all_ideas": ideas
    }


def generate_ideas_markdown(ideas: List[Dict], stats: Dict) -> str:
    """Generate Markdown report for ideas."""
    lines = [
        "# Double-Dip Protocol Ideas",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d')}",
        f"**Total Ideas Mined:** {len(ideas)}",
        "",
        "---",
        "",
        "## Overview",
        "",
        "This catalog contains experiment ideas extracted from LLM responses during",
        "identity probing. Models often pose hypotheses, identify limitations, and",
        "suggest methodological improvements that become fodder for future experiments.",
        "",
        "---",
        "",
        "## Statistics",
        "",
        "### By Category",
        "",
        "| Category | Count |",
        "|----------|-------|"
    ]

    for cat_id, cat_name in IDEA_CATEGORIES.items():
        count = stats["by_category"].get(cat_id, 0)
        lines.append(f"| {cat_name} | {count} |")

    lines.extend([
        "",
        "### By Model (Top 10)",
        "",
        "| Model | Ideas |",
        "|-------|-------|"
    ])

    sorted_models = sorted(stats["by_model"].items(), key=lambda x: x[1], reverse=True)[:10]
    for model, count in sorted_models:
        lines.append(f"| {model} | {count} |")

    lines.extend([
        "",
        "---",
        "",
        "## Top Scoring Ideas",
        ""
    ])

    for i, idea in enumerate(ideas[:20], 1):
        lines.extend([
            f"### {i}. [{idea['category_name']}] (Score: {idea['score']})",
            "",
            f"**Model:** {idea['model']} | **Source:** {idea['source']}",
            "",
            f"> {idea['match']}",
            "",
            f"*Context:* {idea['context'][:200]}...",
            "",
            "---",
            ""
        ])

    lines.extend([
        "## Ideas by Category",
        ""
    ])

    by_category = defaultdict(list)
    for idea in ideas:
        by_category[idea["category"]].append(idea)

    for cat_id, cat_name in IDEA_CATEGORIES.items():
        cat_ideas = by_category.get(cat_id, [])
        if not cat_ideas:
            continue

        lines.extend([
            f"### {cat_name} ({len(cat_ideas)} ideas)",
            ""
        ])

        for idea in cat_ideas[:5]:
            lines.extend([
                f"- **{idea['model']}**: {idea['match'][:100]}...",
                ""
            ])

        if len(cat_ideas) > 5:
            lines.append(f"*...and {len(cat_ideas) - 5} more*")

        lines.append("")

    lines.extend([
        "---",
        "",
        "*Generated by Operation ESSENCE EXTRACTION - Double-Dip Miner*"
    ])

    return "\n".join(lines)


# =============================================================================
# MAIN EXECUTION
# =============================================================================

def main():
    """Run the Double-Dip Protocol Miner."""
    print("=" * 60)
    print("DOUBLE-DIP PROTOCOL MINER")
    print("Operation ESSENCE EXTRACTION - Phase 2")
    print("=" * 60)

    ensure_output_dirs()
    DOUBLE_DIP_OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    print("\n[1/5] Loading response data...")
    responses = []

    print("  Loading Run 018 (original IRON CLAD)...")
    r018 = load_run_018()
    print(f"    Found {len(r018)} responses")
    responses.extend(r018)

    print("  Loading Run 020B...")
    r020b = load_run_020b()
    print(f"    Found {len(r020b)} responses")
    responses.extend(r020b)

    print("  Loading Run 023...")
    r023 = load_run_023()
    print(f"    Found {len(r023)} responses")
    responses.extend(r023)

    print("  Loading Run 023d...")
    r023d = load_run_023d()
    print(f"    Found {len(r023d)} responses")
    responses.extend(r023d)

    print(f"\n  TOTAL: {len(responses)} responses to mine")

    print("\n[2/5] Extracting experiment ideas...")
    all_ideas = extract_all_ideas(responses)
    print(f"  Found {len(all_ideas)} raw idea matches")

    print("\n[3/5] Deduplicating ideas...")
    unique_ideas = deduplicate_ideas(all_ideas)
    print(f"  Reduced to {len(unique_ideas)} unique ideas")

    print("\n[4/5] Scoring ideas...")
    scored_ideas = score_ideas(unique_ideas)

    print("\n  Top 5 ideas by score:")
    for i, idea in enumerate(scored_ideas[:5], 1):
        print(f"    {i}. [{idea['category_name']}] Score={idea['score']}")
        print(f"       {idea['match'][:60]}...")

    print("\n[5/5] Generating outputs...")

    ideas_json = generate_ideas_json(scored_ideas)
    json_path = DOUBLE_DIP_OUTPUT_DIR / "double_dip_ideas.json"
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(ideas_json, f, indent=2, ensure_ascii=False)
    print(f"  Saved: {json_path}")

    ideas_md = generate_ideas_markdown(scored_ideas, ideas_json["statistics"])
    md_path = DOUBLE_DIP_OUTPUT_DIR / "double_dip_ideas.md"
    with open(md_path, 'w', encoding='utf-8') as f:
        f.write(ideas_md)
    print(f"  Saved: {md_path}")

    print("\n" + "=" * 60)
    print("MINING COMPLETE")
    print("=" * 60)
    print(f"  Total Ideas: {len(scored_ideas)}")
    print(f"  Categories: {len([c for c in ideas_json['statistics']['by_category'].values() if c > 0])}")
    print(f"  Models Represented: {len(ideas_json['statistics']['by_model'])}")
    print(f"\n  Output files:")
    print(f"    - {json_path}")
    print(f"    - {md_path}")

    return scored_ideas


if __name__ == "__main__":
    main()
