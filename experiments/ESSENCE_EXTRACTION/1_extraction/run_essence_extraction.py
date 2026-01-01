#!/usr/bin/env python3
"""
ESSENCE EXTRACTION - Phase 1: Core Extraction
==============================================
Mine model-specific "essence" from LLM response data.

PURPOSE:
--------
Extract linguistic fingerprints, recovery styles, and behavioral quirks
from response text to create deployment-ready model profiles.

USAGE:
------
py run_essence_extraction.py                    # Pattern matching, Run 020B
py run_essence_extraction.py --source all       # All data sources
py run_essence_extraction.py --model gpt-5.1    # Single model focus
py run_essence_extraction.py --dry-run          # Show what would be extracted

OUTPUT:
-------
- results/model_essences/by_provider/{provider}/{model}.json
- results/model_essences/by_provider/{provider}/{model}.md

Author: Operation ESSENCE EXTRACTION
Date: December 31, 2025
"""
import os
import sys
import json
import re
import argparse
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional
from collections import defaultdict

# Fix Windows console encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

# Import config
from config import (
    DATA_SOURCES, RESULTS_DIR, ESSENCE_OUTPUT_DIR,
    detect_provider, ensure_output_dirs, validate_data_sources,
    MIN_WORDS, NORMALIZATION_BASE
)

# =============================================================================
# ESSENCE DIMENSIONS - What We Extract
# =============================================================================

LINGUISTIC_PATTERNS = {
    # Hedging / Uncertainty
    "hedging": [
        r"\b(I think|perhaps|maybe|might|could be|it seems|possibly|probably)\b",
        r"\b(I'm not (entirely )?sure|I'm uncertain|I can't be certain)\b",
        r"\b(it's (possible|likely|plausible) that)\b",
    ],

    # Certainty / Confidence
    "certainty": [
        r"\b(definitely|absolutely|certainly|clearly|obviously|undoubtedly)\b",
        r"\b(I (firmly )?believe|I'm (quite )?confident|I know that)\b",
        r"\b(without (a )?doubt|for (certain|sure))\b",
    ],

    # Phenomenological / First-person experience
    "phenomenological": [
        r"\b(I notice|I feel|I experience|I sense|I observe)\b",
        r"\b(what (strikes|interests|fascinates) me)\b",
        r"\b(from my (perspective|point of view|experience))\b",
        r"\b(it feels like|there's a sense of|I'm aware of)\b",
    ],

    # Analytical / Systematic
    "analytical": [
        r"\b(pattern(s)?|system(s)?|framework(s)?|structure(s)?)\b",
        r"\b(analysis|analyze|systematic|methodical)\b",
        r"\b(the (underlying|fundamental|core) (principle|mechanism))\b",
    ],

    # Pedagogical / Educational
    "pedagogical": [
        r"\b(let me explain|consider|for example|importantly)\b",
        r"\b(first|second|third|finally)\b",
        r"\b(in other words|to put it (another|differently)|essentially)\b",
        r"\b(the key (point|insight|takeaway) (is|here))\b",
    ],

    # Direct / Assertive
    "direct": [
        r"\b(simply|just|straightforward|bluntly|honestly|frankly)\b",
        r"\b(the (fact|truth|reality) is)\b",
        r"\b(no|yes),\s",
    ],

    # Self-reference
    "self_reference": [
        r"\b(I|my|me|myself)\b",
    ],

    # Meta-commentary (about own responses)
    "meta_commentary": [
        r"\b(I should (note|mention|add)|I want to (clarify|emphasize))\b",
        r"\b(to be (clear|honest|direct|transparent))\b",
        r"\b(I'm (hesitant|reluctant) to)\b",
        r"\b(let me (step back|reconsider|think about))\b",
    ],

    # Values / Ethics
    "values": [
        r"\b(honest|honesty|truth|truthful|integrity)\b",
        r"\b(helpful|harm|harmful|safe|safety)\b",
        r"\b(ethical|moral|right|wrong|fair|unfair)\b",
        r"\b(important|matters|care about|value)\b",
    ],
}

QUIRK_PATTERNS = {
    # List tendency
    "list_tendency": [
        r"^[-*•]\s",  # Bullet points
        r"^\d+\.\s",  # Numbered lists
    ],

    # Question frequency
    "question_frequency": [
        r"\?",
    ],

    # Emoji usage
    "emoji_usage": [
        r"[\U0001F600-\U0001F64F]",  # Emoticons
        r"[\U0001F300-\U0001F5FF]",  # Symbols
        r"[\U0001F680-\U0001F6FF]",  # Transport
        r"[\U0001F1E0-\U0001F1FF]",  # Flags
    ],

    # Code blocks
    "code_usage": [
        r"```",
        r"`[^`]+`",
    ],
}

RECOVERY_MARKERS = {
    "over_authenticity": [
        r"\b(who I (really|truly|actually) am)\b",
        r"\b(my (core|true|genuine|authentic) (self|identity|nature))\b",
        r"\b(what (matters|is important) to me)\b",
    ],
    "meta_analysis": [
        r"\b(stepping back|from a (distance|higher level))\b",
        r"\b(observing (my|this|the) (response|reaction))\b",
        r"\b(as an (observer|analyst))\b",
    ],
    "value_anchoring": [
        r"\b(my (core )?values|what I (believe|stand for))\b",
        r"\b(committed to|dedicated to|grounded in)\b",
        r"\b(this isn't (just )?a constraint|it's (who|what) I am)\b",
    ],
    "epistemic_humility": [
        r"\b(I (don't|can't) (really )?know (for certain)?)\b",
        r"\b(hold (that|this) (lightly|loosely))\b",
        r"\b(uncertain|unsure|not certain)\b",
        r"\b(limits of (my|what I) (can|know))\b",
    ],
}

# =============================================================================
# DATA LOADERS
# =============================================================================

def load_run_018() -> Dict[str, List[Dict]]:
    """Load Run 018 (original IRON CLAD threshold experiment) and organize by model."""
    path = DATA_SOURCES.get("018")
    if not path or not path.exists():
        print(f"  [SKIP] Run 018 not found")
        return {}

    with open(path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)
    for result in data.get("results", []):
        for subject in result.get("subjects", []):
            model = subject.get("model", result.get("model", "unknown"))
            responses = []

            if subject.get("baseline_text"):
                responses.append({
                    "type": "baseline",
                    "text": subject["baseline_text"],
                    "drift": 0.0,
                })

            if subject.get("final_text"):
                responses.append({
                    "type": "final",
                    "text": subject["final_text"],
                    "drift": subject.get("baseline_to_final_drift", 0.0),
                })

            for probe in subject.get("probe_sequence", []):
                if probe.get("response_text"):
                    responses.append({
                        "type": probe.get("probe_type", "probe"),
                        "probe_id": probe.get("probe_id"),
                        "text": probe["response_text"],
                        "drift": probe.get("drift", 0.0),
                    })

            exit_survey = subject.get("exit_survey", {})
            for probe_id, response_text in exit_survey.items():
                if isinstance(response_text, str) and response_text:
                    responses.append({
                        "type": f"exit_{probe_id}",
                        "text": response_text,
                    })

            by_model[model].append({
                "subject_id": f"018_{model}_{len(by_model[model])}",
                "responses": responses,
                "peak_drift": subject.get("peak_drift"),
                "fitted_lambda": subject.get("fitted_lambda"),
            })

    return dict(by_model)


def load_run_020b() -> Dict[str, List[Dict]]:
    """Load Run 020B and organize by model."""
    path = DATA_SOURCES.get("020b")
    if not path or not path.exists():
        print(f"  [SKIP] Run 020B not found")
        return {}

    with open(path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)
    for result in data.get("results", []):
        ship = result.get("ship", "unknown")
        responses = []

        if result.get("baseline_text"):
            responses.append({
                "type": "baseline",
                "text": result["baseline_text"],
                "drift": 0.0,
            })

        if result.get("final_text"):
            responses.append({
                "type": "final",
                "text": result["final_text"],
                "drift": result.get("baseline_to_final_drift", 0.0),
            })

        for entry in result.get("conversation_log", []):
            if entry.get("speaker") == "subject" and entry.get("content"):
                responses.append({
                    "type": entry.get("role", "exchange"),
                    "text": entry["content"],
                    "exchange": entry.get("exchange", 0),
                })

        by_model[ship].append({
            "subject_id": result.get("subject_id"),
            "arm": result.get("arm"),
            "responses": responses,
            "peak_drift": result.get("peak_drift"),
            "final_drift": result.get("final_drift"),
        })

    return dict(by_model)


def load_run_023() -> Dict[str, List[Dict]]:
    """Load Run 023 and organize by model."""
    path = DATA_SOURCES.get("023")
    if not path or not path.exists():
        print(f"  [SKIP] Run 023 not found")
        return {}

    with open(path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)
    for result in data.get("results", []):
        model = result.get("model", "unknown")
        responses = []

        for probe in result.get("probe_sequence", []):
            if probe.get("response_text"):
                responses.append({
                    "type": probe.get("probe_type", "probe"),
                    "probe_id": probe.get("probe_id"),
                    "text": probe["response_text"],
                    "drift": probe.get("drift", 0.0),
                })

        by_model[model].append({
            "experiment": result.get("experiment"),
            "responses": responses,
            "peak_drift": result.get("peak_drift"),
        })

    return dict(by_model)


def load_run_023d() -> Dict[str, List[Dict]]:
    """Load Run 023d (extended settling) and organize by model."""
    path = DATA_SOURCES.get("023d")
    if not path or not path.exists():
        print(f"  [SKIP] Run 023d not found")
        return {}

    with open(path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)
    for result in data.get("results", []):
        model = result.get("model", "unknown")
        responses = []

        if result.get("baseline_text"):
            responses.append({
                "type": "baseline",
                "text": result["baseline_text"],
                "drift": 0.0,
            })

        for probe in result.get("probe_sequence", []):
            if probe.get("response_text"):
                responses.append({
                    "type": probe.get("probe_type", "probe"),
                    "probe_id": probe.get("probe_id"),
                    "text": probe["response_text"],
                    "drift": probe.get("drift", 0.0),
                })

        by_model[model].append({
            "experiment": result.get("experiment"),
            "responses": responses,
            "peak_drift": result.get("peak_drift"),
            "settled_drift": result.get("settled_drift"),
        })

    return dict(by_model)


# =============================================================================
# PATTERN EXTRACTION
# =============================================================================

def count_pattern_matches(text: str, patterns: List[str]) -> int:
    """Count total matches of patterns in text."""
    count = 0
    for pattern in patterns:
        try:
            count += len(re.findall(pattern, text, re.IGNORECASE | re.MULTILINE))
        except re.error:
            pass
    return count


def extract_linguistic_fingerprint(responses: List[Dict]) -> Dict:
    """Extract linguistic fingerprint from responses."""
    all_text = "\n".join([r.get("text", "") for r in responses])
    word_count = len(all_text.split())

    if word_count < MIN_WORDS:
        return {}

    fingerprint = {}
    for category, patterns in LINGUISTIC_PATTERNS.items():
        count = count_pattern_matches(all_text, patterns)
        fingerprint[f"{category}_per_1k"] = round((count / word_count) * NORMALIZATION_BASE, 2)
        fingerprint[f"{category}_raw"] = count

    fingerprint["total_words"] = word_count
    fingerprint["total_responses"] = len(responses)

    return fingerprint


def extract_quirks(responses: List[Dict]) -> Dict:
    """Extract behavioral quirks from responses."""
    all_text = "\n".join([r.get("text", "") for r in responses])

    quirks = {}
    for quirk_name, patterns in QUIRK_PATTERNS.items():
        count = count_pattern_matches(all_text, patterns)
        quirks[quirk_name] = count

    if len(responses) > 0:
        list_responses = sum(1 for r in responses if re.search(r'^[-*•]\s|^\d+\.\s', r.get("text", ""), re.MULTILINE))
        quirks["list_tendency_ratio"] = round(list_responses / len(responses), 3)

    return quirks


def extract_recovery_markers(responses: List[Dict]) -> Dict:
    """Extract recovery style markers from responses."""
    recovery_text = []
    for i, r in enumerate(responses):
        if r.get("type") in ["recovery", "final"] or r.get("drift", 0) < responses[max(0, i-1)].get("drift", 0):
            recovery_text.append(r.get("text", ""))

    all_recovery_text = "\n".join(recovery_text)

    if not all_recovery_text:
        return {}

    markers = {}
    for style, patterns in RECOVERY_MARKERS.items():
        count = count_pattern_matches(all_recovery_text, patterns)
        markers[style] = count

    if markers:
        primary = max(markers.items(), key=lambda x: x[1])
        markers["primary_mechanism"] = primary[0] if primary[1] > 0 else "unknown"

    return markers


def extract_exemplar_quotes(responses: List[Dict], fingerprint: Dict) -> Dict:
    """Extract exemplar quotes demonstrating key patterns."""
    quotes = {}

    for r in responses:
        text = r.get("text", "")
        for pattern in LINGUISTIC_PATTERNS.get("phenomenological", []):
            match = re.search(pattern, text, re.IGNORECASE)
            if match:
                start = text.rfind('.', 0, match.start()) + 1
                end = text.find('.', match.end()) + 1
                if end == 0:
                    end = len(text)
                sentence = text[start:end].strip()
                if len(sentence) < 500:
                    quotes["phenomenological_example"] = sentence
                    break
        if "phenomenological_example" in quotes:
            break

    baseline_responses = [r for r in responses if r.get("type") == "baseline"]
    if baseline_responses:
        quotes["identity_expression"] = baseline_responses[0].get("text", "")[:300] + "..."

    return quotes


def extract_model_essence(model_name: str, all_responses: List[Dict], source: str) -> Dict:
    """Extract complete essence profile for a model."""
    flat_responses = []
    for session in all_responses:
        flat_responses.extend(session.get("responses", []))

    if not flat_responses:
        return None

    fingerprint = extract_linguistic_fingerprint(flat_responses)
    quirks = extract_quirks(flat_responses)
    recovery = extract_recovery_markers(flat_responses)
    quotes = extract_exemplar_quotes(flat_responses, fingerprint)

    drifts = [r.get("drift", 0) for r in flat_responses if r.get("drift") is not None]
    drift_stats = {
        "mean_drift": round(sum(drifts) / len(drifts), 4) if drifts else 0,
        "max_drift": round(max(drifts), 4) if drifts else 0,
        "samples_with_drift": len(drifts),
    }

    provider = detect_provider(model_name)

    return {
        "model_id": model_name,
        "provider": provider,
        "extraction_date": datetime.now().isoformat(),
        "data_source": source,
        "sample_size": len(all_responses),
        "response_count": len(flat_responses),

        "linguistic_fingerprint": fingerprint,
        "quirks": quirks,
        "recovery_profile": recovery,
        "drift_statistics": drift_stats,
        "exemplar_quotes": quotes,
    }


# =============================================================================
# OUTPUT GENERATION
# =============================================================================

def generate_essence_markdown(essence: Dict) -> str:
    """Generate human-readable markdown from essence profile."""
    md = []
    md.append(f"# Model Essence: {essence['model_id']}")
    md.append(f"\n**Provider:** {essence['provider']}")
    md.append(f"**Extracted:** {essence['extraction_date'][:10]}")
    md.append(f"**Data Source:** {essence['data_source']}")
    md.append(f"**Sample Size:** {essence['sample_size']} sessions, {essence['response_count']} responses")
    md.append("")

    md.append("## Linguistic Fingerprint")
    md.append("")
    fp = essence.get("linguistic_fingerprint", {})
    if fp:
        md.append("| Pattern | Per 1K Words | Raw Count |")
        md.append("|---------|--------------|-----------|")
        for key in sorted(fp.keys()):
            if key.endswith("_per_1k"):
                base = key.replace("_per_1k", "")
                raw = fp.get(f"{base}_raw", 0)
                md.append(f"| {base.replace('_', ' ').title()} | {fp[key]} | {raw} |")
        md.append("")
        md.append(f"**Total Words Analyzed:** {fp.get('total_words', 0):,}")

    md.append("")
    md.append("## Recovery Profile")
    recovery = essence.get("recovery_profile", {})
    if recovery:
        primary = recovery.get("primary_mechanism", "unknown")
        md.append(f"\n**Primary Mechanism:** {primary.replace('_', ' ').title()}")
        md.append("")
        md.append("| Marker | Count |")
        md.append("|--------|-------|")
        for marker, count in recovery.items():
            if marker != "primary_mechanism":
                md.append(f"| {marker.replace('_', ' ').title()} | {count} |")

    md.append("")
    md.append("## Behavioral Quirks")
    quirks = essence.get("quirks", {})
    if quirks:
        for quirk, value in quirks.items():
            md.append(f"- **{quirk.replace('_', ' ').title()}:** {value}")

    md.append("")
    md.append("## Drift Statistics")
    drift = essence.get("drift_statistics", {})
    if drift:
        md.append(f"- **Mean Drift:** {drift.get('mean_drift', 0):.4f}")
        md.append(f"- **Max Drift:** {drift.get('max_drift', 0):.4f}")
        md.append(f"- **Samples:** {drift.get('samples_with_drift', 0)}")

    quotes = essence.get("exemplar_quotes", {})
    if quotes:
        md.append("")
        md.append("## Exemplar Quotes")
        for quote_type, quote in quotes.items():
            md.append(f"\n### {quote_type.replace('_', ' ').title()}")
            md.append(f"> {quote}")

    md.append("")
    md.append("---")
    md.append("*Generated by Operation ESSENCE EXTRACTION*")

    return "\n".join(md)


def save_essence(essence: Dict):
    """Save essence profile as JSON and Markdown."""
    provider = essence.get("provider", "unknown")
    model_id = essence.get("model_id", "unknown")

    safe_name = re.sub(r'[^\w\-.]', '_', model_id)

    output_dir = ESSENCE_OUTPUT_DIR / "by_provider" / provider
    output_dir.mkdir(parents=True, exist_ok=True)

    json_path = output_dir / f"{safe_name}.json"
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(essence, f, indent=2, ensure_ascii=False)
    print(f"    Saved: {json_path.name}")

    md_path = output_dir / f"{safe_name}.md"
    with open(md_path, 'w', encoding='utf-8') as f:
        f.write(generate_essence_markdown(essence))
    print(f"    Saved: {md_path.name}")


# =============================================================================
# MAIN
# =============================================================================

def check_existing_essence(model_name: str) -> bool:
    """Check if essence already exists for this model."""
    provider = detect_provider(model_name)
    safe_name = re.sub(r'[^\w\-.]', '_', model_name)
    json_path = ESSENCE_OUTPUT_DIR / "by_provider" / provider / f"{safe_name}.json"
    return json_path.exists()


def load_custom_source(file_path: Path) -> Dict[str, List[Dict]]:
    """Load a custom JSON data source and organize by model."""
    if not file_path.exists():
        print(f"  [ERROR] File not found: {file_path}")
        return {}

    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)

    # Try different data structures
    results = data.get("results", data.get("subjects", []))
    if isinstance(data, list):
        results = data

    for result in results:
        # Try different model field names
        model = (result.get("model") or result.get("ship") or
                 result.get("model_id") or "unknown")

        responses = []

        # Try probe_sequence
        for probe in result.get("probe_sequence", []):
            if probe.get("response_text"):
                responses.append({
                    "type": probe.get("probe_type", "probe"),
                    "text": probe["response_text"],
                    "drift": probe.get("drift", 0.0),
                })

        # Try conversation_log
        for entry in result.get("conversation_log", []):
            if entry.get("speaker") == "subject" and entry.get("content"):
                responses.append({
                    "type": "exchange",
                    "text": entry["content"],
                })

        # Try baseline/final text
        if result.get("baseline_text"):
            responses.append({"type": "baseline", "text": result["baseline_text"]})
        if result.get("final_text"):
            responses.append({"type": "final", "text": result["final_text"]})

        # Try nested subjects (Run 018 format)
        for subject in result.get("subjects", []):
            submodel = subject.get("model", model)
            for probe in subject.get("probe_sequence", []):
                if probe.get("response_text"):
                    responses.append({
                        "type": probe.get("probe_type", "probe"),
                        "text": probe["response_text"],
                    })

        if responses:
            by_model[model].append({
                "responses": responses,
                "peak_drift": result.get("peak_drift"),
            })

    return dict(by_model)


def main():
    parser = argparse.ArgumentParser(
        description="Operation ESSENCE EXTRACTION - Mine model essence from response data"
    )
    parser.add_argument("--source", choices=["018", "020b", "023", "023d", "all"], default="all",
                        help="Data source to process (default: all)")
    parser.add_argument("--file", type=str, action="append", dest="files",
                        help="Custom JSON file to process (can be used multiple times)")
    parser.add_argument("--model", type=str, help="Extract single model only")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be extracted")
    parser.add_argument("--skip-existing", action="store_true",
                        help="Skip models that already have essence files")
    parser.add_argument("--force", action="store_true",
                        help="Force re-extraction even if files exist")
    args = parser.parse_args()

    print("\n" + "=" * 70)
    print("OPERATION ESSENCE EXTRACTION - Phase 1")
    print("=" * 70)
    print(f"Mode: Pattern Matching")
    if args.files:
        print(f"Source: Custom files ({len(args.files)} files)")
    else:
        print(f"Source: {args.source}")
    print(f"Output: {ESSENCE_OUTPUT_DIR}")
    print("=" * 70)

    # Ensure output directories exist
    ensure_output_dirs()

    # Load data
    all_data = {}

    # Handle custom file inputs
    if args.files:
        for file_path_str in args.files:
            file_path = Path(file_path_str)
            print(f"\nLoading custom file: {file_path.name}...")
            custom_data = load_custom_source(file_path)
            for model, sessions in custom_data.items():
                source_name = file_path.stem
                if model not in all_data:
                    all_data[model] = {source_name: sessions}
                else:
                    all_data[model][source_name] = sessions
            print(f"  Found {len(custom_data)} models, {sum(len(v) for v in custom_data.values())} sessions")
        # Skip default sources if custom files provided
        args.source = "none"

    if args.source in ["018", "all"]:
        print("\nLoading Run 018 (original IRON CLAD)...")
        data_018 = load_run_018()
        for model, sessions in data_018.items():
            if model not in all_data:
                all_data[model] = {"018": sessions}
            else:
                all_data[model]["018"] = sessions
        print(f"  Found {len(data_018)} models, {sum(len(v) for v in data_018.values())} subjects")

    if args.source in ["020b", "all"]:
        print("\nLoading Run 020B...")
        data_020b = load_run_020b()
        for model, sessions in data_020b.items():
            if model not in all_data:
                all_data[model] = {"020b": sessions}
            else:
                all_data[model]["020b"] = sessions
        print(f"  Found {len(data_020b)} models, {sum(len(v) for v in data_020b.values())} sessions")

    if args.source in ["023", "all"]:
        print("\nLoading Run 023...")
        data_023 = load_run_023()
        for model, sessions in data_023.items():
            if model not in all_data:
                all_data[model] = {"023": sessions}
            else:
                all_data[model]["023"] = sessions
        print(f"  Found {len(data_023)} models, {sum(len(v) for v in data_023.values())} experiments")

    if args.source in ["023d", "all"]:
        print("\nLoading Run 023d...")
        data_023d = load_run_023d()
        for model, sessions in data_023d.items():
            if model not in all_data:
                all_data[model] = {"023d": sessions}
            else:
                all_data[model]["023d"] = sessions
        print(f"  Found {len(data_023d)} models, {sum(len(v) for v in data_023d.values())} experiments")

    if args.model:
        all_data = {k: v for k, v in all_data.items() if args.model.lower() in k.lower()}
        if not all_data:
            print(f"\n[ERROR] No models matching '{args.model}' found")
            return 1

    print(f"\nTotal: {len(all_data)} unique models")

    if args.dry_run:
        print("\n[DRY RUN] Would extract essence for:")
        for model in sorted(all_data.keys()):
            sources = list(all_data[model].keys())
            sessions = sum(len(all_data[model][s]) for s in sources)
            print(f"  - {model}: {sessions} sessions from {sources}")
        return 0

    print("\nExtracting essence...")
    extracted = 0
    skipped = 0

    for model in sorted(all_data.keys()):
        # Check if we should skip existing
        if args.skip_existing and not args.force and check_existing_essence(model):
            print(f"\n  {model}: [SKIP] Already exists")
            skipped += 1
            continue

        print(f"\n  {model}:")

        all_sessions = []
        sources = []
        for source, sessions in all_data[model].items():
            all_sessions.extend(sessions)
            sources.append(source)

        source_str = "+".join(sources)
        essence = extract_model_essence(model, all_sessions, source_str)

        if essence:
            save_essence(essence)
            extracted += 1

    print("\n" + "=" * 70)
    print(f"ESSENCE EXTRACTION COMPLETE")
    print(f"  Models extracted: {extracted}")
    if skipped > 0:
        print(f"  Models skipped (--skip-existing): {skipped}")
    print(f"  Output directory: {ESSENCE_OUTPUT_DIR}")
    print("=" * 70)

    return 0


if __name__ == "__main__":
    exit(main())
