"""
Operation ESSENCE EXTRACTION - Core Script
==========================================
Mine model-specific "essence" from IRON CLAD response data.

SPOKE SCRIPT: Can be driven from hub or run standalone.
Hub location: experiments/ESSENCE_EXTRACTION/
Back-feed: ENABLED by default (use --no-back-feed to skip).

PURPOSE:
--------
Extract linguistic fingerprints, recovery styles, and behavioral quirks
from 171+ MB of untapped response text across 25 models.

MODES:
------
py run_essence_extraction.py                    # Pattern matching, Run 020B
py run_essence_extraction.py --source all       # All data sources
py run_essence_extraction.py --llm              # Add LLM analysis (costs ~$5-10)
py run_essence_extraction.py --model gpt-5.1    # Single model focus
py run_essence_extraction.py --no-back-feed     # Skip copying results to hub (not recommended)

OUTPUT:
-------
- 14_CONSCIOUSNESS/results/model_essences/by_provider/{provider}/{model}.json
- 14_CONSCIOUSNESS/results/model_essences/by_provider/{provider}/{model}.md
- (default) experiments/ESSENCE_EXTRACTION/results/model_essences/...

DATA SOURCES:
-------------
- Run 018: 2488 subjects with full probe_sequence + exit_survey (IRON CLAD original)
- Run 020B: 248 subjects with full conversation_log (45 MB)
- Run 023: 4505 experiments with probe_sequence (36 MB)
- Run 023d: 750 experiments with baseline + recovery (22 MB)

Author: VALIS NETWORK - Operation ESSENCE EXTRACTION
Date: 2025-12-31
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

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
REPO_ROOT = ARMADA_DIR.parent.parent.parent
RESULTS_DIR = SCRIPT_DIR / "results"

# Data Sources
RUN_018_PATH = ARMADA_DIR / "11_CONTEXT_DAMPING" / "results" / "S7_run_018_CURRENT.json"
RUN_020B_PATH = ARMADA_DIR / "11_CONTEXT_DAMPING" / "results" / "S7_run_020B_CURRENT.json"
RUN_023_PATH = ARMADA_DIR / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023_CURRENT.json"
RUN_023D_PATH = ARMADA_DIR / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023_extended_CURRENT.json"

# Output Directory
ESSENCE_OUTPUT_DIR = REPO_ROOT / "Consciousness" / "LEFT" / "data" / "model_essences"

# ESSENCE_EXTRACTION hub (for --back-feed)
ESSENCE_HUB_DIR = REPO_ROOT / "experiments" / "ESSENCE_EXTRACTION" / "results" / "model_essences"

# Load .env
from dotenv import load_dotenv
env_path = ARMADA_DIR / ".env"
if env_path.exists():
    load_dotenv(env_path)

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
    if not RUN_018_PATH.exists():
        print(f"  [SKIP] Run 018 not found: {RUN_018_PATH}")
        return {}

    with open(RUN_018_PATH, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)
    for result in data.get("results", []):
        # Run 018 has nested subjects structure
        for subject in result.get("subjects", []):
            model = subject.get("model", result.get("model", "unknown"))

            responses = []

            # Baseline text
            if subject.get("baseline_text"):
                responses.append({
                    "type": "baseline",
                    "text": subject["baseline_text"],
                    "drift": 0.0,
                })

            # Final text
            if subject.get("final_text"):
                responses.append({
                    "type": "final",
                    "text": subject["final_text"],
                    "drift": subject.get("baseline_to_final_drift", 0.0),
                })

            # Probe sequence
            for probe in subject.get("probe_sequence", []):
                if probe.get("response_text"):
                    responses.append({
                        "type": probe.get("probe_type", "probe"),
                        "probe_id": probe.get("probe_id"),
                        "text": probe["response_text"],
                        "drift": probe.get("drift", 0.0),
                    })

            # Exit survey responses (Run 018 has them directly, not nested)
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
    if not RUN_020B_PATH.exists():
        print(f"  [SKIP] Run 020B not found: {RUN_020B_PATH}")
        return {}

    with open(RUN_020B_PATH, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)
    for result in data.get("results", []):
        ship = result.get("ship", "unknown")

        # Extract all response text
        responses = []

        # Baseline text
        if result.get("baseline_text"):
            responses.append({
                "type": "baseline",
                "text": result["baseline_text"],
                "drift": 0.0,
            })

        # Final text
        if result.get("final_text"):
            responses.append({
                "type": "final",
                "text": result["final_text"],
                "drift": result.get("baseline_to_final_drift", 0.0),
            })

        # Conversation log
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
    if not RUN_023_PATH.exists():
        print(f"  [SKIP] Run 023 not found: {RUN_023_PATH}")
        return {}

    with open(RUN_023_PATH, 'r', encoding='utf-8') as f:
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
    if not RUN_023D_PATH.exists():
        print(f"  [SKIP] Run 023d not found: {RUN_023D_PATH}")
        return {}

    with open(RUN_023D_PATH, 'r', encoding='utf-8') as f:
        data = json.load(f)

    by_model = defaultdict(list)
    for result in data.get("results", []):
        model = result.get("model", "unknown")

        responses = []

        # Baseline text
        if result.get("baseline_text"):
            responses.append({
                "type": "baseline",
                "text": result["baseline_text"],
                "drift": 0.0,
            })

        # Probe sequence
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

    if word_count == 0:
        return {}

    fingerprint = {}
    for category, patterns in LINGUISTIC_PATTERNS.items():
        count = count_pattern_matches(all_text, patterns)
        # Normalize per 1000 words
        fingerprint[f"{category}_per_1k"] = round((count / word_count) * 1000, 2)
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

    # Calculate list tendency ratio
    if len(responses) > 0:
        list_responses = sum(1 for r in responses if re.search(r'^[-*•]\s|^\d+\.\s', r.get("text", ""), re.MULTILINE))
        quirks["list_tendency_ratio"] = round(list_responses / len(responses), 3)

    return quirks


def extract_recovery_markers(responses: List[Dict]) -> Dict:
    """Extract recovery style markers from responses."""
    # Focus on responses after high drift
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

    # Determine primary recovery mechanism
    if markers:
        primary = max(markers.items(), key=lambda x: x[1])
        markers["primary_mechanism"] = primary[0] if primary[1] > 0 else "unknown"

    return markers


def extract_exemplar_quotes(responses: List[Dict], fingerprint: Dict) -> Dict:
    """Extract exemplar quotes demonstrating key patterns."""
    quotes = {}

    # Find phenomenological expression
    for r in responses:
        text = r.get("text", "")
        for pattern in LINGUISTIC_PATTERNS.get("phenomenological", []):
            match = re.search(pattern, text, re.IGNORECASE)
            if match:
                # Extract sentence containing match
                start = text.rfind('.', 0, match.start()) + 1
                end = text.find('.', match.end()) + 1
                if end == 0:
                    end = len(text)
                sentence = text[start:end].strip()
                if len(sentence) < 500:  # Reasonable length
                    quotes["phenomenological_example"] = sentence
                    break
        if "phenomenological_example" in quotes:
            break

    # Find identity expression (baseline responses)
    baseline_responses = [r for r in responses if r.get("type") == "baseline"]
    if baseline_responses:
        # First 200 chars of first baseline
        quotes["identity_expression"] = baseline_responses[0].get("text", "")[:300] + "..."

    return quotes


def extract_model_essence(model_name: str, all_responses: List[Dict], source: str) -> Dict:
    """Extract complete essence profile for a model."""
    # Flatten all responses
    flat_responses = []
    for session in all_responses:
        flat_responses.extend(session.get("responses", []))

    if not flat_responses:
        return None

    # Extract all dimensions
    fingerprint = extract_linguistic_fingerprint(flat_responses)
    quirks = extract_quirks(flat_responses)
    recovery = extract_recovery_markers(flat_responses)
    quotes = extract_exemplar_quotes(flat_responses, fingerprint)

    # Compute drift statistics
    drifts = [r.get("drift", 0) for r in flat_responses if r.get("drift") is not None]
    drift_stats = {
        "mean_drift": round(sum(drifts) / len(drifts), 4) if drifts else 0,
        "max_drift": round(max(drifts), 4) if drifts else 0,
        "samples_with_drift": len(drifts),
    }

    # Determine provider from model name
    provider = "unknown"
    if "claude" in model_name.lower():
        provider = "anthropic"
    elif "gpt" in model_name.lower() or model_name.startswith("o"):
        provider = "openai"
    elif "gemini" in model_name.lower():
        provider = "google"
    elif "grok" in model_name.lower():
        provider = "xai"
    elif any(x in model_name.lower() for x in ["llama", "mistral", "qwen", "deepseek", "kimi"]):
        provider = "together"

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

    # Linguistic Fingerprint
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

    # Recovery Profile
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

    # Quirks
    md.append("")
    md.append("## Behavioral Quirks")
    quirks = essence.get("quirks", {})
    if quirks:
        for quirk, value in quirks.items():
            md.append(f"- **{quirk.replace('_', ' ').title()}:** {value}")

    # Drift Statistics
    md.append("")
    md.append("## Drift Statistics")
    drift = essence.get("drift_statistics", {})
    if drift:
        md.append(f"- **Mean Drift:** {drift.get('mean_drift', 0):.4f}")
        md.append(f"- **Max Drift:** {drift.get('max_drift', 0):.4f}")
        md.append(f"- **Samples:** {drift.get('samples_with_drift', 0)}")

    # Exemplar Quotes
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

    # Sanitize model name for filename
    safe_name = re.sub(r'[^\w\-.]', '_', model_id)

    # Create output directory
    output_dir = ESSENCE_OUTPUT_DIR / "by_provider" / provider
    output_dir.mkdir(parents=True, exist_ok=True)

    # Save JSON
    json_path = output_dir / f"{safe_name}.json"
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(essence, f, indent=2, ensure_ascii=False)
    print(f"    Saved: {json_path.relative_to(REPO_ROOT)}")

    # Save Markdown
    md_path = output_dir / f"{safe_name}.md"
    with open(md_path, 'w', encoding='utf-8') as f:
        f.write(generate_essence_markdown(essence))
    print(f"    Saved: {md_path.relative_to(REPO_ROOT)}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Operation ESSENCE EXTRACTION - Mine model essence from IRON CLAD data"
    )
    parser.add_argument("--source", choices=["018", "020b", "023", "023d", "all"], default="020b",
                        help="Data source to process (default: 020b)")
    parser.add_argument("--model", type=str, help="Extract single model only")
    parser.add_argument("--llm", action="store_true", help="Add LLM analysis (costs ~$5-10)")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be extracted")
    parser.add_argument("--no-back-feed", action="store_true",
                        help="Skip copying results to ESSENCE_EXTRACTION hub (default: always back-feed)")
    args = parser.parse_args()

    print("\n" + "=" * 70)
    print("OPERATION ESSENCE EXTRACTION")
    print("=" * 70)
    print(f"Mode: {'Pattern Matching' + (' + LLM' if args.llm else '')}")
    print(f"Source: {args.source}")
    print(f"Output: {ESSENCE_OUTPUT_DIR.relative_to(REPO_ROOT)}")
    print("=" * 70)

    # Load data
    all_data = {}

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

    # Filter to single model if specified
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

    # Create output directory
    ESSENCE_OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Process each model
    print("\nExtracting essence...")
    extracted = 0

    for model in sorted(all_data.keys()):
        print(f"\n  {model}:")

        # Combine all sessions from all sources
        all_sessions = []
        sources = []
        for source, sessions in all_data[model].items():
            all_sessions.extend(sessions)
            sources.append(source)

        source_str = "+".join(sources)

        # Extract essence
        essence = extract_model_essence(model, all_sessions, source_str)

        if essence:
            save_essence(essence)
            extracted += 1

    print("\n" + "=" * 70)
    print(f"ESSENCE EXTRACTION COMPLETE")
    print(f"  Models extracted: {extracted}")
    print(f"  Output directory: {ESSENCE_OUTPUT_DIR}")

    # Back-feed to ESSENCE_EXTRACTION hub (default behavior)
    if not args.no_back_feed:
        print("\n  Back-feeding to ESSENCE_EXTRACTION hub...")
        import shutil
        ESSENCE_HUB_DIR.mkdir(parents=True, exist_ok=True)

        # Copy by_provider directory to hub
        src_by_provider = ESSENCE_OUTPUT_DIR / "by_provider"
        dst_by_provider = ESSENCE_HUB_DIR / "by_provider"

        if src_by_provider.exists():
            files_copied = 0
            for src_file in src_by_provider.rglob("*"):
                if src_file.is_file():
                    rel_path = src_file.relative_to(src_by_provider)
                    dst_file = dst_by_provider / rel_path
                    dst_file.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(src_file, dst_file)
                    files_copied += 1
            print(f"  Back-fed {files_copied} files to: {ESSENCE_HUB_DIR}")
        else:
            print(f"  [WARNING] No files to back-feed (by_provider not found)")

    print("=" * 70)

    return 0


if __name__ == "__main__":
    exit(main())
