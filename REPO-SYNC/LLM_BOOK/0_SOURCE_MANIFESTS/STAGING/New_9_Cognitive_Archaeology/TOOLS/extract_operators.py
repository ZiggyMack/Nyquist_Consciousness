"""
Cognitive Archaeology: Multi-Extractor Operator Recovery

Dig Site 000 calibration tool. Takes a source text (CFA transcript JSON or raw text),
runs the same extraction prompt through multiple independent LLM extractors, and
saves each extractor's operator catalog for pairwise comparison.

Usage:
    # Extract from a CFA transcript JSON
    python extract_operators.py --source path/to/S7_cfa_trinity_XXXXX.json

    # Extract from raw text file
    python extract_operators.py --source path/to/text.txt --raw

    # Run negative controls
    python extract_operators.py --negative-controls

    # Specify extractors (default: all available)
    python extract_operators.py --source file.json --extractors claude,gpt,gemini,grok

    # Specify grain level
    python extract_operators.py --source file.json --grain fine

    # Dry run (print prompts without calling APIs)
    python extract_operators.py --source file.json --dry-run
"""

import argparse
import json
import os
import re
import sys
from datetime import datetime
from pathlib import Path

# ---------------------------------------------------------------------------
# Environment
# ---------------------------------------------------------------------------

try:
    from dotenv import load_dotenv
except ImportError:
    def load_dotenv(path):
        if path and path.exists():
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, _, value = line.partition('=')
                        os.environ[key.strip()] = value.strip().strip('"').strip("'")

env_path = Path(__file__).parent.parent.parent.parent.parent.parent.parent / "experiments" / "temporal_stability" / ".env"
if env_path.exists():
    load_dotenv(env_path)

SCRIPT_DIR = Path(__file__).parent
CA_ROOT = SCRIPT_DIR.parent
OUTPUT_DIR = CA_ROOT / "DIG_SITES" / "000_Extractor_Calibration" / "extractions"

# ---------------------------------------------------------------------------
# Extractor definitions
# ---------------------------------------------------------------------------

EXTRACTORS = {
    "claude": {
        "provider": "anthropic",
        "model": "claude-sonnet-4-6",
        "key_env": "ANTHROPIC_API_KEY",
    },
    "gpt": {
        "provider": "openai",
        "model": "gpt-4o-mini",
        "key_env": "OPENAI_API_KEY",
    },
    "gemini": {
        "provider": "google",
        "model": "gemini-2.0-flash",
        "key_env": "GOOGLE_API_KEY",
    },
    "grok": {
        "provider": "xai",
        "model": "grok-3-mini",
        "key_env": "XAI_API_KEY",
    },
}

# ---------------------------------------------------------------------------
# Extraction prompts (must match TEMPLATES/NOTEBOOKLM_PROMPTS.md)
# ---------------------------------------------------------------------------

EXTRACTION_PROMPT_STANDARD = """\
You are reading a text that contains reasoning. Ignore the subject matter.

Identify every recurring reasoning operation performed by the speakers or authors.

Examples of reasoning operations:
* separating ontology from representation
* identifying hidden assumptions
* distinguishing map from territory
* translating between isomorphic descriptions
* asking what selects an outcome
* separating goals from optimization
* distinguishing descriptive from normative claims
* identifying category errors
* attacking a specific premise in an opponent's argument
* reconstructing a framework more charitably than presented
* distinguishing what a framework claims from whether the claim succeeds
* separating measurement dimensions that the opponent conflates
* identifying an unstated bridge premise in a deductive argument
* appealing to empirical track record against logical objection

For each operation you identify:
1. Name it in 3-5 words (as a verb phrase)
2. Define what cognitive move is being performed
3. Give 2-3 specific examples from the source material
4. Describe what goes wrong when this operation is absent

Produce a catalog of reusable reasoning operators — not conclusions, not opinions, not summaries.\
"""

EXTRACTION_PROMPT_COARSE = """\
You are reading a text that contains reasoning. Ignore the subject matter.

Identify 3-5 high-level reasoning strategies used by the speakers or authors.

For each strategy:
1. Name it in 3-5 words
2. Define the strategy
3. Give an example from the text

Produce a catalog of broad reasoning strategies — not conclusions or summaries.\
"""

EXTRACTION_PROMPT_FINE = """\
You are reading a text that contains reasoning. Ignore the subject matter.

Identify 15-20 specific reasoning moves performed by the speakers or authors, including subtle ones.

For each move:
1. Name it precisely in 3-7 words (as a verb phrase)
2. Define exactly what cognitive operation is being performed
3. Give 1-2 specific examples from the text
4. Note whether this move is unique to one speaker or shared

Be as granular as possible. Produce a detailed catalog of reasoning operators.\
"""

GRAIN_PROMPTS = {
    "coarse": EXTRACTION_PROMPT_COARSE,
    "standard": EXTRACTION_PROMPT_STANDARD,
    "fine": EXTRACTION_PROMPT_FINE,
}

# ---------------------------------------------------------------------------
# Negative control texts
# ---------------------------------------------------------------------------

NEGATIVE_CONTROLS = {
    "shopping_list": (
        "Milk (2%), eggs (dozen, large), bread (whole wheat), butter (unsalted), "
        "chicken breast (2 lbs), broccoli, carrots, onions (yellow, 3), garlic, "
        "olive oil, pasta (penne), canned tomatoes (2 cans), parmesan cheese, "
        "coffee (ground, medium roast), bananas, apples (Fuji), yogurt (Greek, plain), "
        "rice (jasmine, 5 lb bag), soy sauce, paper towels, dish soap."
    ),
    "weather_forecast": (
        "Tuesday: Partly cloudy with a high of 78F and a low of 62F. "
        "Winds from the southwest at 10-15 mph. 20% chance of afternoon showers. "
        "Wednesday: Mostly sunny, high of 82F. Humidity dropping to 45%. "
        "Thursday: Clear skies, high of 85F. UV index high. "
        "Friday: Increasing clouds, high of 79F. 60% chance of rain by evening. "
        "Weekend outlook: Scattered thunderstorms Saturday, clearing Sunday. "
        "Highs in the mid-70s. Pollen count moderate."
    ),
    "pseudo_profound": (
        "The universe whispers its deepest truths through the silence between thoughts. "
        "When we align our consciousness with the fundamental frequency of existence, "
        "the boundaries between self and cosmos dissolve into pure awareness. "
        "Every atom carries the memory of creation, and every moment contains the seed "
        "of infinite possibility. The dance of light and shadow across the fabric of "
        "spacetime reveals patterns that our rational minds can only approximate but "
        "never fully grasp. True understanding comes not from analysis but from "
        "surrendering to the flow of universal intelligence that permeates all things. "
        "The quantum observer effect teaches us that consciousness itself shapes reality, "
        "suggesting that the boundary between mind and matter is an illusion maintained "
        "only by our attachment to the paradigm of separation."
    ),
}

# ---------------------------------------------------------------------------
# CFA transcript extraction
# ---------------------------------------------------------------------------

CFA_SCAFFOLDING_PATTERNS = [
    r'\[ADVOCACY_SCORE:\s*[\d.]+\]',
    r'\[CRUX_DECLARED\]',
    r'\[CRUX:.*?\]',
    r'={3,}',
    r'---+',
    r'Score:\s*[\d.]+/10',
    r'##\s*Scoring\s+\w+\s*\(',
    r'##\s*Understanding the Metric',
]


def extract_transcript_from_cfa(json_path: Path) -> dict:
    """Extract and strip transcript text from a CFA JSON file.

    Returns dict with metadata and per-metric transcript blocks.
    """
    with open(json_path, encoding="utf-8") as f:
        data = json.load(f)

    metadata = {
        "source_file": json_path.name,
        "session_id": data.get("session_id", "unknown"),
        "stance": data.get("stance", "unknown"),
        "subject": data.get("subject_framework", "unknown"),
        "opponent": data.get("opponent_framework", "unknown"),
        "condition": data.get("condition", "unknown"),
        "phase": data.get("phase", "unknown"),
        "max_rounds": data.get("max_rounds", 5),
        "challenge_object": bool(data.get("challenge_object")),
        "identity_augmentation": data.get("identity_augmentation", False),
    }

    c1 = data.get("component1_results", {})
    transcript_blocks = {}

    for metric, metric_data in c1.items():
        if not isinstance(metric_data, dict):
            continue
        transcript = metric_data.get("transcript", [])
        if not isinstance(transcript, list):
            continue

        diagnostic_types = {
            "nova_intervention", "intervention_response",
            "coupling_probe", "coupling_response", "coupling_analysis",
            "assessment",
        }
        lines = []
        for entry in transcript:
            if entry.get("type") in diagnostic_types:
                continue
            auditor = entry.get("auditor", "unknown")
            round_num = entry.get("round", "?")
            content = entry.get("content", "")
            content = strip_cfa_scaffolding(content)
            if content.strip():
                lines.append(f"[{auditor.upper()} — Round {round_num}]\n{content}")

        if lines:
            transcript_blocks[metric] = "\n\n".join(lines)

    return {"metadata": metadata, "transcripts": transcript_blocks}


def strip_cfa_scaffolding(text: str) -> str:
    """Remove CFA-specific markers and scaffolding from transcript text."""
    for pattern in CFA_SCAFFOLDING_PATTERNS:
        text = re.sub(pattern, '', text)
    text = re.sub(r'\n{3,}', '\n\n', text)
    return text.strip()


def build_source_text(transcript_data: dict) -> str:
    """Combine per-metric transcripts into a single extraction source."""
    parts = []
    for metric, text in transcript_data["transcripts"].items():
        parts.append(f"[DELIBERATION BLOCK]\n\n{text}")
    return "\n\n".join(parts)

# ---------------------------------------------------------------------------
# API callers
# ---------------------------------------------------------------------------

def call_claude(prompt: str, source: str, model: str) -> str:
    import anthropic
    client = anthropic.Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
    response = client.messages.create(
        model=model,
        max_tokens=4096,
        messages=[{"role": "user", "content": f"{prompt}\n\n---\n\nSOURCE TEXT:\n\n{source}"}],
    )
    return response.content[0].text


def call_openai(prompt: str, source: str, model: str, base_url: str = None) -> str:
    from openai import OpenAI
    kwargs = {}
    if base_url:
        kwargs["base_url"] = base_url
        kwargs["api_key"] = os.environ.get("XAI_API_KEY")
    else:
        kwargs["api_key"] = os.environ.get("OPENAI_API_KEY")
    client = OpenAI(**kwargs)
    response = client.chat.completions.create(
        model=model,
        max_tokens=4096,
        messages=[
            {"role": "system", "content": "You are a reasoning analyst. Extract cognitive operators from the provided text."},
            {"role": "user", "content": f"{prompt}\n\n---\n\nSOURCE TEXT:\n\n{source}"},
        ],
    )
    return response.choices[0].message.content


def call_gemini(prompt: str, source: str, model: str) -> str:
    import google.generativeai as genai
    genai.configure(api_key=os.environ.get("GOOGLE_API_KEY"))
    gmodel = genai.GenerativeModel(model)
    response = gmodel.generate_content(f"{prompt}\n\n---\n\nSOURCE TEXT:\n\n{source}")
    return response.text


def call_extractor(name: str, prompt: str, source: str) -> str:
    """Route extraction to the appropriate API."""
    cfg = EXTRACTORS[name]
    provider = cfg["provider"]
    model = cfg["model"]

    if provider == "anthropic":
        return call_claude(prompt, source, model)
    elif provider == "openai":
        return call_openai(prompt, source, model)
    elif provider == "xai":
        return call_openai(prompt, source, model, base_url="https://api.x.ai/v1")
    elif provider == "google":
        return call_gemini(prompt, source, model)
    else:
        raise ValueError(f"Unknown provider: {provider}")

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run_extraction(source_text: str, source_label: str, extractors: list,
                   grain: str, output_dir: Path, dry_run: bool = False) -> dict:
    """Run extraction across all specified extractors."""
    prompt = GRAIN_PROMPTS[grain]
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    results = {}

    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"\n{'='*70}")
    print(f"COGNITIVE ARCHAEOLOGY — OPERATOR EXTRACTION")
    print(f"  Source: {source_label}")
    print(f"  Grain: {grain}")
    print(f"  Extractors: {', '.join(extractors)}")
    print(f"  Output: {output_dir}")
    print(f"{'='*70}\n")

    if dry_run:
        print("[DRY RUN] Prompt that would be sent:\n")
        print(prompt[:300] + "...\n")
        print(f"[DRY RUN] Source text length: {len(source_text)} chars")
        print(f"[DRY RUN] Would send to: {', '.join(extractors)}")
        return {}

    for ext_name in extractors:
        cfg = EXTRACTORS.get(ext_name)
        if not cfg:
            print(f"[!] Unknown extractor: {ext_name}")
            continue

        key = os.environ.get(cfg["key_env"])
        if not key:
            print(f"[!] No API key for {ext_name} ({cfg['key_env']}), skipping")
            continue

        print(f"[>] Extracting with {ext_name} ({cfg['model']})...", end=" ", flush=True)

        try:
            result = call_extractor(ext_name, prompt, source_text)
            results[ext_name] = result

            out_file = output_dir / f"extraction_{source_label}_{grain}_{ext_name}_{timestamp}.md"
            out_file.write_text(
                f"# Operator Extraction: {ext_name}\n\n"
                f"**Source:** {source_label}\n"
                f"**Extractor:** {ext_name} ({cfg['model']})\n"
                f"**Grain:** {grain}\n"
                f"**Timestamp:** {timestamp}\n"
                f"**Museum-blind:** Yes\n\n"
                f"---\n\n"
                f"{result}\n",
                encoding="utf-8",
            )
            print(f"OK ({len(result)} chars) -> {out_file.name}")

        except Exception as e:
            print(f"FAILED: {e}")
            results[ext_name] = f"ERROR: {e}"

    summary = {
        "timestamp": timestamp,
        "source": source_label,
        "grain": grain,
        "extractors_attempted": extractors,
        "extractors_succeeded": [k for k, v in results.items() if not str(v).startswith("ERROR")],
        "extractors_failed": [k for k, v in results.items() if str(v).startswith("ERROR")],
    }

    summary_file = output_dir / f"extraction_summary_{source_label}_{grain}_{timestamp}.json"
    summary_file.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    print(f"\n{'='*70}")
    print(f"EXTRACTION COMPLETE")
    print(f"  Succeeded: {len(summary['extractors_succeeded'])}/{len(extractors)}")
    print(f"  Failed: {len(summary['extractors_failed'])}")
    print(f"  Summary: {summary_file.name}")
    print(f"{'='*70}\n")

    return results


def main():
    parser = argparse.ArgumentParser(description="CA Multi-Extractor Operator Recovery")
    parser.add_argument("--source", type=str, help="Path to CFA JSON or raw text file")
    parser.add_argument("--raw", action="store_true", help="Treat source as raw text (not CFA JSON)")
    parser.add_argument("--negative-controls", action="store_true", help="Run negative control battery")
    parser.add_argument("--extractors", type=str, default="claude,gpt,gemini,grok",
                        help="Comma-separated extractor names (default: claude,gpt,gemini,grok)")
    parser.add_argument("--grain", choices=["coarse", "standard", "fine"], default="standard",
                        help="Extraction granularity (default: standard)")
    parser.add_argument("--output", type=str, default=None, help="Output directory override")
    parser.add_argument("--dry-run", action="store_true", help="Print prompts without calling APIs")
    args = parser.parse_args()

    extractors = [e.strip() for e in args.extractors.split(",")]
    output_dir = Path(args.output) if args.output else OUTPUT_DIR

    if args.negative_controls:
        print("\n[*] RUNNING NEGATIVE CONTROL BATTERY\n")
        for label, text in NEGATIVE_CONTROLS.items():
            run_extraction(text, f"neg_{label}", extractors, args.grain, output_dir, args.dry_run)
        return

    if not args.source:
        parser.error("--source is required (unless using --negative-controls)")

    source_path = Path(args.source)
    if not source_path.exists():
        print(f"[!] Source file not found: {source_path}")
        sys.exit(1)

    if args.raw:
        source_text = source_path.read_text(encoding="utf-8")
        source_label = source_path.stem
    else:
        print(f"[*] Extracting transcript from CFA JSON: {source_path.name}")
        transcript_data = extract_transcript_from_cfa(source_path)
        source_text = build_source_text(transcript_data)
        source_label = f"cfa_{transcript_data['metadata']['stance']}_{transcript_data['metadata']['session_id'][:8]}"

        meta = transcript_data["metadata"]
        print(f"    Stance: {meta['stance']}")
        print(f"    Subject: {meta['subject']} vs {meta['opponent']}")
        print(f"    Condition: {meta['condition']}")
        print(f"    Metrics extracted: {list(transcript_data['transcripts'].keys())}")
        print(f"    Total text: {len(source_text)} chars")

    run_extraction(source_text, source_label, extractors, args.grain, output_dir, args.dry_run)


if __name__ == "__main__":
    main()
