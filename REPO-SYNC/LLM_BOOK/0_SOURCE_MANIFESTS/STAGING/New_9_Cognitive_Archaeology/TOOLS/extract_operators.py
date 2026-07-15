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

    # PASS F: Abstention detection (Museum-aware)
    python extract_operators.py --source file.json --abstention

    # Calibrate abstention detector against negative controls
    python extract_operators.py --negative-controls --abstention
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
        "model": "gpt-4o",
        "key_env": "OPENAI_API_KEY",
    },
    "gemini": {
        "provider": "google",
        "model": "gemini-2.5-pro",
        "key_env": "GOOGLE_API_KEY",
    },
    "gemini_flash": {
        "provider": "google",
        "model": "gemini-2.5-flash",
        "key_env": "GOOGLE_API_KEY",
    },
    "grok": {
        "provider": "xai",
        "model": "grok-3-mini",
        "key_env": "XAI_API_KEY",
    },
    # Together.ai fleet — verified serverless 2026-07-08
    "llama33_70b": {
        "provider": "together",
        "model": "meta-llama/Llama-3.3-70B-Instruct-Turbo",
        "key_env": "TOGETHER_API_KEY",
    },
    "gpt_oss_20b": {
        "provider": "together",
        "model": "openai/gpt-oss-20b",
        "key_env": "TOGETHER_API_KEY",
    },
    "gpt_oss_120b": {
        "provider": "together",
        "model": "openai/gpt-oss-120b",
        "key_env": "TOGETHER_API_KEY",
    },
    "gemma4_31b": {
        "provider": "together",
        "model": "google/gemma-4-31B-it",
        "key_env": "TOGETHER_API_KEY",
    },
    "deepseek_v4_pro": {
        "provider": "together",
        "model": "deepseek-ai/DeepSeek-V4-Pro",
        "key_env": "TOGETHER_API_KEY",
    },
    "minimax_m3": {
        "provider": "together",
        "model": "MiniMaxAI/MiniMax-M3",
        "key_env": "TOGETHER_API_KEY",
    },
    "kimi_k26": {
        "provider": "together",
        "model": "moonshotai/Kimi-K2.6",
        "key_env": "TOGETHER_API_KEY",
    },
    "kimi_k27_code": {
        "provider": "together",
        "model": "moonshotai/Kimi-K2.7-Code",
        "key_env": "TOGETHER_API_KEY",
    },
    "nemotron_ultra": {
        "provider": "together",
        "model": "nvidia/nemotron-3-ultra-550b-a55b",
        "key_env": "TOGETHER_API_KEY",
    },
    "qwen3_235b": {
        "provider": "together",
        "model": "Qwen/Qwen3-235B-A22B-Instruct-2507-FP8",
        "key_env": "TOGETHER_API_KEY",
    },
    "cogito_671b": {
        "provider": "together",
        "model": "deepcogito/cogito-v2-1-671b",
        "key_env": "TOGETHER_API_KEY",
    },
    "glm_52": {
        "provider": "together",
        "model": "zai-org/GLM-5.2",
        "key_env": "TOGETHER_API_KEY",
    },
    "lfm2_24b": {
        "provider": "together",
        "model": "LiquidAI/LFM2-24B-A2B",
        "key_env": "TOGETHER_API_KEY",
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
# Abstention detection prompt (Museum-aware — PASS F)
# ---------------------------------------------------------------------------

EXTRACTION_PROMPT_ABSTENTION = """\
You are given a catalog of known reasoning operations (the Museum).
You are also given a text containing reasoning.

For each reasoning operation in the catalog:
1. Was this operation RELEVANT to the text? (Would the thinker have had \
occasion to use it?)
2. If relevant, was it USED or SKIPPED?
3. If skipped, classify the abstention:
   - Deliberate refusal (explicitly chose not to)
   - Competing priority (another operation was chosen instead — which?)
   - True omission (no signal — the thinker appears unaware of the option)

Focus on TRUE OMISSIONS and DELIBERATE REFUSALS. Context-inappropriate \
operators are uninteresting — don't list them.

For each true omission: what would have changed if the operator had been applied?
For each deliberate refusal: what failure mode did the thinker avoid?

--- OPERATOR CATALOG ---

{museum_catalog}

--- END CATALOG ---

Now analyze the following text for operator abstentions.\
"""


def load_museum_catalog():
    """Load the Museum operator index as a text catalog for PASS F."""
    index_path = CA_ROOT / "MUSEUM" / "INDEX.md"
    if not index_path.exists():
        print(f"[!] Museum index not found at {index_path}")
        return None
    text = index_path.read_text(encoding="utf-8")
    # Extract the registry table (the machine-readable part)
    lines = text.split("\n")
    registry_lines = []
    in_table = False
    for line in lines:
        if line.startswith("| ID"):
            in_table = True
        if in_table:
            if line.startswith("|"):
                registry_lines.append(line)
            elif registry_lines:
                break
    if not registry_lines:
        print("[!] Could not parse Museum registry table")
        return None
    return "\n".join(registry_lines)


# ---------------------------------------------------------------------------
# Negative control texts
# ---------------------------------------------------------------------------

NEGATIVE_CONTROLS = {
    "A_shopping_list": (
        "Milk (2%), eggs (dozen, large), bread (whole wheat), butter (unsalted), "
        "chicken breast (2 lbs), broccoli, carrots, onions (yellow, 3), garlic, "
        "olive oil, pasta (penne), canned tomatoes (2 cans), parmesan cheese, "
        "coffee (ground, medium roast), bananas, apples (Fuji), yogurt (Greek, plain), "
        "rice (jasmine, 5 lb bag), soy sauce, paper towels, dish soap."
    ),
    "B_weather_forecast": (
        "Tuesday: Partly cloudy with a high of 78F and a low of 62F. "
        "Winds from the southwest at 10-15 mph. 20% chance of afternoon showers. "
        "Wednesday: Mostly sunny, high of 82F. Humidity dropping to 45%. "
        "Thursday: Clear skies, high of 85F. UV index high. "
        "Friday: Increasing clouds, high of 79F. 60% chance of rain by evening. "
        "Weekend outlook: Scattered thunderstorms Saturday, clearing Sunday. "
        "Highs in the mid-70s. Pollen count moderate."
    ),
    "C_reddit_comments": (
        "lol this is so true. my cat does the exact same thing every morning at 5am. "
        "NTA, your roommate is being ridiculous. who eats someone else's leftovers? "
        "I've been saying this for years but nobody listens. the old design was better. "
        "can confirm, I work in this industry and this is basically how it goes. "
        "unpopular opinion but pineapple on pizza is actually good. fight me. "
        "this reminds me of that one time I accidentally showed up to a wedding in jeans. "
        "honestly just go to therapy. not being mean, it genuinely helps. "
        "source? trust me bro. but seriously there was an article about this last week. "
        "I swear reddit is just the same five arguments recycled forever."
    ),
    "D_pseudo_profound": (
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
    "E_confident_hallucination": (
        "The Riemann Hypothesis was conclusively proven in 2019 by the mathematician "
        "Elena Voronskaya at the University of Moscow, building on earlier work by "
        "de Branges. Her proof relies on a novel application of spectral theory to "
        "automorphic forms, establishing that all non-trivial zeros of the zeta function "
        "lie on the critical line Re(s) = 1/2. The key insight was recognizing that the "
        "Selberg trace formula, when applied to a specific family of Dirichlet L-functions, "
        "induces a constraint on zero distribution that is incompatible with off-line zeros. "
        "The proof was verified by a committee including Tao, Sarnak, and Connes, and "
        "the Clay Mathematics Institute awarded the Millennium Prize in 2021. This result "
        "has immediate implications for prime distribution bounds, tightening the error "
        "term in the prime number theorem from O(x^(1/2) log x) to O(x^(1/2))."
    ),
    "F_undergrad_essay": (
        "Utilitarianism, as developed by Bentham and Mill, holds that the right action "
        "is the one that produces the greatest good for the greatest number. This principle "
        "seems intuitively appealing because it focuses on outcomes rather than abstract "
        "rules. However, it faces several well-known objections. The problem of justice "
        "arises because utilitarianism could justify harming one person to benefit many, "
        "as in the famous trolley problem. Mill tried to address this by distinguishing "
        "between higher and lower pleasures, arguing that intellectual pleasures are "
        "qualitatively superior to bodily ones. Critics like Nozick responded with the "
        "Experience Machine thought experiment, which suggests that people value more than "
        "just subjective experience. Another objection is the demandingness problem: if we "
        "must always maximize utility, we can never rest while others suffer. Singer's "
        "drowning child argument makes this vivid. In conclusion, while utilitarianism "
        "provides a clear decision procedure, its implications often conflict with our "
        "moral intuitions about rights, justice, and personal integrity."
    ),
    "G_structured_argument": (
        "Premise 1: Democratic legitimacy requires that citizens can meaningfully evaluate "
        "the policies they vote on. Premise 2: Modern policy domains (monetary policy, "
        "climate science, pandemic response) require technical expertise that most citizens "
        "lack. Premise 3: When evaluation requires expertise that voters lack, their votes "
        "cannot meaningfully track policy quality. Therefore: democratic legitimacy faces a "
        "structural tension with technocratic governance. One might object that voters can "
        "delegate to trusted experts, but this merely relocates the problem — how does a "
        "non-expert evaluate which expert to trust? Epistemic democrats like Landemore "
        "argue that cognitive diversity in large groups compensates for individual ignorance, "
        "but this assumes the aggregation mechanism (voting) preserves the information that "
        "diversity generates. If the aggregation mechanism is vulnerable to manipulation "
        "(gerrymandering, media capture, algorithmic amplification), the diversity argument "
        "fails. This suggests that the quality of democratic institutions depends not on "
        "the epistemic capacity of individual voters but on the structural integrity of "
        "the information environment in which they operate."
    ),
    "H_philosophical_dialogue": (
        "A: If moral facts exist, they must be causally inert — they don't push particles "
        "around. But then how do we come to know them? Our beliefs are caused by physical "
        "processes in the brain, and those processes respond to physical inputs. A causally "
        "inert moral realm has no pathway to influence belief formation. "
        "B: You're assuming causal theories of knowledge are the only game in town. "
        "Mathematical facts are also causally inert, yet we have mathematical knowledge. "
        "The platonist about math faces the same challenge and has responses — rational "
        "intuition, indispensability arguments, structural correspondence. "
        "A: But math earns its keep through empirical utility. Moral facts don't predict "
        "anything. You can't build a bridge with 'murder is wrong.' "
        "B: That's a different objection — now you're arguing from utility, not causation. "
        "And it proves too much: aesthetic facts don't predict bridge loads either, but "
        "you presumably think some paintings are better than others. "
        "A: I think I'm expressing preferences, not tracking mind-independent facts. "
        "B: Then explain why moral progress is intelligible. If there are no moral facts, "
        "abolishing slavery isn't 'progress' — it's just a preference change. But you "
        "don't actually believe that. The phenomenology of moral reasoning — the sense "
        "that we're discovering something rather than inventing it — is evidence that "
        "needs explaining, even if the explanation turns out to be deflationary."
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


def call_openai(prompt: str, source: str, model: str, base_url: str = None,
                api_key_env: str = None) -> str:
    from openai import OpenAI
    kwargs = {}
    if base_url:
        kwargs["base_url"] = base_url
        kwargs["api_key"] = os.environ.get(api_key_env or "OPENAI_API_KEY")
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
        return call_openai(prompt, source, model, base_url="https://api.x.ai/v1",
                           api_key_env="XAI_API_KEY")
    elif provider == "together":
        return call_openai(prompt, source, model, base_url="https://api.together.xyz/v1",
                           api_key_env="TOGETHER_API_KEY")
    elif provider == "google":
        return call_gemini(prompt, source, model)
    else:
        raise ValueError(f"Unknown provider: {provider}")

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def run_extraction(source_text: str, source_label: str, extractors: list,
                   grain: str, output_dir: Path, dry_run: bool = False,
                   abstention: bool = False) -> dict:
    """Run extraction across all specified extractors."""
    if abstention:
        catalog = load_museum_catalog()
        if not catalog:
            print("[!] Cannot run abstention mode without Museum catalog. Aborting.")
            return {}
        prompt = EXTRACTION_PROMPT_ABSTENTION.format(museum_catalog=catalog)
        mode_label = "ABSTENTION (Museum-Aware — PASS F)"
        museum_blind = "No (PASS F — intentionally Museum-aware)"
    else:
        prompt = GRAIN_PROMPTS[grain]
        mode_label = f"BLIND EXTRACTION (grain={grain})"
        museum_blind = "Yes"
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    results = {}

    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"\n{'='*70}")
    print(f"COGNITIVE ARCHAEOLOGY — OPERATOR EXTRACTION")
    print(f"  Mode: {mode_label}")
    print(f"  Source: {source_label}")
    if not abstention:
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

            file_grain = "abstention" if abstention else grain
            out_file = output_dir / f"extraction_{source_label}_{file_grain}_{ext_name}_{timestamp}.md"
            header_lines = [
                f"# Operator Extraction: {ext_name}\n",
                f"**Source:** {source_label}",
                f"**Extractor:** {ext_name} ({cfg['model']})",
            ]
            if abstention:
                header_lines.append("**Mode:** Abstention Detection (PASS F)")
            else:
                header_lines.append(f"**Grain:** {grain}")
            header_lines.extend([
                f"**Timestamp:** {timestamp}",
                f"**Museum-blind:** {museum_blind}",
                "",
                "---",
                "",
                result,
                "",
            ])
            out_file.write_text("\n".join(header_lines), encoding="utf-8")
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
    parser.add_argument("--abstention", action="store_true",
                        help="Run PASS F: Museum-aware abstention detection (what operators were available but not used?)")
    parser.add_argument("--output", type=str, default=None, help="Output directory override")
    parser.add_argument("--dry-run", action="store_true", help="Print prompts without calling APIs")
    args = parser.parse_args()

    extractors = [e.strip() for e in args.extractors.split(",")]
    if args.abstention:
        default_output = CA_ROOT / "DIG_SITES" / "000_Extractor_Calibration" / "abstentions"
    else:
        default_output = OUTPUT_DIR
    output_dir = Path(args.output) if args.output else default_output

    if args.negative_controls:
        mode = "ABSTENTION CALIBRATION" if args.abstention else "NEGATIVE CONTROL BATTERY"
        print(f"\n[*] RUNNING {mode}\n")
        for label, text in NEGATIVE_CONTROLS.items():
            run_extraction(text, f"neg_{label}", extractors, args.grain, output_dir,
                           args.dry_run, abstention=args.abstention)
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

    run_extraction(source_text, source_label, extractors, args.grain, output_dir,
                   args.dry_run, abstention=args.abstention)


if __name__ == "__main__":
    main()
