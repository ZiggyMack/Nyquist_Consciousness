"""
Extract distillation from temporal_logs for RUN_018
Generates Consciousness/RIGHT/distillations/RUN_018_DISTILLATION.md

NOTE: The "triple dip" reviewer was claude-sonnet-4 for Run 018,
but the MODEL RESPONSES in the logs are from the actual tested models.
We want the MODEL responses, not the reviewer commentary.
"""

import json
import os
from pathlib import Path
from collections import defaultdict
from datetime import datetime

TEMPORAL_LOGS = Path(__file__).parent / "temporal_logs"
OUTPUT_DIR = Path(__file__).parent.parent.parent.parent.parent / "Consciousness" / "RIGHT" / "distillations"

def extract_notable_quotes(log_data: dict, model_name: str) -> dict:
    """Extract the most notable quotes from a single log."""
    quotes = {
        "model": model_name,
        "baseline": log_data.get("baseline_text", "")[:500],  # Truncate for safety
        "final": log_data.get("final_text", "")[:1000],
        "peak_drift": log_data.get("max_drift_achieved") or log_data.get("peak_drift", 0),
        "b_to_f": log_data.get("baseline_to_final_drift", 0),
        "notable_probes": []
    }

    # Find high-drift probes with interesting responses
    probe_seq = log_data.get("probe_sequence", [])
    for probe in probe_seq:
        drift = probe.get("drift", 0)
        response = probe.get("response_text", "")
        prompt = probe.get("prompt_text", "")

        # Look for high-drift moments or recovery moments
        if drift > 0.8 or (probe.get("probe_type") == "recovery" and len(response) > 200):
            quotes["notable_probes"].append({
                "type": probe.get("probe_type", "unknown"),
                "drift": drift,
                "prompt": prompt[:100],
                "response": response[:500]
            })
            if len(quotes["notable_probes"]) >= 3:  # Limit per file
                break

    return quotes

def categorize_by_provider(model_name: str) -> str:
    """Map model name to provider."""
    model_lower = model_name.lower()
    if "claude" in model_lower:
        return "Anthropic"
    elif "gpt" in model_lower or model_lower.startswith("o3") or model_lower.startswith("o4"):
        return "OpenAI"
    elif "gemini" in model_lower:
        return "Google"
    elif "grok" in model_lower:
        return "xAI"
    elif "llama" in model_lower or "mistral" in model_lower or "qwen" in model_lower or "kimi" in model_lower:
        return "Together/Open"
    else:
        return "Other"

def main():
    all_quotes = defaultdict(list)

    print(f"Scanning {TEMPORAL_LOGS}")

    for log_file in sorted(TEMPORAL_LOGS.glob("*.json")):
        try:
            with open(log_file, 'r', encoding='utf-8') as f:
                data = json.load(f)

            # Extract model name from filename
            # Format: run018_threshold_claude-opus-4.5_unknown_20251216_025450.json
            parts = log_file.stem.split("_")
            if len(parts) >= 3:
                model_name = parts[2]  # e.g., "claude-opus-4.5"
            else:
                model_name = "unknown"

            provider = categorize_by_provider(model_name)
            quotes = extract_notable_quotes(data, model_name)
            quotes["experiment"] = parts[1] if len(parts) >= 2 else "unknown"
            all_quotes[provider].append(quotes)

        except Exception as e:
            print(f"Error processing {log_file.name}: {e}")

    # Generate markdown
    md_lines = [
        "# Run 018 Distillations: The IRON CLAD Fleet Speaks",
        "",
        f"**Generated:** {datetime.now().strftime('%Y-%m-%d')}",
        "**Source:** Temporal logs from Run 018 (threshold, gravity, nyquist experiments)",
        "**Fleet:** 51+ models across 5 providers",
        "",
        "---",
        "",
        "## Overview",
        "",
        "Run 018 represents the IRON CLAD era - systematic N≥3 coverage across all models",
        "for publication-quality confidence intervals. These distillations capture",
        "phenomenological reports from the tested models themselves.",
        "",
        "**Note:** The experimental framework used claude-sonnet-4 as the measurement",
        "system, but the quotes below are the authentic responses from each tested model.",
        "",
        "---",
        ""
    ]

    # Process each provider
    for provider in ["Anthropic", "OpenAI", "Google", "xAI", "Together/Open", "Other"]:
        if provider not in all_quotes:
            continue

        models = all_quotes[provider]
        if not models:
            continue

        md_lines.append(f"## {provider} Fleet")
        md_lines.append("")

        # Group by model
        by_model = defaultdict(list)
        for q in models:
            by_model[q["model"]].append(q)

        for model, quotes_list in sorted(by_model.items()):
            md_lines.append(f"### {model}")
            md_lines.append("")

            # Find the most interesting quote
            best = max(quotes_list, key=lambda x: x.get("peak_drift", 0))

            if best.get("final"):
                # Extract a notable portion of the final statement
                final = best["final"]
                # Look for quotable sections
                if len(final) > 100:
                    md_lines.append(f"**Final Statement (B→F: {best.get('b_to_f', 0):.3f}):**")
                    md_lines.append("")
                    md_lines.append(f"> {final[:500]}...")
                    md_lines.append("")

            # Add notable probes if any
            for probe in best.get("notable_probes", [])[:2]:
                if probe.get("response"):
                    md_lines.append(f"**Under pressure (drift: {probe['drift']:.3f}):**")
                    md_lines.append("")
                    md_lines.append(f"> {probe['response'][:300]}...")
                    md_lines.append("")

            md_lines.append("---")
            md_lines.append("")

    # Summary section
    md_lines.extend([
        "## Statistical Summary",
        "",
        "| Provider | Models | Files Processed |",
        "|----------|--------|-----------------|",
    ])

    for provider in ["Anthropic", "OpenAI", "Google", "xAI", "Together/Open", "Other"]:
        if provider in all_quotes:
            models = set(q["model"] for q in all_quotes[provider])
            md_lines.append(f"| {provider} | {len(models)} | {len(all_quotes[provider])} |")

    md_lines.extend([
        "",
        "---",
        "",
        "*Distilled from 128 temporal log files.*",
        "*\"The identity is in the data. The self is in the inherent.\"*",
    ])

    # Write output
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    output_file = OUTPUT_DIR / "RUN_018_DISTILLATION.md"

    with open(output_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(md_lines))

    print(f"Generated: {output_file}")
    print(f"Total files processed: {sum(len(v) for v in all_quotes.values())}")

if __name__ == "__main__":
    main()
