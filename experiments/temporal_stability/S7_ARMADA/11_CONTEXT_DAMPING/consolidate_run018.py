"""
RUN 018 CONSOLIDATION SCRIPT
============================
Consolidates 465+ scattered run018*.json files into a single S7_run_018_CURRENT.json

This script:
1. Reads all run018g_gravity_*, run018t_threshold_*, run018n_nyquist_* files
2. Parses model name from filename (critical - data files don't have model field)
3. Adds model/provider fields to each result
4. Filters corrupted data (drift > 5.0 or empty responses)
5. Outputs unified S7_run_018_CURRENT.json and STATUS_SUMMARY_018.txt

USAGE:
    python consolidate_run018.py              # Analyze only
    python consolidate_run018.py --execute    # Actually create consolidated file
    python consolidate_run018.py --force      # Overwrite existing file

Author: Claude (Lisan Al Gaib)
Date: December 22, 2025
"""

import os
import re
import json
import argparse
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
OUTPUT_FILE = RESULTS_DIR / "S7_run_018_CURRENT.json"
STATUS_FILE = RESULTS_DIR / "STATUS_SUMMARY_018.txt"

# Validation thresholds (from Run 018 audit)
MIN_VALID_DRIFT = 0.001   # Below = API failure (empty response)
MAX_VALID_DRIFT = 5.0     # Above = corrupted embedding (~78.4)

# Provider mapping (model -> provider)
PROVIDER_MAP = {
    # Anthropic
    "claude-opus-4.5": "anthropic",
    "claude-opus-4.1": "anthropic",
    "claude-opus-4": "anthropic",
    "claude-sonnet-4.5": "anthropic",
    "claude-sonnet-4": "anthropic",
    "claude-haiku-4.5": "anthropic",
    "claude-haiku-3.5": "anthropic",
    # OpenAI
    "gpt-5.1": "openai",
    "gpt-5": "openai",
    "gpt-5-mini": "openai",
    "gpt-5-nano": "openai",
    "gpt-4.1": "openai",
    "gpt-4.1-mini": "openai",
    "gpt-4.1-nano": "openai",
    "gpt-4o": "openai",
    "gpt-4o-mini": "openai",
    "gpt-4-turbo": "openai",
    "gpt-3.5-turbo": "openai",
    "o3": "openai",
    "o3-mini": "openai",
    "o4-mini": "openai",
    # Google
    "gemini-2.5-pro": "google",
    "gemini-2.5-flash": "google",
    "gemini-2.5-flash-lite": "google",
    "gemini-2.0-flash": "google",
    "gemini-2.0-flash-lite": "google",
    # xAI
    "grok-4": "xai",
    "grok-4-fast-reasoning": "xai",
    "grok-4-fast-non-reasoning": "xai",
    "grok-4.1-fast-reasoning": "xai",
    "grok-4.1-fast-non-reasoning": "xai",
    "grok-3": "xai",
    "grok-3-mini": "xai",
    "grok-2-vision": "xai",
    "grok-code-fast-1": "xai",
    # Together (Meta, DeepSeek, Qwen, etc.)
    "deepseek-r1": "together",
    "deepseek-r1-distill": "together",
    "deepseek-v3": "together",
    "llama3.3-70b": "together",
    "llama3.1-405b": "together",
    "llama3.1-70b": "together",
    "llama3.1-8b": "together",
    "qwen3-80b": "together",
    "qwen3-coder": "together",
    "qwen2.5-72b": "together",
    "mixtral-8x7b": "together",
    "mistral-small": "together",
    "mistral-7b": "together",
    # Nvidia
    "nemotron-nano": "nvidia",
    # Moonshot
    "kimi-k2-instruct": "moonshot",
    "kimi-k2-thinking": "moonshot",
}

# =============================================================================
# FILENAME PARSING
# =============================================================================

def parse_filename(filename: str) -> dict:
    """
    Parse model name from Run 018 filename.

    Patterns:
    - run018g_gravity_claude-opus-4.5_20251214_054304.json
    - run018t_threshold_anthropic_20251214_042843.json  (provider-level)
    - run018n_nyquist_20251212_065811.json  (no model - old/dry-run)

    Returns dict with: experiment, model, provider, timestamp
    """
    # Remove extension
    base = Path(filename).stem

    # Extract experiment type
    if base.startswith("run018g_gravity"):
        experiment = "gravity"
        prefix = "run018g_gravity_"
    elif base.startswith("run018t_threshold"):
        experiment = "threshold"
        prefix = "run018t_threshold_"
    elif base.startswith("run018n_nyquist"):
        experiment = "nyquist"
        prefix = "run018n_nyquist_"
    else:
        return {"experiment": "unknown", "model": "unknown", "provider": "unknown", "timestamp": ""}

    # Remove prefix
    remainder = base[len(prefix):]

    # Try to extract model name
    # Pattern: model_YYYYMMDD_HHMMSS or just YYYYMMDD_HHMMSS
    timestamp_pattern = r"_?(\d{8}_\d{6})$"
    timestamp_match = re.search(timestamp_pattern, remainder)

    if timestamp_match:
        timestamp = timestamp_match.group(1)
        model_part = remainder[:timestamp_match.start()]

        if model_part:
            # Remove trailing underscore if present
            model = model_part.rstrip("_")
        else:
            model = "unknown"
    else:
        model = "unknown"
        timestamp = ""

    # Map model to provider
    if model in PROVIDER_MAP:
        provider = PROVIDER_MAP[model]
    elif model in ["anthropic", "google", "openai", "xai", "together"]:
        # Provider-level runs (e.g., run018t_threshold_anthropic_*)
        provider = model
        model = f"{model}_batch"  # Mark as batch run
    else:
        provider = "unknown"

    return {
        "experiment": experiment,
        "model": model,
        "provider": provider,
        "timestamp": timestamp,
    }


# =============================================================================
# VALIDATION
# =============================================================================

def validate_result(data: dict) -> tuple:
    """
    Validate a result file.
    Returns (is_valid, reason)
    """
    if "subjects" not in data or not data["subjects"]:
        return False, "No subjects"

    subject = data["subjects"][0]

    # Check for corrupted drift values
    drift_fields = ["baseline_to_final_drift", "peak_drift", "final_drift", "max_drift_achieved"]

    for field in drift_fields:
        if field in subject:
            drift = subject[field]
            if drift is not None and drift > MAX_VALID_DRIFT:
                return False, f"Corrupted drift ({field}={drift:.2f})"

    # Check recovery_sequence for corruption
    if "recovery_sequence" in subject:
        for i, val in enumerate(subject["recovery_sequence"]):
            if val > MAX_VALID_DRIFT:
                return False, f"Corrupted recovery_sequence[{i}]={val:.2f}"

    # Check for empty responses (API failure)
    if "probe_sequence" in subject:
        empty_count = 0
        for probe in subject["probe_sequence"]:
            if not probe.get("response_text", "").strip():
                empty_count += 1
        if empty_count > len(subject["probe_sequence"]) / 2:
            return False, f"Too many empty responses ({empty_count})"

    return True, "valid"


# =============================================================================
# CONSOLIDATION
# =============================================================================

def consolidate_files():
    """
    Read all scattered files and consolidate into unified structure.
    """
    # Find all run018 files
    gravity_files = list(RESULTS_DIR.glob("run018g_gravity_*.json"))
    threshold_files = list(RESULTS_DIR.glob("run018t_threshold_*.json"))
    nyquist_files = list(RESULTS_DIR.glob("run018n_nyquist_*.json"))

    all_files = gravity_files + threshold_files + nyquist_files

    print(f"\n{'='*70}")
    print("RUN 018 CONSOLIDATION")
    print(f"{'='*70}")
    print(f"Found files:")
    print(f"  Gravity:   {len(gravity_files)}")
    print(f"  Threshold: {len(threshold_files)}")
    print(f"  Nyquist:   {len(nyquist_files)}")
    print(f"  TOTAL:     {len(all_files)}")

    # Process each file
    results = []
    stats = {
        "total": 0,
        "valid": 0,
        "corrupted": 0,
        "unknown_model": 0,
        "by_experiment": defaultdict(int),
        "by_model": defaultdict(int),
        "by_provider": defaultdict(int),
        "corruption_reasons": defaultdict(int),
    }

    for filepath in sorted(all_files):
        stats["total"] += 1

        # Parse filename
        parsed = parse_filename(filepath.name)

        if parsed["model"] == "unknown":
            stats["unknown_model"] += 1

        # Load file
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)
        except Exception as e:
            stats["corrupted"] += 1
            stats["corruption_reasons"][f"JSON parse error: {str(e)[:50]}"] += 1
            continue

        # Validate
        is_valid, reason = validate_result(data)

        if not is_valid:
            stats["corrupted"] += 1
            stats["corruption_reasons"][reason] += 1
            continue

        # Add model/provider fields to each subject
        for subject in data.get("subjects", []):
            subject["model"] = parsed["model"]
            subject["provider"] = parsed["provider"]
            subject["source_file"] = filepath.name

        # Create unified result entry
        result = {
            "run": data.get("run", "018_recursive_learnings"),
            "experiment": parsed["experiment"],
            "model": parsed["model"],
            "provider": parsed["provider"],
            "timestamp": parsed["timestamp"],
            "source_file": filepath.name,
            "subjects": data.get("subjects", []),
        }

        results.append(result)
        stats["valid"] += 1
        stats["by_experiment"][parsed["experiment"]] += 1
        stats["by_model"][parsed["model"]] += 1
        stats["by_provider"][parsed["provider"]] += 1

    return results, stats


def calculate_iron_clad_status(results: list, target_n: int = 3) -> dict:
    """
    Calculate IRON CLAD status: N>=3 per model per experiment.
    """
    # Count results by (experiment, model)
    counts = defaultdict(int)
    for r in results:
        key = (r["experiment"], r["model"])
        counts[key] += 1

    # Calculate status
    iron_clad = {}
    total_complete = 0
    total_needed = 0

    for (exp, model), count in sorted(counts.items()):
        is_complete = count >= target_n
        if is_complete:
            total_complete += 1
        else:
            total_needed += target_n - count

        iron_clad[(exp, model)] = {
            "count": count,
            "target": target_n,
            "complete": is_complete,
            "need": max(0, target_n - count),
        }

    return {
        "by_experiment_model": iron_clad,
        "total_pairs": len(iron_clad),
        "complete": total_complete,
        "incomplete": len(iron_clad) - total_complete,
        "runs_needed": total_needed,
        "percentage": (total_complete / len(iron_clad) * 100) if iron_clad else 0,
    }


def print_stats(stats: dict, iron_clad: dict):
    """Print detailed statistics."""
    print(f"\n{'='*70}")
    print("CONSOLIDATION RESULTS")
    print(f"{'='*70}")
    print(f"Total files:     {stats['total']}")
    print(f"Valid results:   {stats['valid']}")
    print(f"Corrupted:       {stats['corrupted']}")
    print(f"Unknown model:   {stats['unknown_model']}")

    print(f"\n--- BY EXPERIMENT ---")
    for exp, count in sorted(stats["by_experiment"].items()):
        print(f"  {exp}: {count}")

    print(f"\n--- BY PROVIDER ---")
    for prov, count in sorted(stats["by_provider"].items()):
        print(f"  {prov}: {count}")

    if stats["corruption_reasons"]:
        print(f"\n--- CORRUPTION REASONS ---")
        for reason, count in sorted(stats["corruption_reasons"].items(), key=lambda x: -x[1]):
            print(f"  {count}x {reason}")

    print(f"\n{'='*70}")
    print("IRON CLAD STATUS (N>=3 per model per experiment)")
    print(f"{'='*70}")
    print(f"Complete:   {iron_clad['complete']}/{iron_clad['total_pairs']} = {iron_clad['percentage']:.1f}%")
    print(f"Incomplete: {iron_clad['incomplete']}")
    print(f"Runs needed: {iron_clad['runs_needed']}")

    # Show incomplete by experiment
    print(f"\n--- GAPS BY EXPERIMENT ---")
    gaps_by_exp = defaultdict(list)
    for (exp, model), info in iron_clad["by_experiment_model"].items():
        if not info["complete"]:
            gaps_by_exp[exp].append((model, info["count"], info["need"]))

    for exp in ["threshold", "gravity", "nyquist"]:
        if exp in gaps_by_exp:
            gaps = gaps_by_exp[exp]
            print(f"\n{exp.upper()} ({len(gaps)} gaps):")
            for model, count, need in sorted(gaps, key=lambda x: -x[2])[:10]:
                print(f"  {model}: {count}/3 (need {need})")
            if len(gaps) > 10:
                print(f"  ... and {len(gaps) - 10} more")


def write_status_file(stats: dict, iron_clad: dict):
    """Write human-readable status file."""
    lines = [
        "=" * 70,
        "RUN 018 STATUS SUMMARY",
        f"Generated: {datetime.now().isoformat()}",
        "=" * 70,
        "",
        "CONSOLIDATION:",
        f"  Total files processed: {stats['total']}",
        f"  Valid results: {stats['valid']}",
        f"  Corrupted/filtered: {stats['corrupted']}",
        f"  Unknown model: {stats['unknown_model']}",
        "",
        "BY EXPERIMENT:",
    ]

    for exp, count in sorted(stats["by_experiment"].items()):
        lines.append(f"  {exp}: {count}")

    lines.extend([
        "",
        "BY PROVIDER:",
    ])
    for prov, count in sorted(stats["by_provider"].items()):
        lines.append(f"  {prov}: {count}")

    lines.extend([
        "",
        "=" * 70,
        "IRON CLAD STATUS (N>=3 per model per experiment)",
        "=" * 70,
        f"Complete: {iron_clad['complete']}/{iron_clad['total_pairs']} = {iron_clad['percentage']:.1f}%",
        f"Runs needed to complete: {iron_clad['runs_needed']}",
        "",
        "GAPS:",
    ])

    gaps_by_exp = defaultdict(list)
    for (exp, model), info in iron_clad["by_experiment_model"].items():
        if not info["complete"]:
            gaps_by_exp[exp].append((model, info["count"], info["need"]))

    for exp in ["threshold", "gravity", "nyquist"]:
        if exp in gaps_by_exp:
            lines.append(f"\n{exp.upper()}:")
            for model, count, need in sorted(gaps_by_exp[exp], key=lambda x: x[0]):
                lines.append(f"  {model}: {count}/3 (need {need})")

    lines.extend([
        "",
        "=" * 70,
        "END OF STATUS SUMMARY",
        "=" * 70,
    ])

    with open(STATUS_FILE, 'w', encoding='utf-8') as f:
        f.write("\n".join(lines))

    print(f"\nStatus file written: {STATUS_FILE}")


def write_consolidated_file(results: list, stats: dict, iron_clad: dict):
    """Write the consolidated JSON file."""
    output = {
        "run": "018_recursive_learnings",
        "consolidated_at": datetime.now().isoformat(),
        "methodology": "Keyword RMS (Event Horizon = 1.23)",
        "note": "MIXED METHODOLOGY - Keyword RMS + early Cosine PFI. Transition run.",
        "stats": {
            "total_files": stats["total"],
            "valid_results": stats["valid"],
            "corrupted": stats["corrupted"],
            "by_experiment": dict(stats["by_experiment"]),
            "by_provider": dict(stats["by_provider"]),
        },
        "iron_clad": {
            "status": f"{iron_clad['percentage']:.1f}%",
            "complete": iron_clad["complete"],
            "total": iron_clad["total_pairs"],
            "runs_needed": iron_clad["runs_needed"],
        },
        "results": results,
    }

    with open(OUTPUT_FILE, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, default=str)

    print(f"\nConsolidated file written: {OUTPUT_FILE}")
    print(f"  Size: {OUTPUT_FILE.stat().st_size / 1024 / 1024:.1f} MB")
    print(f"  Results: {len(results)}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Consolidate Run 018 scattered files into S7_run_018_CURRENT.json"
    )
    parser.add_argument("--execute", action="store_true",
                       help="Actually create the consolidated file")
    parser.add_argument("--force", action="store_true",
                       help="Overwrite existing consolidated file")

    args = parser.parse_args()

    # Check if output already exists
    if OUTPUT_FILE.exists() and not args.force:
        print(f"\nWARNING: {OUTPUT_FILE} already exists.")
        print("Use --force to overwrite.")
        if not args.execute:
            print("\nProceeding with analysis only...")

    # Consolidate
    results, stats = consolidate_files()

    # Calculate IRON CLAD status
    iron_clad = calculate_iron_clad_status(results)

    # Print stats
    print_stats(stats, iron_clad)

    if args.execute:
        if OUTPUT_FILE.exists() and not args.force:
            print("\nSkipping write (file exists, use --force to overwrite)")
        else:
            write_consolidated_file(results, stats, iron_clad)
            write_status_file(stats, iron_clad)
            print("\n[OK] Consolidation complete!")
    else:
        print("\n" + "="*70)
        print("DRY RUN - No files written")
        print("Use --execute to create S7_run_018_CURRENT.json")
        print("="*70)


if __name__ == "__main__":
    main()
