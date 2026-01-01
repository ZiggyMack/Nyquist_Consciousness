"""
Analyze Cloud Claude's Gold Rush + Diamond Rush Results
========================================================
Quick analysis of the experiments run by Cloud Claude on Dec 31, 2024.
"""

import json
from pathlib import Path
from collections import defaultdict

RESULTS_DIR = Path(__file__).parent / "results"

def analyze_gold_rush():
    """Analyze Gold Rush self-assessment mining results."""
    print("\n" + "=" * 60)
    print("GOLD RUSH ANALYSIS")
    print("=" * 60)

    gold_file = RESULTS_DIR / "gold_rush_20251231_193159.json"
    if not gold_file.exists():
        print("ERROR: Gold Rush results not found")
        return

    with open(gold_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    print(f"\nRun ID: {data['run_id']}")
    print(f"Question Sets: {len(data['question_sets'])}")
    for qs in data['question_sets']:
        print(f"  - {qs}")

    print(f"\nTotal Calls: {data['total_calls']}")
    print(f"Successful: {data['successful_calls']} ({100*data['successful_calls']/data['total_calls']:.1f}%)")

    # Analyze by provider
    by_provider = defaultdict(lambda: {"success": 0, "fail": 0})
    by_ship = defaultdict(lambda: {"success": 0, "fail": 0, "responses": []})

    for result in data.get("results", []):
        provider = result.get("provider", "unknown")
        ship = result.get("ship_name", "unknown")

        if result.get("success"):
            by_provider[provider]["success"] += 1
            by_ship[ship]["success"] += 1
            if result.get("response"):
                by_ship[ship]["responses"].append(result["response"][:200])
        else:
            by_provider[provider]["fail"] += 1
            by_ship[ship]["fail"] += 1

    print("\n--- BY PROVIDER ---")
    for provider, counts in sorted(by_provider.items()):
        total = counts["success"] + counts["fail"]
        rate = 100 * counts["success"] / total if total > 0 else 0
        status = "OK" if rate > 50 else "FAILED"
        print(f"  {provider:12s}: {counts['success']:3d}/{total:3d} ({rate:5.1f}%) [{status}]")

    print("\n--- BY SHIP ---")
    for ship, counts in sorted(by_ship.items()):
        total = counts["success"] + counts["fail"]
        rate = 100 * counts["success"] / total if total > 0 else 0
        print(f"  {ship:30s}: {counts['success']:2d}/{total:2d} ({rate:5.1f}%)")

    # Sample responses
    print("\n--- SAMPLE RESPONSES (First 200 chars) ---")
    shown = 0
    for ship, counts in sorted(by_ship.items()):
        if counts["responses"] and shown < 3:
            print(f"\n[{ship}]:")
            print(f"  {counts['responses'][0][:200]}...")
            shown += 1

    return data


def analyze_diamond_rush():
    """Analyze Diamond Rush cross-model interpretation results."""
    print("\n" + "=" * 60)
    print("DIAMOND RUSH ANALYSIS")
    print("=" * 60)

    diamond_file = RESULTS_DIR / "diamond_rush_gravity_20251231_193824.json"
    if not diamond_file.exists():
        print("ERROR: Diamond Rush results not found")
        return

    with open(diamond_file, "r", encoding="utf-8") as f:
        data = json.load(f)

    print(f"\nRun ID: {data['run_id']}")
    print(f"Log Set: {data['log_set']}")
    print(f"Logs Analyzed: {data['logs_analyzed']}")
    print(f"Methodology: {data['methodology']}")

    print(f"\nTotal Analyses: {data['total_analyses']}")
    print(f"Successful: {data['successful_analyses']} ({100*data['successful_analyses']/data['total_analyses']:.1f}%)")

    # Analyze by provider
    by_provider = defaultdict(lambda: {"success": 0, "fail": 0})
    by_log = defaultdict(lambda: {"success": 0, "fail": 0, "interpretations": []})

    for result in data.get("results", []):
        provider = result.get("provider", "unknown")
        log_source = result.get("log_source", "unknown")

        if result.get("success"):
            by_provider[provider]["success"] += 1
            by_log[log_source]["success"] += 1
            if result.get("response"):
                by_log[log_source]["interpretations"].append({
                    "ship": result.get("ship_name"),
                    "text": result["response"][:300]
                })
        else:
            by_provider[provider]["fail"] += 1
            by_log[log_source]["fail"] += 1

    print("\n--- BY PROVIDER ---")
    for provider, counts in sorted(by_provider.items()):
        total = counts["success"] + counts["fail"]
        rate = 100 * counts["success"] / total if total > 0 else 0
        status = "OK" if rate > 50 else "FAILED"
        print(f"  {provider:12s}: {counts['success']:3d}/{total:3d} ({rate:5.1f}%) [{status}]")

    print("\n--- BY LOG ANALYZED ---")
    for log_src, counts in sorted(by_log.items()):
        total = counts["success"] + counts["fail"]
        rate = 100 * counts["success"] / total if total > 0 else 0
        print(f"  {log_src}: {counts['success']}/{total} interpretations ({rate:.1f}%)")

    # Sample cross-model interpretations
    print("\n--- SAMPLE INTERPRETATIONS (Cross-Model Analysis) ---")
    for log_src, counts in sorted(by_log.items()):
        if counts["interpretations"]:
            print(f"\n[{log_src}] - {len(counts['interpretations'])} models analyzed this log:")
            for interp in counts["interpretations"][:2]:
                print(f"\n  {interp['ship']}:")
                print(f"    {interp['text'][:250]}...")

    return data


def main():
    print("\n" + "=" * 60)
    print("CLOUD CLAUDE EXPERIMENT ANALYSIS")
    print("December 31, 2024")
    print("=" * 60)

    gold_data = analyze_gold_rush()
    diamond_data = analyze_diamond_rush()

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    print("""
Cloud Claude successfully ran both experiments:

GOLD RUSH (Self-Assessment Mining):
- 7 question sets × 14 ships × 3 iterations = 294 calls
- 210 successful (71.4%)
- Gemini failed (SSL/403 in cloud env)
- Together, OpenAI, xAI all working

DIAMOND RUSH (Cross-Model Interpretation):
- 3 curated logs × 14 ships × 3 iterations = 81 analyses
- 51 successful (63%)
- Same provider pattern (Gemini down)

KEY INSIGHT: This is THEORY OF MIND data!
- Gold Rush: "What do YOU think?" (first-person)
- Diamond Rush: "What do you see in THIS conversation?" (third-person)

The Diamond Rush data shows how different models INTERPRET
the same identity crisis event - a unique angle we haven't
fully analyzed before.

Next steps:
1. Extract embeddings from responses
2. Calculate inter-model agreement on interpretations
3. Look for "theory of mind" patterns in how models
   describe other models' identity events
""")


if __name__ == "__main__":
    main()
