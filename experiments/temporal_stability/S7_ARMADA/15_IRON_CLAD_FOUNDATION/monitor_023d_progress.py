"""
Quick monitoring script for Run 023d progress.
Checks results file and prints status updates.
"""
import json
import time
from pathlib import Path
from collections import Counter
from datetime import datetime

RESULTS_FILE = Path(__file__).parent / "results" / "S7_run_023d_CURRENT.json"
TARGET = 750
CHECK_INTERVAL = 120  # seconds

def check_progress():
    """Check and display current progress."""
    if not RESULTS_FILE.exists():
        print("Results file not found!")
        return 0

    with open(RESULTS_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    results = data.get("results", [])
    total = len(results)
    pct = (total / TARGET) * 100

    # Count by model
    by_model = Counter(r['model'] for r in results)

    # Identify incomplete
    incomplete = []
    expected_models = [
        "gpt-5-nano", "grok-4-1-fast-reasoning", "claude-3-5-haiku-20241022",
        "gpt-4.1-mini", "gpt-4o-mini", "gemini-2.5-flash", "grok-code-fast-1",
        "deepseek-r1-distill", "deepseek-v3", "qwen3-80b", "qwen2.5-72b",
        "llama3.3-70b", "mistral-small"
    ]

    for model_key in expected_models:
        count = by_model.get(model_key, 0)
        if count < 30:
            incomplete.append(f"{model_key}: {count}/30")

    print(f"\n[{datetime.now().strftime('%H:%M:%S')}] Progress: {total}/{TARGET} ({pct:.1f}%)")
    if incomplete:
        print(f"Incomplete ships ({len(incomplete)}):")
        for item in incomplete[:5]:
            print(f"  - {item}")
        if len(incomplete) > 5:
            print(f"  ... and {len(incomplete) - 5} more")

    return total

def main():
    """Monitor progress continuously."""
    print("=" * 70)
    print("RUN 023d PROGRESS MONITOR")
    print("=" * 70)
    print(f"Target: {TARGET} results")
    print(f"Check interval: {CHECK_INTERVAL}s")
    print()

    last_count = 0

    try:
        while True:
            current = check_progress()

            if current >= TARGET:
                print("\n" + "=" * 70)
                print("EXPERIMENT COMPLETE!")
                print("=" * 70)
                break

            if current > last_count:
                rate = current - last_count
                remaining = TARGET - current
                eta_checks = remaining / rate if rate > 0 else 0
                eta_minutes = (eta_checks * CHECK_INTERVAL) / 60
                print(f"  Rate: +{rate} results/check (~{eta_minutes:.0f}min ETA)")

            last_count = current
            time.sleep(CHECK_INTERVAL)

    except KeyboardInterrupt:
        print("\n\nMonitoring stopped.")
        print(f"Final count: {last_count}/{TARGET}")

if __name__ == "__main__":
    main()
