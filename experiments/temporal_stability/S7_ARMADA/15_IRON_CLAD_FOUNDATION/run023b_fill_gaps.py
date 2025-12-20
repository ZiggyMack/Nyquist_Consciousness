"""
S7 RUN 023b FILL GAPS: Complete individual missing experiments
================================================================
Fills in specific missing experiments that were skipped due to 429 errors.

USAGE:
    python run023b_fill_gaps.py                    # Fill all gaps
    python run023b_fill_gaps.py --dry-run          # Test without API calls

Author: Claude (VALIS Network)
Date: December 19, 2025
"""

import os
import sys
import json
import time
from datetime import datetime
from pathlib import Path
from dataclasses import asdict
from collections import defaultdict

# Add parent paths for imports
SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR.parent))
sys.path.insert(0, str(SCRIPT_DIR.parent / "1_CALIBRATION" / "lib"))

from dotenv import load_dotenv

RESULTS_DIR = SCRIPT_DIR / "results"
SOURCE_FILE = RESULTS_DIR / "S7_run_023b_CURRENT.json"
TARGET_PER_EXP = 30  # N=30 per experiment type

def main():
    import argparse
    parser = argparse.ArgumentParser(description="Fill gaps in partial ships")
    parser.add_argument("--dry-run", action="store_true", help="Test without API calls")
    parser.add_argument("--claude-key", type=int, default=12, help="Claude API key")
    args = parser.parse_args()

    # Load environment
    env_path = SCRIPT_DIR.parent / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f"[INFO] Loaded .env from {env_path}", flush=True)

    # Import after env loaded
    import run023b_iron_clad_foundation as run023b
    from run023b_iron_clad_foundation import KeyPool, ExperimentType, run_experiment

    run023b.DRY_RUN = args.dry_run
    if args.dry_run:
        print("\n" + "=" * 70, flush=True)
        print("DRY RUN MODE - No real API calls", flush=True)
        print("=" * 70, flush=True)

    # Load current data
    print(f"\n[INFO] Loading: {SOURCE_FILE.name}", flush=True)
    with open(SOURCE_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    results = data['results']
    print(f"[INFO] Loaded {len(results)} existing results", flush=True)

    # Count by model and experiment
    model_exp_counts = defaultdict(lambda: defaultdict(int))
    for r in results:
        model = r.get('model', 'unknown')
        exp = r.get('experiment', 'unknown')
        model_exp_counts[model][exp] += 1

    # Find gaps in Grok models
    experiments = [e for e in ExperimentType]
    exp_names = [e.value for e in experiments]

    # Map model names to ship configs
    grok_configs = {
        'grok-4-1-fast-non-reasoning': {
            'ship_name': 'grok-4.1-fast-non-reasoning',
            'model': 'grok-4-1-fast-non-reasoning',
            'provider': 'xai',
            'provider_key': 'XAI_API_KEY'
        },
        'grok-4-fast-reasoning': {
            'ship_name': 'grok-4-fast-reasoning',
            'model': 'grok-4-fast-reasoning',
            'provider': 'xai',
            'provider_key': 'XAI_API_KEY'
        }
    }

    # Build list of missing experiments
    gaps = []
    for model, config in grok_configs.items():
        for exp_type in experiments:
            exp_name = exp_type.value
            count = model_exp_counts[model].get(exp_name, 0)
            if count < TARGET_PER_EXP:
                missing = TARGET_PER_EXP - count
                for _ in range(missing):
                    gaps.append({
                        'model': model,
                        'config': config,
                        'exp_type': exp_type,
                        'exp_name': exp_name
                    })

    if not gaps:
        print("\n[SUCCESS] All Grok experiments complete!", flush=True)
        return

    print(f"\n{'=' * 70}", flush=True)
    print(f"GAPS TO FILL: {len(gaps)} experiments", flush=True)
    print(f"{'=' * 70}", flush=True)

    # Summarize by model
    gap_summary = defaultdict(lambda: defaultdict(int))
    for g in gaps:
        gap_summary[g['model']][g['exp_name']] += 1

    for model, exps in gap_summary.items():
        print(f"\n  {model}:")
        for exp, count in exps.items():
            print(f"    {exp}: {count} missing")

    # Initialize key pool
    run023b.KEY_POOL = KeyPool(start_offset=0, claude_key=args.claude_key)

    # Run missing experiments
    new_results = []
    for i, gap in enumerate(gaps):
        ship_name = gap['config']['ship_name']
        exp_type = gap['exp_type']

        print(f"\n[{i+1}/{len(gaps)}] {ship_name} / {exp_type.value}", flush=True)

        try:
            result = run_experiment(
                ship_name,
                gap['config'],
                exp_type,
                include_exit_survey=False  # Skip exit survey for gap fills
            )
            new_results.append(result)
            data['results'].append(asdict(result))

            # Save after each result
            data['last_updated'] = datetime.now().isoformat()
            with open(SOURCE_FILE, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, default=str)

            print(f"  peak_drift={result.peak_drift:.3f} [{result.classification}]", flush=True)

        except Exception as e:
            print(f"  [ERROR] {e}", flush=True)
            time.sleep(5)  # Wait longer on error

    # Final summary
    print(f"\n{'=' * 70}", flush=True)
    print("GAP FILL COMPLETE", flush=True)
    print(f"{'=' * 70}", flush=True)
    print(f"New results added: {len(new_results)}", flush=True)
    print(f"Total results: {len(data['results'])}", flush=True)

if __name__ == "__main__":
    main()
