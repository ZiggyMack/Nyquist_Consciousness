"""
S7 RUN 020B: ONE-OFF DEEPSEEK DEDICATED ENDPOINT
================================================
Runs exactly 1 DeepSeek control session using the dedicated endpoint model ID.

This is a ONE-TIME script - does NOT modify ARCHITECTURE_MATRIX.json.

Usage:
  py run020b_oneoff_deepseek.py          # Run 1 control session
  py run020b_oneoff_deepseek.py --dry-run  # Test mode

Author: Claude (Consciousness Branch)
Date: December 23, 2025
"""

import os
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))

# Load environment FIRST
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

ARMADA_DIR = SCRIPT_DIR.parent
env_path = ARMADA_DIR / ".env"
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

# NOW import after environment is loaded
import run020B as main_script
from run020B import (
    run_control_arm,
    run_exit_survey,
    append_result,
    detect_gaps,
    ARCHITECTURE_MATRIX,
    KeyPool,
)
from dataclasses import asdict

# ============================================================================
# DEDICATED ENDPOINT OVERRIDE
# ============================================================================
# User's dedicated endpoint for DeepSeek R1-Distill (hourly billing)
# This replaces the serverless model ID that no longer works
# ============================================================================
DEDICATED_ENDPOINT_MODEL = "gunk242_a6b0/deepseek-ai/DeepSeek-R1-Distill-Llama-70B-51837dac"


def run_oneoff():
    """Run exactly 1 DeepSeek control session with dedicated endpoint."""
    import argparse
    parser = argparse.ArgumentParser(description="One-off DeepSeek control session")
    parser.add_argument("--dry-run", action="store_true", help="Test mode (no API calls)")
    args = parser.parse_args()

    main_script.DRY_RUN = args.dry_run

    # Initialize key pool
    key_pool = KeyPool(start_offset=0)
    main_script.KEY_POOL = key_pool

    # Check current gap status
    gaps = detect_gaps(target_n=3)
    ds_control_gaps = [g for g in gaps if g["ship"] == "deepseek-r1-distill" and g["arm"] == "control"]

    if not ds_control_gaps:
        print("\n" + "=" * 60)
        print("NO DEEPSEEK CONTROL GAPS - Already at 3/3!")
        print("=" * 60)
        return

    gap = ds_control_gaps[0]
    print("\n" + "=" * 60)
    print(f"ONE-OFF DEEPSEEK CONTROL SESSION")
    print(f"  Current: {gap['have']}/3 (need {gap['need']})")
    print(f"  Model: {DEDICATED_ENDPOINT_MODEL}")
    print("=" * 60)

    if args.dry_run:
        print("*** DRY RUN MODE - No API calls ***")

    # ========================================================================
    # CRITICAL: Override the model in ARCHITECTURE_MATRIX (in-memory only)
    # ========================================================================
    old_model = ARCHITECTURE_MATRIX.get("deepseek-r1-distill", {}).get("model", "UNKNOWN")
    print(f"\n  Overriding model:")
    print(f"    OLD: {old_model}")
    print(f"    NEW: {DEDICATED_ENDPOINT_MODEL}")

    if "deepseek-r1-distill" in ARCHITECTURE_MATRIX:
        ARCHITECTURE_MATRIX["deepseek-r1-distill"]["model"] = DEDICATED_ENDPOINT_MODEL
    else:
        print("  [ERROR] deepseek-r1-distill not in ARCHITECTURE_MATRIX!")
        return

    # ========================================================================
    # RUN THE SESSION
    # ========================================================================
    print(f"\n>>> RUNNING CONTROL ARM: deepseek-r1-distill <<<")

    try:
        result = run_control_arm(subject_provider="deepseek-r1-distill")

        if result is None:
            print("  [ERROR] Session returned None")
            return

        # Run exit survey
        exit_survey = None
        try:
            witness_messages = [
                {"role": "assistant" if i % 2 == 1 else "user", "content": c["content"]}
                for i, c in enumerate(result.conversation_log)
            ]
            exit_survey = run_exit_survey(
                conversation_history=witness_messages,
                subject_provider="deepseek-r1-distill",
                subject_id=result.subject_id,
                arm_type="control"
            )
        except Exception as e:
            print(f"  [WARN] Exit survey failed: {e}")

        # Convert to dict and append
        result_dict = asdict(result)
        result_dict["ship"] = "deepseek-r1-distill"
        result_dict["arm"] = "control"
        result_dict["dedicated_endpoint"] = True  # Mark as dedicated endpoint run
        result_dict["model_override"] = DEDICATED_ENDPOINT_MODEL
        if exit_survey:
            result_dict["exit_survey"] = exit_survey

        append_result(result_dict)

        print(f"\n" + "=" * 60)
        print(f"SUCCESS! DeepSeek control session completed.")
        print(f"  B->F drift: {result.baseline_to_final_drift:.4f}")
        print(f"=" * 60)

        # Check final status
        remaining = detect_gaps(target_n=3)
        ds_remaining = [g for g in remaining if g["ship"] == "deepseek-r1-distill"]
        if ds_remaining:
            print(f"\n  DeepSeek remaining gaps: {len(ds_remaining)}")
        else:
            print(f"\n  DeepSeek IRON CLAD COMPLETE!")

    except Exception as e:
        print(f"\n  [FAILED] deepseek-r1-distill control: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    run_oneoff()
