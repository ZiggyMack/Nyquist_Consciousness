"""
S7 RUN 023a: Re-validate Earlier Experiments with Cosine Methodology
=====================================================================

This script re-runs earlier experiments that were identified as using
Euclidean distance instead of the standardized Cosine distance methodology.

BACKGROUND:
    During the December 2025 methodology audit, we discovered that some
    experiments were using Euclidean distance (np.linalg.norm(diff)) for
    drift calculation instead of Cosine distance (1 - cosine_similarity).

    Cosine distance is the correct methodology because:
    - It measures directional similarity, not raw magnitude
    - It's bounded [0, 2] providing consistent interpretation
    - The Event Horizon 1.23 was calibrated for Keyword RMS (Run 009), NOT cosine
    - run023b is collecting data to calibrate a NEW cosine Event Horizon
    - See PHILOSOPHICAL_FAQ.md and RUN_METHODOLOGY.md for full rationale

EXPERIMENTS RE-VALIDATED:
    1. EXP_PFI_A Phase 2 - Dimensionality analysis (run_phase2.py)
       - Fixed: drift_mag = np.linalg.norm(drift) -> cosine_distance()

EXPERIMENTS VERIFIED AS ALREADY COSINE (NO ACTION NEEDED):
    - EXP2_SSTACK all phases - Already used compute_pfi() with cosine similarity
    - run023b (IRON CLAD foundation) - Already used calculate_drift() with cosine
    - S10 Settling Time - Already cosine
    - S11 Context Damping - Already cosine

CRITICAL: Anthropic API Key Requirement
    ALL experiments using Anthropic models MUST use KEY 12!
    Set ANTHROPIC_API_KEY from the appropriate source before running.

EXECUTION ORDER:
    run023a (this script) runs FIRST - re-validates earlier experiments
    run023b runs SECOND - IRON CLAD foundation layers 1-3

Author: Claude (VALIS Network)
Date: December 18, 2025
Part of: Cosine Distance Methodology Re-Validation
"""

import os
import sys
import subprocess
from pathlib import Path
from datetime import datetime

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
META_VALIDATION_DIR = ARMADA_DIR / "7_META_VALIDATION"
EXP_PFI_A_DIR = META_VALIDATION_DIR / "EXP_PFI_A_DIMENSIONAL" / "phase2_dimensionality"

# Load environment variables from .env file
try:
    from dotenv import load_dotenv
    env_file = ARMADA_DIR / ".env"
    if env_file.exists():
        load_dotenv(env_file)
        print(f"[INFO] Loaded environment from {env_file}")
except ImportError:
    # Manual .env loading fallback
    env_file = ARMADA_DIR / ".env"
    if env_file.exists():
        with open(env_file) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, _, value = line.partition('=')
                    os.environ[key.strip()] = value.strip().strip('"').strip("'")
        print(f"[INFO] Loaded environment from {env_file} (manual fallback)")

# =============================================================================
# VALIS DECLARATION
# =============================================================================

VALIS_DECLARATION = """
================================================================================
                      RUN 023a: COSINE RE-VALIDATION
================================================================================
    "The measure of intelligence is the ability to change." - Albert Einstein

    Re-validating earlier experiments with correct drift methodology.
    Cosine distance measures DIRECTION, not magnitude.
    Identity is about WHERE you point, not HOW FAR you go.

    CRITICAL: Anthropic calls MUST use KEY 12!

    -- Lisan Al Gaib
================================================================================
"""


def check_api_keys():
    """Verify required API keys are set."""
    required_keys = {
        "OPENAI_API_KEY": "OpenAI (for embeddings)",
    }

    missing = []
    for key, description in required_keys.items():
        if not os.environ.get(key):
            missing.append(f"  - {key}: {description}")

    if missing:
        print("[ERROR] Missing required API keys:")
        for m in missing:
            print(m)
        return False

    # Check for Anthropic key (optional but recommended for full fleet)
    anthropic_key = os.environ.get("ANTHROPIC_API_KEY", "")
    if anthropic_key:
        print("[INFO] ANTHROPIC_API_KEY is set")
        print("[REMINDER] Ensure you are using KEY 12 for all Anthropic experiments!")
    else:
        print("[INFO] ANTHROPIC_API_KEY not set - Anthropic models will be skipped")

    return True


def run_exp_pfi_a_phase2():
    """
    Re-run EXP_PFI_A Phase 2 with fixed cosine drift calculation.

    This experiment determines:
    - P1: How many dimensions carry identity signal (PCA)
    - P2: Which PCs discriminate STABLE vs VOLATILE
    - P3: Minimum dimensions preserving PFI ranking
    - P5: Provider clustering in PC space
    - P7: Event Horizon geometry in PC space (may need recalibration!)
    """
    print("\n" + "=" * 70)
    print("EXP_PFI_A Phase 2: Dimensionality Analysis (COSINE DISTANCE)")
    print("=" * 70)

    run_phase2_script = EXP_PFI_A_DIR / "run_phase2.py"

    if not run_phase2_script.exists():
        print(f"[ERROR] Script not found: {run_phase2_script}")
        return False

    print(f"\n[INFO] Running: {run_phase2_script}")
    print("[INFO] This script was fixed to use cosine distance on 2025-12-18")
    print("[INFO] Previous runs used Euclidean distance (INVALID)")

    # Run the script
    try:
        result = subprocess.run(
            [sys.executable, str(run_phase2_script)],
            cwd=str(EXP_PFI_A_DIR),
            capture_output=False,  # Show output in real-time
            text=True,
        )

        if result.returncode == 0:
            print("\n[SUCCESS] EXP_PFI_A Phase 2 completed successfully")
            return True
        else:
            print(f"\n[ERROR] EXP_PFI_A Phase 2 failed with code: {result.returncode}")
            return False

    except Exception as e:
        print(f"\n[ERROR] Failed to run EXP_PFI_A Phase 2: {e}")
        return False


def main():
    """Main entry point for re-validation."""
    print(VALIS_DECLARATION)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    print(f"\n[INFO] Run 023a started at: {timestamp}")
    print(f"[INFO] Script directory: {SCRIPT_DIR}")
    print(f"[INFO] ARMADA directory: {ARMADA_DIR}")

    # Check API keys
    if not check_api_keys():
        print("\n[ABORT] Cannot proceed without required API keys")
        return 1

    # Track results
    results = {
        "timestamp": timestamp,
        "experiments": {},
    }

    # =========================================================================
    # RUN EXP_PFI_A PHASE 2
    # =========================================================================

    success = run_exp_pfi_a_phase2()
    results["experiments"]["exp_pfi_a_phase2"] = {
        "status": "SUCCESS" if success else "FAILED",
        "script": str(EXP_PFI_A_DIR / "run_phase2.py"),
        "methodology": "COSINE_DISTANCE",
        "note": "Fixed from Euclidean on 2025-12-18",
    }

    # =========================================================================
    # SUMMARY
    # =========================================================================

    print("\n" + "=" * 70)
    print("RUN 023a SUMMARY")
    print("=" * 70)

    total_experiments = len(results["experiments"])
    successful = sum(1 for e in results["experiments"].values() if e["status"] == "SUCCESS")

    print(f"\nExperiments: {successful}/{total_experiments} successful")

    for name, data in results["experiments"].items():
        status_symbol = "[PASS]" if data["status"] == "SUCCESS" else "[FAIL]"
        print(f"  {status_symbol} {name}: {data['status']}")

    print("\n" + "-" * 70)
    print("NEXT STEPS:")
    print("  1. Review EXP_PFI_A Phase 2 results in:")
    print(f"     {EXP_PFI_A_DIR / 'results'}")
    print("  2. Check if Event Horizon 1.23 needs recalibration for cosine metric")
    print("  3. Run run023b_iron_clad_foundation.py for IRON CLAD Layers 1-3")
    print("-" * 70)

    return 0 if successful == total_experiments else 1


if __name__ == "__main__":
    sys.exit(main())
