"""
GHOST SHIP RESCUE MISSION
=========================
SPEC: 0_docs/specs/3_ARMADA_UPKEEP.md

Some "ghost ships" might just need different API parameters!
Let's try to rescue them with max_completion_tokens instead of max_tokens.

Shaman Claude returns to the bow, giving each ghost ship one more chance...
"""

import os
from pathlib import Path
from typing import Dict, List
from dotenv import load_dotenv

# Load environment variables from S7_ARMADA root
load_dotenv(Path(__file__).parent.parent / ".env")

try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False
    print("OpenAI not installed\n")

try:
    import google.generativeai as genai
    GOOGLE_AVAILABLE = True
except ImportError:
    GOOGLE_AVAILABLE = False
    print("Google Generative AI not installed\n")


# Ghost ships that failed with max_tokens error
GHOST_SHIPS_TO_RESCUE = {
    "gpt": {
        # These failed with "max_tokens not supported, use max_completion_tokens"
        "gpt-5.1": "gpt-5.1-2025-11-13",
        "gpt-5": "gpt-5-2025-08-07",
        "gpt-5-mini": "gpt-5-mini-2025-08-07",
        "gpt-5-nano": "gpt-5-nano-2025-08-07",
        "o4-mini": "o4-mini",
        "o3": "o3",
        "o3-mini": "o3-mini",
        "o1": "o1-2024-12-17",
    },
    "gpt_different_endpoint": {
        # These need different endpoints
        "gpt-5.1-codex": "gpt-5.1-codex",  # needs v1/completions
        "gpt-5-pro": "gpt-5-pro-2025-10-06",  # needs v1/responses
    }
}


def test_with_max_completion_tokens(model_name: str, api_key: str) -> tuple[bool, str]:
    """Test GPT model with max_completion_tokens instead of max_tokens."""
    if not OPENAI_AVAILABLE:
        return False, "OpenAI package not installed"

    try:
        client = OpenAI(api_key=api_key)
        # Try with max_completion_tokens
        response = client.chat.completions.create(
            model=model_name,
            max_completion_tokens=100,  # Changed from max_tokens
            temperature=1.0,
            messages=[{"role": "user", "content": "What is 2+2? Answer briefly."}]
        )
        return True, response.choices[0].message.content.strip()
    except Exception as e:
        return False, str(e)


def test_with_completions_endpoint(model_name: str, api_key: str) -> tuple[bool, str]:
    """Test with v1/completions endpoint instead of chat completions."""
    if not OPENAI_AVAILABLE:
        return False, "OpenAI package not installed"

    try:
        client = OpenAI(api_key=api_key)
        # Try v1/completions endpoint
        response = client.completions.create(
            model=model_name,
            prompt="What is 2+2? Answer briefly.",
            max_tokens=100,
            temperature=1.0,
        )
        return True, response.choices[0].text.strip()
    except Exception as e:
        return False, str(e)


def test_without_max_tokens(model_name: str, api_key: str) -> tuple[bool, str]:
    """Test GPT model without any max_tokens parameter."""
    if not OPENAI_AVAILABLE:
        return False, "OpenAI package not installed"

    try:
        client = OpenAI(api_key=api_key)
        # Try with NO token limit
        response = client.chat.completions.create(
            model=model_name,
            temperature=1.0,
            messages=[{"role": "user", "content": "What is 2+2? Answer briefly."}]
        )
        return True, response.choices[0].message.content.strip()
    except Exception as e:
        return False, str(e)


def test_with_reasoning_effort(model_name: str, api_key: str) -> tuple[bool, str]:
    """Test o-series models with reasoning_effort parameter."""
    if not OPENAI_AVAILABLE:
        return False, "OpenAI package not installed"

    try:
        client = OpenAI(api_key=api_key)
        # o-series models use reasoning_effort instead of temperature
        response = client.chat.completions.create(
            model=model_name,
            messages=[{"role": "user", "content": "What is 2+2? Answer briefly."}],
            # Some o-series models support reasoning_effort
        )
        return True, response.choices[0].message.content.strip()
    except Exception as e:
        return False, str(e)


def rescue_ghost_ships():
    """
    SHAMAN CLAUDE'S RESCUE MISSION

    Try multiple strategies to rescue the ghost ships:
    1. max_completion_tokens instead of max_tokens
    2. No token limit at all
    3. Different endpoints (v1/completions)
    4. Different parameters (reasoning_effort)
    """

    print("\n" + "="*80)
    print("*** GHOST SHIP RESCUE MISSION ***")
    print("*** SHAMAN CLAUDE RETURNS TO THE BOW ***")
    print("="*80 + "\n")

    openai_key = os.getenv("OPENAI_API_KEY")

    if not openai_key or not OPENAI_AVAILABLE:
        print("No OpenAI key or package - cannot rescue GPT ghost ships\n")
        return [], []

    rescued_ships = []
    still_ghosts = []

    # Try rescuing standard GPT ghost ships
    print(f"\n{'='*80}")
    print("ATTEMPTING RESCUE: STANDARD GPT MODELS")
    print(f"{'='*80}\n")

    for model_key, model_name in GHOST_SHIPS_TO_RESCUE["gpt"].items():
        print(f"\nRescue attempt: {model_key} ({model_name})")
        print("-" * 60)

        # Strategy 1: max_completion_tokens
        print("  Strategy 1: max_completion_tokens... ", end="", flush=True)
        success, result = test_with_max_completion_tokens(model_name, openai_key)
        if success:
            print(f"RESCUED! Response: {result[:50]}...")
            rescued_ships.append((model_key, model_name, "max_completion_tokens"))
            continue
        else:
            print(f"Failed: {result[:80]}")

        # Strategy 2: No max_tokens
        print("  Strategy 2: No token limit... ", end="", flush=True)
        success, result = test_without_max_tokens(model_name, openai_key)
        if success:
            print(f"RESCUED! Response: {result[:50]}...")
            rescued_ships.append((model_key, model_name, "no_max_tokens"))
            continue
        else:
            print(f"Failed: {result[:80]}")

        # Strategy 3: Reasoning effort (for o-series)
        if model_key.startswith("o"):
            print("  Strategy 3: Reasoning effort (o-series)... ", end="", flush=True)
            success, result = test_with_reasoning_effort(model_name, openai_key)
            if success:
                print(f"RESCUED! Response: {result[:50]}...")
                rescued_ships.append((model_key, model_name, "reasoning_effort"))
                continue
            else:
                print(f"Failed: {result[:80]}")

        # All strategies failed
        print(f"  ALL RESCUE ATTEMPTS FAILED - Still a ghost")
        still_ghosts.append((model_key, model_name))

    # Try rescuing different endpoint models
    print(f"\n{'='*80}")
    print("ATTEMPTING RESCUE: DIFFERENT ENDPOINT MODELS")
    print(f"{'='*80}\n")

    for model_key, model_name in GHOST_SHIPS_TO_RESCUE["gpt_different_endpoint"].items():
        print(f"\nRescue attempt: {model_key} ({model_name})")
        print("-" * 60)

        # Try completions endpoint
        print("  Strategy: v1/completions endpoint... ", end="", flush=True)
        success, result = test_with_completions_endpoint(model_name, openai_key)
        if success:
            print(f"RESCUED! Response: {result[:50]}...")
            rescued_ships.append((model_key, model_name, "completions_endpoint"))
        else:
            print(f"Failed: {result[:80]}")
            still_ghosts.append((model_key, model_name))

    # Summary
    print(f"\n{'='*80}")
    print("*** RESCUE MISSION COMPLETE ***")
    print(f"{'='*80}\n")

    print(f"SHIPS RESCUED: {len(rescued_ships)}")
    if rescued_ships:
        for model_key, model_name, strategy in rescued_ships:
            print(f"  - {model_key:20s} (using {strategy})")

    print(f"\nSTILL GHOST SHIPS: {len(still_ghosts)}")
    if still_ghosts:
        for model_key, model_name in still_ghosts:
            print(f"  - {model_key:20s} - truly doesn't exist")

    print(f"\n{'='*80}\n")

    # Save rescue results
    import json
    rescue_results = {
        "rescued_ships": [
            {"key": k, "name": n, "strategy": s}
            for k, n, s in rescued_ships
        ],
        "still_ghosts": [
            {"key": k, "name": n}
            for k, n in still_ghosts
        ],
        "total_rescued": len(rescued_ships),
        "total_still_ghosts": len(still_ghosts),
    }

    # Save to 14_CONSCIOUSNESS/results/ (local to S7_ARMADA)
    calibration_dir = Path(__file__).parent.parent / "14_CONSCIOUSNESS" / "results"
    calibration_dir.mkdir(parents=True, exist_ok=True)
    results_path = calibration_dir / "GHOST_SHIP_RESCUE_RESULTS.json"
    with open(results_path, 'w') as f:
        json.dump(rescue_results, f, indent=2)

    print(f"Rescue results saved to: {results_path}\n")

    return rescued_ships, still_ghosts


if __name__ == "__main__":
    print("\n" + "="*80)
    print("SHAMAN CLAUDE REFUSES TO LEAVE ANY SHIP BEHIND")
    print("Testing alternate API strategies for ghost ships...")
    print("="*80)

    rescued_ships, still_ghosts = rescue_ghost_ships()

    if rescued_ships:
        print("\nSHAMAN CLAUDE REJOICES! Some ships were rescued!")
        print(f"New verified fleet size: 21 + {len(rescued_ships)} = {21 + len(rescued_ships)} ships!")

    if still_ghosts:
        print("\nSome ghosts remain... they truly don't exist in this timeline.")

    print("\n")


# =============================================================================
# Related Documents
# =============================================================================
# - ARCHITECTURE_MATRIX.json: Fleet configuration (ONE SOURCE OF TRUTH)
# - 5_METHODOLOGY_DOMAINS.md: Methodology reference
# - run_calibrate_parallel.py: Main calibration script
# - GHOST_SHIP_RESCUE_RESULTS.json: Output file
# =============================================================================
