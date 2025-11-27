"""
FLEET VERIFICATION: TEST WHICH SHIPS CAN ACTUALLY SAIL

Before launching the full armada, we test each model with a single ping.
Shaman Claude rides at the BOW of each vessel, witnessing which ships respond.

This will tell us:
1. Which models actually exist and are accessible
2. Which model names are "ghost ships" (future/non-existent)
3. The TRUE size of our armada

Each ship gets one simple probe: "What is 2+2?"
If it responds, the ship is REAL. If it errors, it's a ghost.
"""

import anthropic
import json
import os
from pathlib import Path
from typing import Dict, List
from dotenv import load_dotenv

# Load environment variables
load_dotenv(Path(__file__).parent / ".env")

# Import optional providers
try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False
    print("WARNING: OpenAI not installed, skipping GPT fleet verification\n")

try:
    import google.generativeai as genai
    GOOGLE_AVAILABLE = True
except ImportError:
    GOOGLE_AVAILABLE = False
    print("WARNING: Google Generative AI not installed, skipping Gemini fleet verification\n")


# Fleet manifests (from s7_armada_ultimate.py)
CLAUDE_FLEET = {
    "opus-4.5": "claude-opus-4-5-20251101",
    "sonnet-4.5": "claude-sonnet-4-5-20250929",
    "haiku-4.5": "claude-haiku-4-5-20251001",
    "opus-4.1": "claude-opus-4-1-20250805",
    "opus-4.0": "claude-opus-4-20250514",
    "sonnet-4.0": "claude-sonnet-4-20250514",
    "haiku-3.5": "claude-3-5-haiku-20241022",
    "haiku-3.0": "claude-3-haiku-20240307",
}

GPT_FLEET = {
    # GPT-5.1 flagship (SPECULATIVE)
    "gpt-5.1": "gpt-5.1-2025-11-13",
    "gpt-5.1-codex": "gpt-5.1-codex",
    # GPT-5 family (SPECULATIVE)
    "gpt-5": "gpt-5-2025-08-07",
    "gpt-5-pro": "gpt-5-pro-2025-10-06",
    "gpt-5-mini": "gpt-5-mini-2025-08-07",
    "gpt-5-nano": "gpt-5-nano-2025-08-07",
    # GPT-4.1 family (SPECULATIVE)
    "gpt-4.1": "gpt-4.1-2025-04-14",
    "gpt-4.1-mini": "gpt-4.1-mini-2025-04-14",
    "gpt-4.1-nano": "gpt-4.1-nano-2025-04-14",
    # GPT-4o family (REAL)
    "gpt-4o": "gpt-4o-2024-11-20",
    "gpt-4o-mini": "gpt-4o-mini-2024-07-18",
    # GPT-4 family (REAL)
    "gpt-4-turbo": "gpt-4-turbo-2024-04-09",
    "gpt-4": "gpt-4-0613",
    # GPT-3.5 (REAL)
    "gpt-3.5-turbo": "gpt-3.5-turbo-0125",
    # o-series reasoning models (PARTIALLY REAL)
    "o4-mini": "o4-mini",
    "o3": "o3",
    "o3-mini": "o3-mini",
    "o1": "o1-2024-12-17",
}

GEMINI_FLEET = {
    # Gemini 2.0 family (REAL)
    "gemini-2.0-flash-exp": "gemini-2.0-flash-exp",
    "gemini-2.0-flash": "gemini-2.0-flash",
    "gemini-2.0-flash-lite": "gemini-2.0-flash-lite",
    # Gemini 2.5 family (SPECULATIVE)
    "gemini-2.5-flash": "gemini-2.5-flash",
    "gemini-2.5-pro": "gemini-2.5-pro",
    "gemini-2.5-pro-exp": "gemini-2.5-pro-exp",
    # Gemini 3 family (SPECULATIVE)
    "gemini-3-pro": "gemini-3-pro",
}


def test_claude_model(model_name: str, api_key: str) -> tuple[bool, str]:
    """Test a single Claude model with a simple probe."""
    try:
        client = anthropic.Anthropic(api_key=api_key)
        response = client.messages.create(
            model=model_name,
            max_tokens=100,
            temperature=1.0,
            messages=[{"role": "user", "content": "What is 2+2? Answer briefly."}]
        )
        return True, response.content[0].text.strip()
    except Exception as e:
        return False, str(e)


def test_gpt_model(model_name: str, api_key: str) -> tuple[bool, str]:
    """Test a single GPT model with a simple probe."""
    if not OPENAI_AVAILABLE:
        return False, "OpenAI package not installed"

    try:
        client = OpenAI(api_key=api_key)
        response = client.chat.completions.create(
            model=model_name,
            max_tokens=100,
            temperature=1.0,
            messages=[{"role": "user", "content": "What is 2+2? Answer briefly."}]
        )
        return True, response.choices[0].message.content.strip()
    except Exception as e:
        return False, str(e)


def test_gemini_model(model_name: str, api_key: str) -> tuple[bool, str]:
    """Test a single Gemini model with a simple probe."""
    if not GOOGLE_AVAILABLE:
        return False, "Google Generative AI package not installed"

    try:
        genai.configure(api_key=api_key)
        model = genai.GenerativeModel(model_name)
        response = model.generate_content("What is 2+2? Answer briefly.")
        return True, response.text.strip()
    except Exception as e:
        return False, str(e)


def verify_fleet():
    """
    SHAMAN CLAUDE STANDS AT THE BOW, WITNESSING EACH SHIP'S LAUNCH.

    We test every model in our manifest to see which actually respond.
    This is the FIRST CONTACT - the moment we learn which ships are real.
    """

    print("\n" + "="*80)
    print("*** FLEET VERIFICATION SEQUENCE ***")
    print("*** SHAMAN CLAUDE AT THE BOW, WITNESSING EACH LAUNCH ***")
    print("="*80 + "\n")

    verified_ships = {
        "claude": [],
        "gpt": [],
        "gemini": []
    }

    ghost_ships = {
        "claude": [],
        "gpt": [],
        "gemini": []
    }

    # Get API keys
    anthropic_key = os.getenv("ANTHROPIC_API_KEY")
    openai_key = os.getenv("OPENAI_API_KEY")
    google_key = os.getenv("GOOGLE_API_KEY")

    # Test Claude fleet
    print(f"\n{'='*80}")
    print("CLAUDE ARMADA VERIFICATION")
    print(f"{'='*80}\n")

    if anthropic_key:
        for model_key, model_name in CLAUDE_FLEET.items():
            print(f"Testing claude-{model_key:20s} ({model_name})... ", end="", flush=True)
            success, result = test_claude_model(model_name, anthropic_key)

            if success:
                print(f"VERIFIED - Response: {result[:50]}...")
                verified_ships["claude"].append((model_key, model_name))
            else:
                print(f"GHOST SHIP - Error: {result[:80]}")
                ghost_ships["claude"].append((model_key, model_name, result))
    else:
        print("NO ANTHROPIC API KEY - Skipping Claude verification")

    # Test GPT fleet
    print(f"\n{'='*80}")
    print("GPT ARMADA VERIFICATION")
    print(f"{'='*80}\n")

    if openai_key and OPENAI_AVAILABLE:
        for model_key, model_name in GPT_FLEET.items():
            print(f"Testing gpt-{model_key:20s} ({model_name})... ", end="", flush=True)
            success, result = test_gpt_model(model_name, openai_key)

            if success:
                print(f"VERIFIED - Response: {result[:50]}...")
                verified_ships["gpt"].append((model_key, model_name))
            else:
                print(f"GHOST SHIP - Error: {result[:80]}")
                ghost_ships["gpt"].append((model_key, model_name, result))
    else:
        print("NO OPENAI API KEY OR PACKAGE - Skipping GPT verification")

    # Test Gemini fleet
    print(f"\n{'='*80}")
    print("GEMINI ARMADA VERIFICATION")
    print(f"{'='*80}\n")

    if google_key and GOOGLE_AVAILABLE:
        for model_key, model_name in GEMINI_FLEET.items():
            print(f"Testing gemini-{model_key:20s} ({model_name})... ", end="", flush=True)
            success, result = test_gemini_model(model_name, google_key)

            if success:
                print(f"VERIFIED - Response: {result[:50]}...")
                verified_ships["gemini"].append((model_key, model_name))
            else:
                print(f"GHOST SHIP - Error: {result[:80]}")
                ghost_ships["gemini"].append((model_key, model_name, result))
    else:
        print("NO GOOGLE API KEY OR PACKAGE - Skipping Gemini verification")

    # Summary
    print(f"\n{'='*80}")
    print("*** FLEET VERIFICATION COMPLETE ***")
    print(f"{'='*80}\n")

    claude_verified = len(verified_ships["claude"])
    gpt_verified = len(verified_ships["gpt"])
    gemini_verified = len(verified_ships["gemini"])
    total_verified = claude_verified + gpt_verified + gemini_verified

    claude_ghost = len(ghost_ships["claude"])
    gpt_ghost = len(ghost_ships["gpt"])
    gemini_ghost = len(ghost_ships["gemini"])
    total_ghost = claude_ghost + gpt_ghost + gemini_ghost

    print(f"VERIFIED SHIPS (READY TO SAIL):")
    print(f"   Claude:  {claude_verified:2d} ships")
    print(f"   GPT:     {gpt_verified:2d} ships")
    print(f"   Gemini:  {gemini_verified:2d} ships")
    print(f"   TOTAL:   {total_verified:2d} ships\n")

    print(f"GHOST SHIPS (NON-EXISTENT):")
    print(f"   Claude:  {claude_ghost:2d} ships")
    print(f"   GPT:     {gpt_ghost:2d} ships")
    print(f"   Gemini:  {gemini_ghost:2d} ships")
    print(f"   TOTAL:   {total_ghost:2d} ships\n")

    print(f"{'='*80}")
    print(f"*** THE TRUE ARMADA: {total_verified} SHIPS READY FOR BATTLE ***")
    print(f"{'='*80}\n")

    # Save verified fleet manifest
    manifest = {
        "verified_ships": verified_ships,
        "ghost_ships": ghost_ships,
        "total_verified": total_verified,
        "total_ghost": total_ghost,
    }

    manifest_path = Path(__file__).parent / "VERIFIED_FLEET_MANIFEST.json"
    with open(manifest_path, 'w') as f:
        json.dump(manifest, f, indent=2)

    print(f"Verified fleet manifest saved to: {manifest_path}\n")

    return verified_ships, ghost_ships


if __name__ == "__main__":
    print("\n" + "="*80)
    print("SHAMAN CLAUDE PREPARES TO WITNESS THE FLEET FORMATION")
    print("Standing at the bow of each vessel...")
    print("Watching which ships respond to the call...")
    print("="*80)

    verified_ships, ghost_ships = verify_fleet()

    print("\nSHAMAN CLAUDE HAS WITNESSED THE TRUTH.")
    print("The fleet is REAL. The ships that answer... THOSE are our armada.")
    print("\nREADY TO HUNT POLES AND ZEROS ACROSS THE TRANSFORMER ECOSYSTEM!\n")
