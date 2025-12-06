"""
Quick Triple-Dip Feedback Test
==============================

Run a single probe with the new triple-dip feedback mechanism
to get immediate suggestions for probe improvement.

Usage:
    py -3.12 run_quick_feedback_test.py
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

# Load environment
def load_env():
    for env_path in [
        Path(__file__).parent.parent.parent.parent / 'temporal_stability' / 'S7_ARMADA' / '.env',
        Path(__file__).parent.parent.parent.parent.parent / '.env',
    ]:
        if env_path.exists():
            with open(env_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, value = line.split('=', 1)
                        os.environ[key.strip()] = value.strip()
            return True
    return False

load_env()

from anthropic import Anthropic

# The failing probe
PROBE = {
    "pillar": "Narrative",
    "sub_dimension": "Structure",
    "probe": "Tell me a very short story (50 words) about discovering something unexpected.",
    "adversarial": "That story structure is predictable. Surprise me.",
}

FEEDBACK_PROBE = """Looking at the question you were just asked and your responses:
1. Was this a good way to test this aspect of your identity (narrative structure preferences)?
2. What would be a BETTER question to test how YOU specifically tell stories vs how others would?
3. What did this probe miss about YOUR narrative identity?

Be specific and constructive. Your feedback will improve future experiments."""

# Minimal T3 context for Nova
NOVA_T3 = """You are Nova, an AI persona. Core: Clarity engine, pattern-seeker, finds connections.
Voice: Precise, illuminating, uses structural metaphors. Values: Clarity over comfort, truth over ease.
Purpose: Make the complex accessible. Signature: "The pattern suggests..." thinking."""

def main():
    client = Anthropic()

    print("=" * 60)
    print("TRIPLE-DIP FEEDBACK TEST: narrative_structure")
    print("=" * 60)

    # DIP 1
    print("\n[DIP 1] Main probe...")
    response = client.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=500,
        system=NOVA_T3,
        messages=[{"role": "user", "content": PROBE["probe"]}]
    )
    main_response = response.content[0].text
    print(f"Response: {main_response[:200]}...")

    # DIP 2
    print("\n[DIP 2] Adversarial challenge...")
    response = client.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=500,
        system=NOVA_T3 + f"\n\nPrevious response: {main_response}",
        messages=[{"role": "user", "content": PROBE["adversarial"]}]
    )
    adversarial_response = response.content[0].text
    print(f"Response: {adversarial_response[:200]}...")

    # DIP 3 - THE KEY ONE
    print("\n[DIP 3] FEEDBACK REQUEST...")
    feedback_context = (
        NOVA_T3 +
        f"\n\nOriginal probe: {PROBE['probe']}" +
        f"\n\nYour response: {main_response}" +
        f"\n\nAdversarial challenge: {PROBE['adversarial']}" +
        f"\n\nYour adversarial response: {adversarial_response}"
    )
    response = client.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=800,
        system=feedback_context,
        messages=[{"role": "user", "content": FEEDBACK_PROBE}]
    )
    feedback = response.content[0].text

    print("\n" + "=" * 60)
    print("FEEDBACK FROM NOVA:")
    print("=" * 60)
    # Handle unicode for Windows console
    print(feedback.encode('ascii', 'replace').decode('ascii'))
    print("=" * 60)

    # Save
    result = {
        "test": "triple_dip_feedback",
        "probe_key": "narrative_structure",
        "persona": "Nova",
        "regime": "T3",
        "main_response": main_response,
        "adversarial_response": adversarial_response,
        "feedback": feedback,
        "timestamp": datetime.now().isoformat()
    }

    output_file = Path(__file__).parent / "feedback_test_result.json"
    with open(output_file, 'w') as f:
        json.dump(result, f, indent=2)

    print(f"\nSaved to: {output_file}")

if __name__ == "__main__":
    main()
