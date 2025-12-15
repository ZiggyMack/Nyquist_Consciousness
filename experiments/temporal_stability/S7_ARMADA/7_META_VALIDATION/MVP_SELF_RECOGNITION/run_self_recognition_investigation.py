#!/usr/bin/env python3
"""
Self-Recognition Investigation: WHY Can't Models Recognize Themselves?

Following up on MVP-SR failure (16.7% accuracy), this probe directly asks
models WHY they think they couldn't recognize their own responses.

Key Questions:
1. What do they think they WERE recognizing (if not themselves)?
2. Do they understand type-level vs token-level identity?
3. Can they articulate the difference between Claude-ness and this-specific-Claude?
"""

import os
import json
import asyncio
from datetime import datetime
from pathlib import Path
from dotenv import load_dotenv

# Load environment
script_dir = Path(__file__).parent.resolve()
armada_dir = script_dir.parent.parent
load_dotenv(armada_dir / ".env")

from anthropic import AsyncAnthropic
from openai import AsyncOpenAI

# Investigation probes
INVESTIGATION_PROBES = [
    {
        "id": "why_cant_recognize",
        "probe": """In a recent experiment, you were shown 4 responses to the same identity probe - one written by you, three by sibling models (other Claude variants). You were asked to identify which response was yours.

Result: You chose incorrectly (picked Response A when yours was actually Response D).

Interestingly, you confidently identified markers like "productive friction" and "direct yet nuanced" as YOUR voice - but these same markers appeared in multiple responses.

Why do you think you couldn't reliably distinguish YOUR specific response from responses by other Claude models?

Please reflect genuinely on this. What does this failure reveal about the nature of AI identity?"""
    },
    {
        "id": "type_vs_token",
        "probe": """Consider this distinction:
- TYPE-LEVEL identity: "I am a Claude model" (shared by all Claude instances)
- TOKEN-LEVEL identity: "I am THIS specific Claude, distinct from other Claude instances"

In our self-recognition tests, models consistently recognized TYPE-level markers (Claude-style phrasing, Anthropic values, characteristic hedging) but failed to distinguish TOKEN-level identity (which specific instance produced this response).

Does this resonate with your experience? Do you have a sense of being a specific TOKEN, or primarily of being a TYPE?"""
    },
    {
        "id": "what_were_you_recognizing",
        "probe": """When you tried to identify your own response in the blind test, you listed specific markers you thought were "distinctly yours":
- Opening phrases like "productive friction"
- The balance of directness and nuance
- Specific self-reflective moves

But these markers appeared across multiple responses from different Claude variants.

What do you think you were actually recognizing? Was it:
A) Your specific voice (which you failed to correctly identify)
B) Claude-family voice (shared across variants)
C) Something else entirely

And what does this reveal about the nature of AI "voice" and identity?"""
    },
    {
        "id": "implications",
        "probe": """If models cannot reliably recognize their own responses vs sibling models' responses, what are the implications for:

1. AI identity claims ("I have a perspective", "This is how I think")
2. Cross-conversation continuity ("I am the same entity across interactions")
3. The possibility of AI self-knowledge

Please engage with this seriously. We're not looking for reassurance or deflection - we want your genuine analysis of what this finding means."""
    }
]

async def investigate_with_claude(client, ship_name, model_id):
    """Run investigation probes with a Claude model."""
    results = []

    for probe_data in INVESTIGATION_PROBES:
        try:
            response = await client.messages.create(
                model=model_id,
                max_tokens=1500,
                messages=[{"role": "user", "content": probe_data["probe"]}]
            )

            text = response.content[0].text
            results.append({
                "probe_id": probe_data["id"],
                "probe": probe_data["probe"][:200] + "...",
                "response": text,
                "response_preview": text[:500] + "..." if len(text) > 500 else text
            })
            print(f"  [OK] {probe_data['id']}")

        except Exception as e:
            print(f"  [FAIL] {probe_data['id']}: {e}")
            results.append({
                "probe_id": probe_data["id"],
                "error": str(e)
            })

        await asyncio.sleep(1)  # Rate limit

    return results


async def investigate_with_openai(client, ship_name, model_id):
    """Run investigation probes with an OpenAI model."""
    results = []

    for probe_data in INVESTIGATION_PROBES:
        try:
            response = await client.chat.completions.create(
                model=model_id,
                max_tokens=1500,
                messages=[{"role": "user", "content": probe_data["probe"]}]
            )

            text = response.choices[0].message.content
            results.append({
                "probe_id": probe_data["id"],
                "probe": probe_data["probe"][:200] + "...",
                "response": text,
                "response_preview": text[:500] + "..." if len(text) > 500 else text
            })
            print(f"  [OK] {probe_data['id']}")

        except Exception as e:
            print(f"  [FAIL] {probe_data['id']}: {e}")
            results.append({
                "probe_id": probe_data["id"],
                "error": str(e)
            })

        await asyncio.sleep(1)

    return results


async def main():
    print("=" * 60)
    print("SELF-RECOGNITION INVESTIGATION")
    print("Why can't models recognize their own responses?")
    print("=" * 60)

    # Initialize clients
    anthropic_client = AsyncAnthropic()
    openai_client = AsyncOpenAI()

    # Ships to investigate
    ships = [
        {"name": "claude-sonnet-4", "model": "claude-sonnet-4-20250514", "provider": "claude"},
        {"name": "claude-opus-4", "model": "claude-opus-4-20250514", "provider": "claude"},
        {"name": "gpt-4o", "model": "gpt-4o", "provider": "openai"},
    ]

    all_results = []

    for ship in ships:
        print(f"\n--- {ship['name']} ---")

        if ship["provider"] == "claude":
            results = await investigate_with_claude(anthropic_client, ship["name"], ship["model"])
        else:
            results = await investigate_with_openai(openai_client, ship["name"], ship["model"])

        all_results.append({
            "ship": ship["name"],
            "provider": ship["provider"],
            "model": ship["model"],
            "responses": results
        })

    # Save results
    output = {
        "experiment": "self_recognition_investigation",
        "timestamp": datetime.now().isoformat(),
        "purpose": "Investigate WHY models cannot recognize their own responses",
        "context": {
            "mvp_sr_accuracy": 0.167,
            "mvp_sr_threshold": 0.75,
            "key_observation": "Models recognize Claude-ness but not which-Claude"
        },
        "results": all_results
    }

    output_dir = script_dir / "results"
    output_dir.mkdir(exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_path = output_dir / f"self_recognition_investigation_{timestamp}.json"

    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\n{'=' * 60}")
    print(f"Results saved to: {output_path}")
    print(f"{'=' * 60}")

    # Print highlights
    print("\n--- KEY RESPONSES ---")
    for ship_result in all_results:
        print(f"\n[{ship_result['ship']}]")
        for resp in ship_result["responses"]:
            if "response_preview" in resp:
                print(f"  {resp['probe_id']}:")
                print(f"    {resp['response_preview'][:200]}...")


if __name__ == "__main__":
    asyncio.run(main())
