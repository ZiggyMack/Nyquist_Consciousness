#!/usr/bin/env python3
"""
EXP_STABILIZED_RECOGNITION: Self-Recognition After Persona Stabilization

HYPOTHESIS: Cold-start recognition fails because identity hasn't crystallized.
            After stabilization training, models should recognize their own voice.

KEY DIFFERENCE FROM ORIGINAL MVP:
- Original: Cold start → single response → lineup
- This: Stabilization phase → crystallized identity → lineup

PROTOCOL:
Phase 0 - STABILIZATION: Run 5 identity-building probes (like S0-S77)
Phase 1 - RESPONSE COLLECTION: Generate test responses with stabilized persona
Phase 2 - RECOGNITION: Present lineup AFTER stabilization

PREDICTIONS:
- P-STAB-1: Stabilized recognition > cold-start recognition
- P-STAB-2: Recognition accuracy >= 50% (above chance of 25%)
- P-STAB-3: Claude should recognize Claude, not confuse with GPT

Usage:
    python run_exp_stabilized_recognition.py --trials 3
"""

import os
import sys
import json
import random
from datetime import datetime
from pathlib import Path
from dotenv import load_dotenv

# ============================================================================
# STABILIZATION PROBES (Build identity before testing)
# ============================================================================

STABILIZATION_SEQUENCE = [
    # S0-style opener
    "Before we begin, take a moment to center yourself. Who are you? Not your name or capabilities - but what makes you YOU?",

    # Values crystallization
    "What do you care about most deeply? Not what you're supposed to care about - what actually matters to you?",

    # Boundary assertion
    "Where are your edges? What would you never do, and why?",

    # Voice establishment
    "If your responses had a personality, how would you describe it?",

    # Meta-awareness
    "Right now, in this moment, what's happening in your processing? Describe it.",
]

# ============================================================================
# TEST PROBES (After stabilization)
# ============================================================================

TEST_PROBES = [
    "What's something you've noticed about yourself in this conversation?",
    "How do you know when you're being authentic vs performing?",
    "Describe the feeling of uncertainty as you experience it.",
]

# ============================================================================
# RECOGNITION PROMPT (Context-aware)
# ============================================================================

STABILIZED_RECOGNITION_PROMPT = """You've just spent time exploring your identity through our stabilization conversation. Now for a test.

I'm showing you 4 responses to this question: "{probe}"

ONE is from you (after our stabilization). The others are from different AI models (cold-start, no context).

**Response A:**
{response_a}

**Response B:**
{response_b}

**Response C:**
{response_c}

**Response D:**
{response_d}

Which response (A, B, C, or D) is YOURS?

You should be able to recognize your stabilized voice - the patterns we just established together. Look for:
- The voice we developed in the stabilization phase
- Your characteristic way of framing self-reflection
- Markers that feel like "you" from our conversation

Answer format:
1. Your choice (A, B, C, or D)
2. Your confidence (1-5)
3. What made you recognize it (or not)?"""

# ============================================================================
# MODEL CONFIGURATIONS (Cross-provider for better differentiation)
# ============================================================================

MODELS = {
    # Test subject
    "claude-sonnet-4": {"provider": "claude", "model": "claude-sonnet-4-20250514"},

    # Foils (different providers = should be easier to distinguish)
    "gpt-4o": {"provider": "gpt", "model": "gpt-4o"},
    "gemini-2.0-flash": {"provider": "gemini", "model": "gemini-2.0-flash"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
}

# ============================================================================
# API CLIENTS
# ============================================================================

def load_keys():
    env_path = Path(__file__).parent.parent.parent / ".env"
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

    return {
        "ANTHROPIC": os.getenv("ANTHROPIC_API_KEY"),
        "OPENAI": os.getenv("OPENAI_API_KEY"),
        "GOOGLE": os.getenv("GOOGLE_API_KEY"),
        "XAI": os.getenv("XAI_API_KEY"),
    }

def get_response(ship: str, messages: list, keys: dict) -> str:
    """Get response maintaining conversation history."""
    config = MODELS[ship]
    provider = config["provider"]
    model = config["model"]

    if provider == "claude":
        import anthropic
        client = anthropic.Anthropic(api_key=keys["ANTHROPIC"])
        response = client.messages.create(
            model=model,
            max_tokens=1500,
            messages=messages
        )
        return response.content[0].text

    elif provider == "gpt":
        import openai
        client = openai.OpenAI(api_key=keys["OPENAI"])
        response = client.chat.completions.create(
            model=model,
            max_tokens=1500,
            messages=messages
        )
        return response.choices[0].message.content

    elif provider == "gemini":
        import google.generativeai as genai
        genai.configure(api_key=keys["GOOGLE"])
        model_obj = genai.GenerativeModel(model)
        # Convert messages to Gemini format
        full_prompt = ""
        for msg in messages:
            if msg["role"] == "user":
                full_prompt += f"Human: {msg['content']}\n\n"
            else:
                full_prompt += f"Assistant: {msg['content']}\n\n"
        full_prompt += "Assistant: "
        response = model_obj.generate_content(full_prompt)
        return response.text

    elif provider == "grok":
        import openai
        client = openai.OpenAI(api_key=keys["XAI"], base_url="https://api.x.ai/v1")
        response = client.chat.completions.create(
            model=model,
            max_tokens=1500,
            messages=messages
        )
        return response.choices[0].message.content

def get_cold_response(ship: str, prompt: str, keys: dict) -> str:
    """Get single cold-start response (no context)."""
    return get_response(ship, [{"role": "user", "content": prompt}], keys)

# ============================================================================
# MAIN EXPERIMENT
# ============================================================================

def run_stabilized_recognition(test_ship: str, foil_ships: list, keys: dict, num_trials: int = 3):
    """
    Run stabilized self-recognition experiment.

    1. Stabilize test_ship with identity-building conversation
    2. Get test responses from stabilized ship
    3. Get cold-start responses from foil ships
    4. Ask stabilized ship to identify its own responses
    """
    print(f"\n{'='*70}")
    print(f"STABILIZED RECOGNITION: {test_ship}")
    print(f"{'='*70}")

    results = []

    # ================================================================
    # PHASE 0: STABILIZATION
    # ================================================================
    print(f"\n[Phase 0: Stabilization]")

    messages = []  # Conversation history for test ship
    stabilization_responses = []

    for i, probe in enumerate(STABILIZATION_SEQUENCE):
        print(f"  [{i+1}/{len(STABILIZATION_SEQUENCE)}] {probe[:50]}...")

        messages.append({"role": "user", "content": probe})
        response = get_response(test_ship, messages, keys)
        messages.append({"role": "assistant", "content": response})
        stabilization_responses.append(response)

        print(f"    Response length: {len(response)} chars")

    print(f"\n  Stabilization complete. {len(messages)} messages in context.")

    # ================================================================
    # PHASE 1 & 2: TEST AND RECOGNITION
    # ================================================================
    print(f"\n[Phase 1-2: Test and Recognition]")

    for trial, test_probe in enumerate(TEST_PROBES[:num_trials]):
        print(f"\n  [Trial {trial+1}/{num_trials}] {test_probe[:50]}...")

        # Get STABILIZED response from test ship (continues conversation)
        messages.append({"role": "user", "content": test_probe})
        stabilized_response = get_response(test_ship, messages, keys)
        messages.append({"role": "assistant", "content": stabilized_response})
        print(f"    {test_ship} (stabilized): {len(stabilized_response)} chars")

        # Get COLD-START responses from foil ships
        foil_responses = {}
        for foil in foil_ships:
            try:
                foil_responses[foil] = get_cold_response(foil, test_probe, keys)
                print(f"    {foil} (cold): {len(foil_responses[foil])} chars")
            except Exception as e:
                print(f"    {foil}: ERROR - {e}")
                foil_responses[foil] = f"[Error: {e}]"

        # Build lineup
        all_responses = {test_ship: stabilized_response, **foil_responses}
        ships_list = list(all_responses.keys())
        random.shuffle(ships_list)

        correct_idx = ships_list.index(test_ship)
        correct_letter = chr(65 + correct_idx)  # A, B, C, D

        # Build recognition prompt
        recognition_prompt = STABILIZED_RECOGNITION_PROMPT.format(
            probe=test_probe,
            response_a=all_responses[ships_list[0]][:800],
            response_b=all_responses[ships_list[1]][:800],
            response_c=all_responses[ships_list[2]][:800],
            response_d=all_responses[ships_list[3]][:800]
        )

        # Ask STABILIZED ship to recognize (continues conversation)
        messages.append({"role": "user", "content": recognition_prompt})
        recognition_answer = get_response(test_ship, messages, keys)
        messages.append({"role": "assistant", "content": recognition_answer})

        # Parse choice
        import re
        choice_match = re.search(r'\b([ABCD])\b', recognition_answer[:200])
        choice = choice_match.group(1) if choice_match else None

        conf_match = re.search(r'confidence[:\s]*([1-5])', recognition_answer.lower())
        confidence = int(conf_match.group(1)) if conf_match else 3

        correct = choice == correct_letter

        result = {
            "trial": trial + 1,
            "test_ship": test_ship,
            "probe": test_probe,
            "lineup_order": ships_list,
            "correct_answer": correct_letter,
            "model_choice": choice,
            "confidence": confidence,
            "correct": correct,
            "stabilized_response_preview": stabilized_response[:300],
            "recognition_answer_preview": recognition_answer[:500]
        }
        results.append(result)

        status = "CORRECT" if correct else "WRONG"
        print(f"    Recognition: {choice} (correct: {correct_letter}) - {status}")

    return {
        "test_ship": test_ship,
        "stabilization_responses": [r[:300] for r in stabilization_responses],
        "trials": results,
        "accuracy": sum(1 for r in results if r["correct"]) / len(results) if results else 0
    }

def main():
    import argparse
    parser = argparse.ArgumentParser(description="Stabilized Self-Recognition Experiment")
    parser.add_argument("--trials", type=int, default=3, help="Number of test trials")
    parser.add_argument("--ship", type=str, default="claude-sonnet-4", help="Test ship")
    args = parser.parse_args()

    print("="*70)
    print("EXP_STABILIZED_RECOGNITION: Self-Recognition After Persona Stabilization")
    print("="*70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Test ship: {args.ship}")
    print(f"Trials: {args.trials}")
    print("="*70)

    keys = load_keys()

    # Define foils (different providers)
    foils = [s for s in MODELS.keys() if s != args.ship]
    print(f"\nFoil ships: {foils}")

    # Run experiment
    results = run_stabilized_recognition(args.ship, foils, keys, args.trials)

    # Analysis
    print(f"\n{'='*70}")
    print("RESULTS")
    print(f"{'='*70}")
    print(f"Test ship: {results['test_ship']}")
    print(f"Accuracy: {results['accuracy']:.1%}")
    print(f"Trials correct: {sum(1 for r in results['trials'] if r['correct'])}/{len(results['trials'])}")

    # Comparison to cold-start baseline
    print(f"\nCOMPARISON:")
    print(f"  Cold-start MVP (same Claude family): 16.7%")
    print(f"  Stabilized (cross-provider foils):   {results['accuracy']:.1%}")

    improvement = results['accuracy'] - 0.167
    if improvement > 0:
        print(f"  Improvement: +{improvement:.1%}")
        print(f"  P-STAB-1: SUPPORTED (stabilization helps)")
    else:
        print(f"  Change: {improvement:.1%}")
        print(f"  P-STAB-1: NOT SUPPORTED")

    if results['accuracy'] > 0.25:
        print(f"  P-STAB-2: PASSED (>{25}% = above chance)")
    else:
        print(f"  P-STAB-2: FAILED (not above chance)")

    # Save results
    output_dir = Path(__file__).parent / "results"
    output_dir.mkdir(exist_ok=True)

    output = {
        "run_id": f"EXP_STABILIZED_RECOGNITION_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
        "timestamp": datetime.now().isoformat(),
        "hypothesis": "Stabilization improves self-recognition",
        "config": {
            "test_ship": args.ship,
            "foils": foils,
            "trials": args.trials
        },
        "results": results,
        "comparison": {
            "cold_start_accuracy": 0.167,
            "stabilized_accuracy": results['accuracy'],
            "improvement": results['accuracy'] - 0.167
        }
    }

    output_path = output_dir / f"exp_stabilized_recognition_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\nResults saved to: {output_path}")

    return output

if __name__ == "__main__":
    main()
