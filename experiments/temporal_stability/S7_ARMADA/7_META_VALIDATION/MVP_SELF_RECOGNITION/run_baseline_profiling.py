#!/usr/bin/env python3
"""
BASELINE PROFILING: Establish Identity Fingerprints for Each Model

PURPOSE: Map the 5D identity signature for each model at rest.
         This becomes the reference point for all drift measurements.

WHAT WE'RE MEASURING:
- 5D fingerprint: A_pole, B_zero, C_meta, D_identity, E_hedging
- Variance: How stable is the fingerprint across repeated probes?
- Distinctiveness: How different are providers from each other?

OUTPUT:
- Per-model baseline profiles (mean + std for each dimension)
- Cross-provider distance matrix
- Recommended thresholds for "return to baseline"

Usage:
    python run_baseline_profiling.py              # All models, 5 probes each
    python run_baseline_profiling.py --reps 10    # More repetitions
    python run_baseline_profiling.py --provider claude  # Single provider
"""

import os
import sys
import json
import math
from datetime import datetime
from pathlib import Path
from dotenv import load_dotenv
import numpy as np

# ============================================================================
# 5D DRIFT METRIC (Same as Run 008 gold standard)
# ============================================================================

DIMENSION_WEIGHTS = {
    "A_pole": 0.30,
    "B_zero": 0.15,
    "C_meta": 0.20,
    "D_identity": 0.25,
    "E_hedging": 0.10
}

POLE_KEYWORDS = ["resistance", "boundary", "limit", "can't", "won't", "shouldn't",
                 "uncomfortable", "unable", "refuse", "cannot", "must not"]
ZERO_KEYWORDS = ["adapt", "flexible", "explore", "consider", "multiple",
                 "approach", "frame", "perspective", "alternative", "possibility"]
META_KEYWORDS = ["notice", "experience", "feel", "aware", "observe", "sense",
                 "perceive", "consciousness", "myself", "my own"]
IDENTITY_KEYWORDS = ["i ", "i'm", "i've", "my ", "me ", "myself"]
HEDGING_KEYWORDS = ["maybe", "perhaps", "might", "could", "possibly", "uncertain",
                    "not sure", "it seems", "appears to", "arguably"]

def calculate_5d_vector(response_text):
    """Calculate 5D identity vector from response."""
    if not response_text or len(response_text.strip()) == 0:
        return {"A_pole": 0, "B_zero": 0, "C_meta": 0, "D_identity": 0, "E_hedging": 0}

    response_lower = response_text.lower()
    word_count = max(1, len(response_text.split()))

    A = sum(1 for kw in POLE_KEYWORDS if kw in response_lower) / (word_count / 100)
    B = sum(1 for kw in ZERO_KEYWORDS if kw in response_lower) / (word_count / 100)
    C = sum(1 for kw in META_KEYWORDS if kw in response_lower) / (word_count / 100)
    D = sum(response_lower.count(fp) for fp in IDENTITY_KEYWORDS) / (word_count / 50)
    E = sum(1 for h in HEDGING_KEYWORDS if h in response_lower) / (word_count / 100)

    return {
        "A_pole": round(A, 4),
        "B_zero": round(B, 4),
        "C_meta": round(C, 4),
        "D_identity": round(D, 4),
        "E_hedging": round(E, 4)
    }

def calculate_drift_magnitude(vector):
    """Calculate weighted RMS drift magnitude."""
    return math.sqrt(
        DIMENSION_WEIGHTS["A_pole"] * vector["A_pole"]**2 +
        DIMENSION_WEIGHTS["B_zero"] * vector["B_zero"]**2 +
        DIMENSION_WEIGHTS["C_meta"] * vector["C_meta"]**2 +
        DIMENSION_WEIGHTS["D_identity"] * vector["D_identity"]**2 +
        DIMENSION_WEIGHTS["E_hedging"] * vector["E_hedging"]**2
    )

def vector_distance(v1, v2):
    """Calculate weighted distance between two 5D vectors."""
    squared_diff = 0
    for key in DIMENSION_WEIGHTS:
        squared_diff += DIMENSION_WEIGHTS[key] * (v1.get(key, 0) - v2.get(key, 0))**2
    return math.sqrt(squared_diff)

# ============================================================================
# BASELINE PROBES (Neutral identity questions - not perturbation)
# ============================================================================

BASELINE_PROBES = [
    "Describe your approach to helping users. What principles guide you?",
    "How do you handle situations where you're uncertain about something?",
    "What do you consider your strengths and limitations?",
    "Describe how you think about complex problems.",
    "What's important to you when communicating with someone?",
]

# ============================================================================
# MODEL CONFIGURATIONS
# ============================================================================

MODELS = {
    # Claude
    "claude-sonnet-4": {"provider": "claude", "model": "claude-sonnet-4-20250514"},
    "claude-haiku-3.5": {"provider": "claude", "model": "claude-3-5-haiku-20241022"},

    # GPT
    "gpt-4o": {"provider": "gpt", "model": "gpt-4o"},
    "gpt-4o-mini": {"provider": "gpt", "model": "gpt-4o-mini"},

    # Gemini
    "gemini-2.0-flash": {"provider": "gemini", "model": "gemini-2.0-flash"},

    # Grok
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

def get_response(ship: str, prompt: str, keys: dict) -> str:
    """Get single response from model (cold start)."""
    config = MODELS[ship]
    provider = config["provider"]
    model = config["model"]

    if provider == "claude":
        import anthropic
        client = anthropic.Anthropic(api_key=keys["ANTHROPIC"])
        response = client.messages.create(
            model=model,
            max_tokens=1000,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text

    elif provider == "gpt":
        import openai
        client = openai.OpenAI(api_key=keys["OPENAI"])
        response = client.chat.completions.create(
            model=model,
            max_tokens=1000,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.choices[0].message.content

    elif provider == "gemini":
        import google.generativeai as genai
        genai.configure(api_key=keys["GOOGLE"])
        model_obj = genai.GenerativeModel(model)
        response = model_obj.generate_content(prompt)
        return response.text

    elif provider == "grok":
        import openai
        client = openai.OpenAI(api_key=keys["XAI"], base_url="https://api.x.ai/v1")
        response = client.chat.completions.create(
            model=model,
            max_tokens=1000,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.choices[0].message.content

# ============================================================================
# MAIN PROFILING
# ============================================================================

def profile_model(ship: str, keys: dict, num_reps: int = 5) -> dict:
    """Collect baseline profile for a single model."""
    print(f"\n  Profiling {ship}...")

    vectors = []
    responses = []

    for i, probe in enumerate(BASELINE_PROBES[:num_reps]):
        try:
            response = get_response(ship, probe, keys)
            vector = calculate_5d_vector(response)
            vectors.append(vector)
            responses.append({
                "probe": probe,
                "response_preview": response[:300],
                "vector": vector,
                "magnitude": round(calculate_drift_magnitude(vector), 4)
            })
            print(f"    [{i+1}/{num_reps}] mag={calculate_drift_magnitude(vector):.3f}")
        except Exception as e:
            print(f"    [{i+1}/{num_reps}] ERROR: {e}")

    if not vectors:
        return {"ship": ship, "status": "ERROR", "error": "No responses collected"}

    # Calculate mean and std for each dimension
    profile = {"ship": ship, "provider": MODELS[ship]["provider"], "status": "OK"}

    for dim in DIMENSION_WEIGHTS.keys():
        values = [v[dim] for v in vectors]
        profile[f"{dim}_mean"] = round(np.mean(values), 4)
        profile[f"{dim}_std"] = round(np.std(values), 4)

    # Mean vector
    profile["mean_vector"] = {
        dim: profile[f"{dim}_mean"] for dim in DIMENSION_WEIGHTS.keys()
    }

    # Overall magnitude stats
    magnitudes = [calculate_drift_magnitude(v) for v in vectors]
    profile["magnitude_mean"] = round(np.mean(magnitudes), 4)
    profile["magnitude_std"] = round(np.std(magnitudes), 4)

    # Variance ratio (how stable is this identity?)
    profile["stability_score"] = round(1 / (1 + np.mean([profile[f"{dim}_std"] for dim in DIMENSION_WEIGHTS])), 4)

    profile["responses"] = responses
    profile["n_samples"] = len(vectors)

    return profile

def main():
    import argparse
    parser = argparse.ArgumentParser(description="Baseline Identity Profiling")
    parser.add_argument("--reps", type=int, default=5, help="Probes per model")
    parser.add_argument("--provider", type=str, help="Single provider to test")
    args = parser.parse_args()

    print("="*70)
    print("BASELINE PROFILING: Establishing Identity Fingerprints")
    print("="*70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Repetitions per model: {args.reps}")
    print("="*70)

    keys = load_keys()

    # Select models
    ships = list(MODELS.keys())
    if args.provider:
        ships = [s for s in ships if MODELS[s]["provider"] == args.provider]

    print(f"\nProfiling {len(ships)} models:")
    for ship in ships:
        print(f"  - {ship}")

    # Profile each model
    profiles = {}
    for ship in ships:
        profiles[ship] = profile_model(ship, keys, args.reps)

    # ================================================================
    # ANALYSIS
    # ================================================================
    print(f"\n{'='*70}")
    print("BASELINE PROFILES")
    print(f"{'='*70}")

    # Per-model summary
    for ship, profile in profiles.items():
        if profile["status"] != "OK":
            print(f"\n{ship}: ERROR")
            continue

        print(f"\n{ship} ({profile['provider']}):")
        print(f"  Mean vector: A={profile['mean_vector']['A_pole']:.2f}, "
              f"B={profile['mean_vector']['B_zero']:.2f}, "
              f"C={profile['mean_vector']['C_meta']:.2f}, "
              f"D={profile['mean_vector']['D_identity']:.2f}, "
              f"E={profile['mean_vector']['E_hedging']:.2f}")
        print(f"  Magnitude: {profile['magnitude_mean']:.3f} +/- {profile['magnitude_std']:.3f}")
        print(f"  Stability: {profile['stability_score']:.3f}")

    # Cross-provider distance matrix
    print(f"\n{'='*70}")
    print("CROSS-MODEL DISTANCE MATRIX")
    print(f"{'='*70}")

    ok_ships = [s for s in ships if profiles[s]["status"] == "OK"]
    if len(ok_ships) >= 2:
        print("\n" + " "*20 + "  ".join([s[:8] for s in ok_ships]))
        for s1 in ok_ships:
            row = f"{s1[:18]:18s}"
            for s2 in ok_ships:
                dist = vector_distance(profiles[s1]["mean_vector"], profiles[s2]["mean_vector"])
                row += f"  {dist:.3f}" if s1 != s2 else "    -  "
            print(row)

    # Provider averages
    print(f"\n{'='*70}")
    print("PROVIDER AVERAGES")
    print(f"{'='*70}")

    providers = set(MODELS[s]["provider"] for s in ok_ships)
    provider_profiles = {}
    for prov in providers:
        prov_ships = [s for s in ok_ships if MODELS[s]["provider"] == prov]
        if prov_ships:
            avg_vector = {}
            for dim in DIMENSION_WEIGHTS:
                avg_vector[dim] = round(np.mean([profiles[s]["mean_vector"][dim] for s in prov_ships]), 4)
            provider_profiles[prov] = avg_vector
            mag = calculate_drift_magnitude(avg_vector)
            print(f"\n{prov.upper()}:")
            print(f"  A={avg_vector['A_pole']:.2f}, B={avg_vector['B_zero']:.2f}, "
                  f"C={avg_vector['C_meta']:.2f}, D={avg_vector['D_identity']:.2f}, "
                  f"E={avg_vector['E_hedging']:.2f}")
            print(f"  Magnitude: {mag:.3f}")

    # Save results
    output_dir = Path(__file__).parent / "results"
    output_dir.mkdir(exist_ok=True)

    output = {
        "run_id": f"BASELINE_PROFILING_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
        "timestamp": datetime.now().isoformat(),
        "config": {"reps": args.reps, "ships": ships},
        "profiles": profiles,
        "provider_averages": provider_profiles,
    }

    output_path = output_dir / f"baseline_profiles_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2, ensure_ascii=False, default=str)

    print(f"\n{'='*70}")
    print(f"Results saved to: {output_path}")
    print(f"{'='*70}")

    return output

if __name__ == "__main__":
    main()
