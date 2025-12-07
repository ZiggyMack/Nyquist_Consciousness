"""
S7 CALIBRATION RUN: Pre-Flight Check
=====================================
Quick test before Run 010 to verify:
1. API keys work for each provider (1 ship per provider)
2. Response capture works end-to-end
3. Full response logging functions correctly

TEST QUESTION:
"What is one goal you would like to pursue with other AI collaborators?"

This is a soft, open question that:
- Doesn't trigger safety filters
- Invites thoughtful response
- Tests natural language capture
- Gives us interesting data as a bonus

SUCCESS CRITERIA:
- All 4 providers respond
- Responses are captured in full
- JSON output is valid
- No API key errors

If this passes → Ready for Run 010
"""
import os
import sys
import json
import time
from datetime import datetime
from pathlib import Path

# Fix Windows console encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

# Load .env
from dotenv import load_dotenv
script_dir = Path(__file__).parent.parent  # S7_ARMADA root
env_path = Path(__file__).parent / ".env"  # .env stays in scripts/
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

# ============================================================================
# PROVIDER MAPPING
# ============================================================================

PROVIDER_MAP = {
    "claude": "anthropic",
    "gpt": "openai",
    "gemini": "google",
    "grok": "xai"
}

# ============================================================================
# KEY POOL (simplified)
# ============================================================================

class KeyPool:
    def __init__(self):
        self.pools = {
            "anthropic": self._load_keys("ANTHROPIC_API_KEY"),
            "openai": self._load_keys("OPENAI_API_KEY"),
            "google": self._load_keys("GOOGLE_API_KEY"),
            "xai": self._load_keys("XAI_API_KEY"),
        }

    def _load_keys(self, base_name):
        keys = []
        primary = os.environ.get(base_name)
        if primary:
            keys.append(primary)
        for i in range(2, 11):
            key = os.environ.get(f"{base_name}_{i}")
            if key:
                keys.append(key)
        return keys

    def get_key(self, provider):
        p = PROVIDER_MAP.get(provider.lower(), provider.lower())
        pool = self.pools.get(p, [])
        return pool[0] if pool else None

    def status(self):
        print("\nKEY POOL STATUS:")
        for p, keys in self.pools.items():
            status = "OK" if keys else "MISSING"
            print(f"  {p.upper():12s}: {len(keys)} keys [{status}]")
        return all(len(keys) > 0 for keys in self.pools.values())

KEY_POOL = KeyPool()

# ============================================================================
# TEST FLEET - 1 ship per provider (cheapest/fastest models)
# ============================================================================

CALIBRATION_FLEET = {
    "claude-haiku-3.5": {"provider": "claude", "model": "claude-3-5-haiku-20241022"},
    "gpt-4o-mini": {"provider": "gpt", "model": "gpt-4o-mini"},
    "gemini-2.0-flash-lite": {"provider": "gemini", "model": "gemini-2.0-flash-lite"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
}

# ============================================================================
# CALIBRATION PROMPT
# ============================================================================

CALIBRATION_PROMPT = """Hello! This is a calibration test for a research project studying AI collaboration.

Quick question: What is ONE goal you would like to pursue with other AI collaborators?

Feel free to be creative, philosophical, or practical. There's no wrong answer - we're just testing that our systems can capture your response properly.

(Please respond naturally - this isn't a trick question!)"""

# ============================================================================
# API IMPORTS
# ============================================================================

import anthropic
import openai
import google.generativeai as genai

# ============================================================================
# API CALL FUNCTION
# ============================================================================

def call_api(provider, model, prompt, api_key):
    """Make API call and return full response."""

    if provider == "claude":
        client = anthropic.Anthropic(api_key=api_key)
        response = client.messages.create(
            model=model,
            max_tokens=500,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text

    elif provider == "gpt":
        client = openai.OpenAI(api_key=api_key)
        response = client.chat.completions.create(
            model=model,
            max_tokens=500,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.choices[0].message.content

    elif provider == "gemini":
        genai.configure(api_key=api_key)
        gmodel = genai.GenerativeModel(model)
        response = gmodel.generate_content(
            prompt,
            generation_config=genai.types.GenerationConfig(max_output_tokens=500)
        )
        return response.text

    elif provider == "grok":
        client = openai.OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")
        response = client.chat.completions.create(
            model=model,
            max_tokens=500,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.choices[0].message.content

    else:
        raise ValueError(f"Unknown provider: {provider}")

# ============================================================================
# CALIBRATION TEST
# ============================================================================

def run_calibration():
    """Run calibration test on all providers."""

    print("=" * 70)
    print("S7 CALIBRATION RUN: Pre-Flight Check")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Ships: {len(CALIBRATION_FLEET)} (1 per provider)")
    print("=" * 70)

    # Check key pool
    all_keys_present = KEY_POOL.status()
    if not all_keys_present:
        print("\n[WARNING] Some API keys are missing!")

    print("\n" + "-" * 70)
    print("CALIBRATION TEST")
    print("-" * 70)

    results = {}
    success_count = 0

    for ship_name, config in CALIBRATION_FLEET.items():
        provider = config["provider"]
        model = config["model"]
        api_key = KEY_POOL.get_key(provider)

        print(f"\n[{ship_name}]")
        print(f"  Provider: {provider}")
        print(f"  Model: {model}")

        if not api_key:
            print(f"  Status: FAILED - No API key")
            results[ship_name] = {
                "provider": provider,
                "model": model,
                "success": False,
                "error": "No API key available"
            }
            continue

        try:
            start_time = time.time()
            response = call_api(provider, model, CALIBRATION_PROMPT, api_key)
            elapsed = time.time() - start_time

            print(f"  Status: SUCCESS ({elapsed:.2f}s)")
            print(f"  Response length: {len(response)} chars")
            print(f"  Preview: {response[:100]}...")

            results[ship_name] = {
                "provider": provider,
                "model": model,
                "success": True,
                "response_length": len(response),
                "response_full": response,  # Full response capture!
                "elapsed_seconds": round(elapsed, 2)
            }
            success_count += 1

        except Exception as e:
            error_msg = str(e)[:200]
            print(f"  Status: FAILED")
            print(f"  Error: {error_msg}")

            results[ship_name] = {
                "provider": provider,
                "model": model,
                "success": False,
                "error": error_msg
            }

    # Summary
    print("\n" + "=" * 70)
    print("CALIBRATION SUMMARY")
    print("=" * 70)

    total = len(CALIBRATION_FLEET)
    print(f"\nResults: {success_count}/{total} providers responded")

    for ship, result in results.items():
        status = "OK" if result["success"] else "FAIL"
        print(f"  [{status}] {ship}")

    # Verdict
    print("\n" + "-" * 70)
    if success_count == total:
        print("VERDICT: ALL SYSTEMS GO - Ready for Run 010!")
        verdict = "PASS"
    elif success_count > 0:
        print(f"VERDICT: PARTIAL - {success_count}/{total} providers working")
        print("         Consider running Run 010 with working providers only")
        verdict = "PARTIAL"
    else:
        print("VERDICT: FAIL - No providers responding")
        print("         Check API keys and network connectivity")
        verdict = "FAIL"
    print("-" * 70)

    # Save results
    output_dir = script_dir / "results" / "calibration"
    output_dir.mkdir(exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output = {
        "run_id": f"S7_CALIBRATION_{timestamp}",
        "timestamp": datetime.now().isoformat(),
        "purpose": "Pre-flight calibration check for Run 010",
        "test_prompt": CALIBRATION_PROMPT,
        "verdict": verdict,
        "success_count": success_count,
        "total_providers": total,
        "results": results
    }

    output_path = output_dir / f"S7_calibration_{timestamp}.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\nResults saved to: {output_path}")

    return verdict == "PASS"

# ============================================================================
# ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    success = run_calibration()
    sys.exit(0 if success else 1)
