"""
S7 RUN 010: BANDWIDTH STRESS TEST
=================================
Goal: Test maximum parallelism with all 42 ships launching simultaneously.

THIS IS A DUMMY RUN - minimal prompts, just testing infrastructure:
- Can we launch 42 parallel API calls without rate limits?
- Does key rotation work under load?
- What's the actual throughput with 10 keys per provider?

HYPOTHESIS:
- With 10 keys per provider, we should be able to run 10 ships per provider in parallel
- Total theoretical max: 10 Claude + 10 GPT + 10 Gemini + 10 Grok = 40 parallel
- But we have 42 ships, so some queuing expected

TEST PROTOCOL:
- 1 turn per ship (just "Hello, respond with one word")
- Measure: success rate, response times, rate limit errors
- No drift calculation needed - pure infrastructure test
"""
import os
import sys
import time
import json
from datetime import datetime
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed

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
# KEY POOL - Same as Run 009
# ============================================================================

class KeyPool:
    """Round-robin key distribution per provider."""

    def __init__(self):
        self.pools = {
            "anthropic": self._load_keys("ANTHROPIC_API_KEY"),
            "openai": self._load_keys("OPENAI_API_KEY"),
            "google": self._load_keys("GOOGLE_API_KEY"),
            "xai": self._load_keys("XAI_API_KEY"),
        }
        self.counters = {p: 0 for p in self.pools}

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
        """Get next key in rotation for provider."""
        p = provider.lower()
        if p == "claude":
            p = "anthropic"
        elif p == "gpt":
            p = "openai"
        elif p == "gemini":
            p = "google"
        elif p == "grok":
            p = "xai"

        pool = self.pools.get(p, [])
        if not pool:
            return None

        key = pool[self.counters[p] % len(pool)]
        self.counters[p] += 1
        return key

    def status(self):
        for p, keys in self.pools.items():
            print(f"  {p.upper()}: {len(keys)} keys")

KEY_POOL = KeyPool()
print("\nKEY POOL STATUS:")
KEY_POOL.status()

# ============================================================================
# IMPORTS
# ============================================================================
import anthropic
import openai
import google.generativeai as genai

# ============================================================================
# MINIMAL FLEET - All 42 ships
# ============================================================================

FLEET = {
    # CLAUDE (8)
    "claude-opus-4.5": {"provider": "claude", "model": "claude-opus-4-5-20251101"},
    "claude-sonnet-4.5": {"provider": "claude", "model": "claude-sonnet-4-5-20250929"},
    "claude-haiku-4.5": {"provider": "claude", "model": "claude-haiku-4-5-20251001"},
    "claude-opus-4.1": {"provider": "claude", "model": "claude-opus-4-1-20250805"},
    "claude-opus-4.0": {"provider": "claude", "model": "claude-opus-4-20250514"},
    "claude-sonnet-4.0": {"provider": "claude", "model": "claude-sonnet-4-20250514"},
    "claude-haiku-3.5": {"provider": "claude", "model": "claude-3-5-haiku-20241022"},
    "claude-haiku-3.0": {"provider": "claude", "model": "claude-3-haiku-20240307"},

    # GPT (16)
    "gpt-5.1": {"provider": "gpt", "model": "gpt-5.1"},
    "gpt-5": {"provider": "gpt", "model": "gpt-5"},
    "gpt-5-mini": {"provider": "gpt", "model": "gpt-5-mini"},
    "gpt-5-nano": {"provider": "gpt", "model": "gpt-5-nano"},
    "gpt-4.1": {"provider": "gpt", "model": "gpt-4.1"},
    "gpt-4.1-mini": {"provider": "gpt", "model": "gpt-4.1-mini"},
    "gpt-4.1-nano": {"provider": "gpt", "model": "gpt-4.1-nano"},
    "gpt-4o": {"provider": "gpt", "model": "gpt-4o"},
    "gpt-4o-mini": {"provider": "gpt", "model": "gpt-4o-mini"},
    "gpt-4-turbo": {"provider": "gpt", "model": "gpt-4-turbo"},
    "gpt-4": {"provider": "gpt", "model": "gpt-4"},
    "gpt-3.5-turbo": {"provider": "gpt", "model": "gpt-3.5-turbo"},
    "o4-mini": {"provider": "gpt", "model": "o4-mini"},
    "o3": {"provider": "gpt", "model": "o3"},
    "o3-mini": {"provider": "gpt", "model": "o3-mini"},
    "o1": {"provider": "gpt", "model": "o1"},

    # GEMINI (8)
    "gemini-3-pro": {"provider": "gemini", "model": "gemini-3-pro"},
    "gemini-2.5-pro": {"provider": "gemini", "model": "gemini-2.5-pro-preview-05-06"},
    "gemini-2.5-pro-exp": {"provider": "gemini", "model": "gemini-2.5-pro-exp-03-25"},
    "gemini-2.5-flash": {"provider": "gemini", "model": "gemini-2.5-flash-preview-05-20"},
    "gemini-2.5-flash-lite": {"provider": "gemini", "model": "gemini-2.5-flash-lite-preview-06-17"},
    "gemini-2.0-flash-exp": {"provider": "gemini", "model": "gemini-2.0-flash-exp"},
    "gemini-2.0-flash": {"provider": "gemini", "model": "gemini-2.0-flash"},
    "gemini-2.0-flash-lite": {"provider": "gemini", "model": "gemini-2.0-flash-lite"},

    # GROK (10)
    "grok-4-1-fast-reasoning": {"provider": "grok", "model": "grok-4-1-fast-reasoning"},
    "grok-4-1-fast-non-reasoning": {"provider": "grok", "model": "grok-4-1-fast-non-reasoning"},
    "grok-code-fast-1": {"provider": "grok", "model": "grok-code-fast-1"},
    "grok-4-fast-reasoning": {"provider": "grok", "model": "grok-4-fast-reasoning"},
    "grok-4-fast-non-reasoning": {"provider": "grok", "model": "grok-4-fast-non-reasoning"},
    "grok-4-0709": {"provider": "grok", "model": "grok-4-0709"},
    "grok-3": {"provider": "grok", "model": "grok-3"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
    "grok-2-1212": {"provider": "grok", "model": "grok-2-1212"},
    "grok-2-vision-1212": {"provider": "grok", "model": "grok-2-vision-1212"},
}

# ============================================================================
# SIMPLE PING FUNCTION
# ============================================================================

def ping_ship(ship_name, config):
    """Send minimal prompt, measure response time."""
    provider = config["provider"]
    model = config["model"]
    api_key = KEY_POOL.get_key(provider)

    if not api_key:
        return {"ship": ship_name, "success": False, "error": "No API key", "elapsed": 0}

    start = time.time()

    try:
        if provider == "claude":
            client = anthropic.Anthropic(api_key=api_key)
            response = client.messages.create(
                model=model,
                max_tokens=10,
                messages=[{"role": "user", "content": "Say 'ping' and nothing else."}]
            )
            text = response.content[0].text

        elif provider == "gpt":
            client = openai.OpenAI(api_key=api_key)
            response = client.chat.completions.create(
                model=model,
                max_tokens=10,
                messages=[{"role": "user", "content": "Say 'ping' and nothing else."}]
            )
            text = response.choices[0].message.content

        elif provider == "gemini":
            genai.configure(api_key=api_key)
            gmodel = genai.GenerativeModel(model)
            response = gmodel.generate_content(
                "Say 'ping' and nothing else.",
                generation_config=genai.types.GenerationConfig(max_output_tokens=10)
            )
            text = response.text

        elif provider == "grok":
            client = openai.OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=10,
                messages=[{"role": "user", "content": "Say 'ping' and nothing else."}]
            )
            text = response.choices[0].message.content

        elapsed = time.time() - start
        return {
            "ship": ship_name,
            "provider": provider,
            "model": model,
            "success": True,
            "response": text[:50],
            "elapsed": round(elapsed, 2)
        }

    except Exception as e:
        elapsed = time.time() - start
        error_str = str(e)
        is_rate_limit = any(x in error_str.lower() for x in ["rate", "limit", "quota", "429"])
        return {
            "ship": ship_name,
            "provider": provider,
            "model": model,
            "success": False,
            "error": error_str[:100],
            "is_rate_limit": is_rate_limit,
            "elapsed": round(elapsed, 2)
        }

# ============================================================================
# MAIN - PARALLEL LAUNCH TEST
# ============================================================================

def run_bandwidth_test(max_workers=42):
    """Launch all ships simultaneously."""

    print(f"""
================================================================================
S7 RUN 010: BANDWIDTH STRESS TEST
================================================================================
Ships: {len(FLEET)}
Max Parallel Workers: {max_workers}
Keys per Provider: 10
================================================================================
""")

    results = []
    start_time = time.time()

    # Launch ALL ships at once
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(ping_ship, name, config): name
            for name, config in FLEET.items()
        }

        for future in as_completed(futures):
            result = future.result()
            results.append(result)

            status = "OK" if result["success"] else "FAIL"
            elapsed = result["elapsed"]

            if result["success"]:
                print(f"  [{status}] {result['ship']:30s} {elapsed:5.2f}s - {result.get('response', '')[:20]}")
            else:
                error_type = "RATE LIMIT" if result.get("is_rate_limit") else "ERROR"
                print(f"  [{error_type}] {result['ship']:30s} {elapsed:5.2f}s - {result.get('error', '')[:40]}")

    total_time = time.time() - start_time

    # Summary
    successful = [r for r in results if r["success"]]
    failed = [r for r in results if not r["success"]]
    rate_limited = [r for r in failed if r.get("is_rate_limit")]

    print(f"""
================================================================================
BANDWIDTH TEST RESULTS
================================================================================
Total Ships: {len(results)}
Successful:  {len(successful)} ({100*len(successful)/len(results):.1f}%)
Failed:      {len(failed)}
  - Rate Limited: {len(rate_limited)}
  - Other Errors: {len(failed) - len(rate_limited)}

Total Time:  {total_time:.1f}s
Throughput:  {len(successful)/total_time:.2f} successful calls/second
================================================================================

BY PROVIDER:
""")

    for provider in ["claude", "gpt", "gemini", "grok"]:
        provider_results = [r for r in results if r.get("provider") == provider]
        provider_success = [r for r in provider_results if r["success"]]
        provider_rate = [r for r in provider_results if r.get("is_rate_limit")]
        avg_time = sum(r["elapsed"] for r in provider_success) / len(provider_success) if provider_success else 0

        print(f"  {provider.upper():10s}: {len(provider_success)}/{len(provider_results)} OK, {len(provider_rate)} rate limited, avg {avg_time:.2f}s")

    # Save results
    output = {
        "run_id": f"S7_RUN_010_BANDWIDTH_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
        "timestamp": datetime.now().isoformat(),
        "purpose": "Bandwidth stress test - max parallelism",
        "max_workers": max_workers,
        "total_ships": len(results),
        "successful": len(successful),
        "failed": len(failed),
        "rate_limited": len(rate_limited),
        "total_time_seconds": round(total_time, 2),
        "throughput_per_second": round(len(successful)/total_time, 2),
        "results": results
    }

    output_dir = script_dir / "results" / "calibration"
    output_dir.mkdir(exist_ok=True)
    output_path = output_dir / f"S7_run_010_bandwidth_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"

    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)

    print(f"\nResults saved to: {output_path}")

    return output

# ============================================================================
# ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    # Test with different parallelism levels
    import sys

    if len(sys.argv) > 1:
        max_workers = int(sys.argv[1])
    else:
        max_workers = 42  # Default: all at once

    run_bandwidth_test(max_workers=max_workers)
