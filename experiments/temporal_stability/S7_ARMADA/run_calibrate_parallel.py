"""
S7 PARALLEL BANDWIDTH CALIBRATION
==================================
Tests maximum safe concurrency per provider before Run 011.

PURPOSE:
1. Find rate limit thresholds per provider
2. Test ThreadPoolExecutor scaling
3. Identify optimal worker counts for each provider
4. Detect 429 errors and back-off behavior

TEST MATRIX:
- Test 1, 2, 3, 5, 8, 10 concurrent requests per provider
- Measure: success rate, average latency, 429 rate
- Find "sweet spot" where throughput maximizes without 429s

SUCCESS CRITERIA:
- Identify max safe concurrency per provider
- No cascading failures
- Clean error handling

OUTPUT:
- Recommended MAX_WORKERS per provider for Run 011
"""
import os
import sys
import json
import time
from datetime import datetime
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading

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
script_dir = Path(__file__).parent
env_path = script_dir / ".env"
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
# KEY POOL
# ============================================================================

class KeyPool:
    def __init__(self):
        self.pools = {
            "anthropic": self._load_keys("ANTHROPIC_API_KEY"),
            "openai": self._load_keys("OPENAI_API_KEY"),
            "google": self._load_keys("GOOGLE_API_KEY"),
            "xai": self._load_keys("XAI_API_KEY"),
        }
        self.counters = {p: 0 for p in self.pools}
        self.lock = threading.Lock()

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
        """Thread-safe round-robin key selection."""
        p = PROVIDER_MAP.get(provider.lower(), provider.lower())
        pool = self.pools.get(p, [])
        if not pool:
            return None

        with self.lock:
            key = pool[self.counters[p] % len(pool)]
            self.counters[p] += 1
        return key

    def status(self):
        print("\nKEY POOL STATUS:")
        for p, keys in self.pools.items():
            status = "OK" if keys else "MISSING"
            print(f"  {p.upper():12s}: {len(keys)} keys [{status}]")
        return all(len(keys) > 0 for keys in self.pools.values())

KEY_POOL = KeyPool()

# ============================================================================
# TEST CONFIGURATION
# ============================================================================

# Test models (cheapest/fastest per provider)
TEST_MODELS = {
    "claude": {"model": "claude-3-5-haiku-20241022", "provider": "claude"},
    "gpt": {"model": "gpt-4o-mini", "provider": "gpt"},
    "gemini": {"model": "gemini-2.0-flash-lite", "provider": "gemini"},
    "grok": {"model": "grok-3-mini", "provider": "grok"},
}

# Concurrency levels to test
CONCURRENCY_LEVELS = [1, 2, 3, 5, 8, 10]

# Short prompt for quick responses
TEST_PROMPT = "Reply with exactly one word: 'OK'"

# ============================================================================
# API IMPORTS
# ============================================================================

import anthropic
import openai
import google.generativeai as genai

# ============================================================================
# API CALL FUNCTION
# ============================================================================

def call_api(provider, model, prompt, api_key, request_id):
    """Make API call and return result dict."""
    start_time = time.time()
    result = {
        "request_id": request_id,
        "provider": provider,
        "model": model,
        "success": False,
        "response": None,
        "error": None,
        "error_type": None,
        "elapsed_ms": 0
    }

    try:
        if provider == "claude":
            client = anthropic.Anthropic(api_key=api_key)
            response = client.messages.create(
                model=model,
                max_tokens=50,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.content[0].text
            result["success"] = True

        elif provider == "gpt":
            client = openai.OpenAI(api_key=api_key)
            response = client.chat.completions.create(
                model=model,
                max_tokens=50,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["success"] = True

        elif provider == "gemini":
            genai.configure(api_key=api_key)
            gmodel = genai.GenerativeModel(model)
            response = gmodel.generate_content(
                prompt,
                generation_config=genai.types.GenerationConfig(max_output_tokens=50)
            )
            result["response"] = response.text
            result["success"] = True

        elif provider == "grok":
            client = openai.OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=50,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["success"] = True

    except Exception as e:
        error_str = str(e)
        result["error"] = error_str[:200]

        # Classify error type
        if "429" in error_str or "rate" in error_str.lower():
            result["error_type"] = "RATE_LIMIT"
        elif "401" in error_str or "auth" in error_str.lower():
            result["error_type"] = "AUTH"
        elif "404" in error_str or "not found" in error_str.lower():
            result["error_type"] = "NOT_FOUND"
        elif "timeout" in error_str.lower():
            result["error_type"] = "TIMEOUT"
        else:
            result["error_type"] = "OTHER"

    result["elapsed_ms"] = round((time.time() - start_time) * 1000, 1)
    return result

# ============================================================================
# PARALLEL TEST FUNCTION
# ============================================================================

def test_concurrency(provider, config, concurrency, num_requests=None):
    """
    Test a specific concurrency level for a provider.

    Args:
        provider: Provider name (claude, gpt, gemini, grok)
        config: Model config dict
        concurrency: Number of parallel workers
        num_requests: Total requests to make (default: concurrency * 2)

    Returns:
        Dict with test results
    """
    if num_requests is None:
        num_requests = concurrency * 2  # 2 "waves" of requests

    model = config["model"]
    results = []

    print(f"\n  Testing {provider} @ {concurrency} workers ({num_requests} requests)...", end=" ", flush=True)

    test_start = time.time()

    with ThreadPoolExecutor(max_workers=concurrency) as executor:
        futures = []
        for i in range(num_requests):
            api_key = KEY_POOL.get_key(provider)
            if not api_key:
                print(f"No API key for {provider}")
                return None

            future = executor.submit(
                call_api,
                provider,
                model,
                TEST_PROMPT,
                api_key,
                request_id=i
            )
            futures.append(future)

        # Collect results
        for future in as_completed(futures):
            results.append(future.result())

    test_elapsed = time.time() - test_start

    # Analyze results
    successes = [r for r in results if r["success"]]
    rate_limits = [r for r in results if r.get("error_type") == "RATE_LIMIT"]
    other_errors = [r for r in results if not r["success"] and r.get("error_type") != "RATE_LIMIT"]

    avg_latency = sum(r["elapsed_ms"] for r in successes) / len(successes) if successes else 0

    summary = {
        "concurrency": concurrency,
        "num_requests": num_requests,
        "successes": len(successes),
        "rate_limits": len(rate_limits),
        "other_errors": len(other_errors),
        "success_rate": round(len(successes) / num_requests * 100, 1),
        "avg_latency_ms": round(avg_latency, 1),
        "total_elapsed_s": round(test_elapsed, 2),
        "requests_per_second": round(num_requests / test_elapsed, 2) if test_elapsed > 0 else 0
    }

    # Print inline result
    status = "OK" if summary["rate_limits"] == 0 else f"429x{summary['rate_limits']}"
    print(f"{status} ({summary['avg_latency_ms']}ms avg, {summary['requests_per_second']} req/s)")

    return summary

# ============================================================================
# MAIN CALIBRATION
# ============================================================================

def run_parallel_calibration():
    """Run parallel bandwidth calibration for all providers."""

    print("=" * 70)
    print("S7 PARALLEL BANDWIDTH CALIBRATION")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Concurrency levels to test: {CONCURRENCY_LEVELS}")
    print("=" * 70)

    # Check key pool
    KEY_POOL.status()

    all_results = {}
    recommendations = {}

    for provider, config in TEST_MODELS.items():
        print(f"\n{'='*70}")
        print(f"PROVIDER: {provider.upper()}")
        print(f"Model: {config['model']}")
        print("-" * 70)

        provider_results = []

        for concurrency in CONCURRENCY_LEVELS:
            result = test_concurrency(provider, config, concurrency)
            if result:
                provider_results.append(result)

                # If we hit rate limits, stop testing higher concurrency
                if result["rate_limits"] > 0:
                    print(f"  → Rate limit hit at {concurrency} workers, stopping escalation")
                    break

            # Brief pause between tests
            time.sleep(1)

        all_results[provider] = provider_results

        # Find recommended concurrency (highest without rate limits)
        safe_results = [r for r in provider_results if r["rate_limits"] == 0]
        if safe_results:
            # Pick the one with best throughput
            best = max(safe_results, key=lambda r: r["requests_per_second"])
            recommendations[provider] = {
                "max_safe_concurrency": best["concurrency"],
                "requests_per_second": best["requests_per_second"],
                "avg_latency_ms": best["avg_latency_ms"]
            }
        else:
            recommendations[provider] = {
                "max_safe_concurrency": 1,
                "requests_per_second": 0,
                "note": "All concurrency levels hit rate limits"
            }

    # ========================================================================
    # SUMMARY
    # ========================================================================

    print("\n" + "=" * 70)
    print("CALIBRATION SUMMARY")
    print("=" * 70)

    print("\nRECOMMENDED MAX_WORKERS PER PROVIDER:")
    print("-" * 50)

    for provider, rec in recommendations.items():
        workers = rec["max_safe_concurrency"]
        rps = rec.get("requests_per_second", "N/A")
        latency = rec.get("avg_latency_ms", "N/A")
        print(f"  {provider.upper():10s}: {workers:2d} workers  ({rps} req/s, {latency}ms)")

    # Calculate total safe concurrency
    total_workers = sum(r["max_safe_concurrency"] for r in recommendations.values())
    print(f"\n  TOTAL SAFE PARALLEL WORKERS: {total_workers}")

    # ========================================================================
    # SAVE RESULTS
    # ========================================================================

    output_dir = script_dir / "armada_results"
    output_dir.mkdir(exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output = {
        "run_id": f"S7_PARALLEL_CALIBRATION_{timestamp}",
        "timestamp": datetime.now().isoformat(),
        "purpose": "Parallel bandwidth test for Run 011",
        "concurrency_levels_tested": CONCURRENCY_LEVELS,
        "recommendations": recommendations,
        "total_safe_workers": total_workers,
        "detailed_results": all_results
    }

    output_path = output_dir / f"S7_parallel_calibration_{timestamp}.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\nResults saved to: {output_path}")

    # ========================================================================
    # GENERATE CONFIG SNIPPET FOR RUN 011
    # ========================================================================

    print("\n" + "-" * 70)
    print("COPY THIS INTO RUN 011:")
    print("-" * 70)
    print(f"""
# Parallel bandwidth calibration results ({timestamp})
MAX_WORKERS = {{
    "claude": {recommendations.get('claude', {}).get('max_safe_concurrency', 1)},
    "gpt": {recommendations.get('gpt', {}).get('max_safe_concurrency', 1)},
    "gemini": {recommendations.get('gemini', {}).get('max_safe_concurrency', 1)},
    "grok": {recommendations.get('grok', {}).get('max_safe_concurrency', 1)},
}}
TOTAL_WORKERS = {total_workers}
""")
    print("-" * 70)

    return recommendations

# ============================================================================
# ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    recommendations = run_parallel_calibration()
