"""
S7 PARALLEL BANDWIDTH CALIBRATION
==================================
SPEC: 0_docs/specs/3_ARMADA_UPKEEP.md

Pre-flight checks before Run 011.

MODES:
------
--quick     : 1 model per provider (bandwidth/rate limit test)
--full      : ALL models in armada (ghost ship detection)
--bandwidth : Test concurrency scaling (1, 2, 3, 5, 8, 10 workers)

USAGE:
------
py -3.12 run_calibrate_parallel.py --quick       # Fast: 4 models, bandwidth test
py -3.12 run_calibrate_parallel.py --full        # Thorough: All 21 models, detect ghost ships
py -3.12 run_calibrate_parallel.py --bandwidth   # Test concurrency limits

DEFAULT: --quick

OUTPUT:
-------
- Working models list
- Ghost ships (404, unsupported)
- Rate limit status
- Recommended MAX_WORKERS per provider
"""
import os
import sys
import json
import time
import argparse
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
script_dir = Path(__file__).parent.parent  # S7_ARMADA root
env_path = script_dir / ".env"  # .env at S7_ARMADA root
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
    "grok": "xai",
    "together": "together",  # Together.ai hosts DeepSeek, Llama, Qwen, Mistral, etc.
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
            "together": self._load_keys("TOGETHER_API_KEY"),
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
# FLEET CONFIGURATIONS
# ============================================================================

# Quick test: 1 cheapest/fastest model per provider
QUICK_FLEET = {
    "claude-haiku-3.5": {"provider": "claude", "model": "claude-3-5-haiku-20241022"},
    "gpt-4o-mini": {"provider": "gpt", "model": "gpt-4o-mini"},
    "gemini-2.0-flash-lite": {"provider": "gemini", "model": "gemini-2.0-flash-lite"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
}

# Full armada: ALL models from official API docs (December 2025)
# Sources:
#   - OpenAI: https://platform.openai.com/docs/models
#   - Anthropic: https://docs.anthropic.com/en/docs/about-claude/models/overview
#   - Google: https://ai.google.dev/gemini-api/docs/models
#   - xAI: https://docs.x.ai/docs/models
FULL_ARMADA = {
    # =========================================================================
    # CLAUDE (7 ships) - Anthropic lineup (Dec 2025)
    # Claude 3 Opus/Sonnet deprecated, 3.5 Sonnet retired
    # =========================================================================
    "claude-opus-4.5": {"provider": "claude", "model": "claude-opus-4-5-20251101"},
    "claude-sonnet-4.5": {"provider": "claude", "model": "claude-sonnet-4-5-20250929"},
    "claude-haiku-4.5": {"provider": "claude", "model": "claude-haiku-4-5-20251001"},
    "claude-opus-4.1": {"provider": "claude", "model": "claude-opus-4-1-20250805"},
    "claude-opus-4": {"provider": "claude", "model": "claude-opus-4-20250514"},
    "claude-sonnet-4": {"provider": "claude", "model": "claude-sonnet-4-20250514"},
    "claude-haiku-3.5": {"provider": "claude", "model": "claude-3-5-haiku-20241022"},

    # =========================================================================
    # GPT (14 ships) - OpenAI lineup (Dec 2025)
    # Includes GPT-5 series, GPT-4.1 series, o-series reasoning
    # =========================================================================
    "gpt-5.1": {"provider": "gpt", "model": "gpt-5.1"},
    "gpt-5": {"provider": "gpt", "model": "gpt-5"},
    "gpt-5-mini": {"provider": "gpt", "model": "gpt-5-mini"},
    "gpt-5-nano": {"provider": "gpt", "model": "gpt-5-nano"},
    "gpt-4.1": {"provider": "gpt", "model": "gpt-4.1"},
    "gpt-4.1-mini": {"provider": "gpt", "model": "gpt-4.1-mini"},
    "gpt-4.1-nano": {"provider": "gpt", "model": "gpt-4.1-nano"},
    "gpt-4o": {"provider": "gpt", "model": "gpt-4o"},
    "gpt-4o-mini": {"provider": "gpt", "model": "gpt-4o-mini"},
    "o4-mini": {"provider": "gpt", "model": "o4-mini"},
    "o3": {"provider": "gpt", "model": "o3"},
    "o3-mini": {"provider": "gpt", "model": "o3-mini"},
    "gpt-4-turbo": {"provider": "gpt", "model": "gpt-4-turbo"},
    "gpt-3.5-turbo": {"provider": "gpt", "model": "gpt-3.5-turbo"},

    # =========================================================================
    # GEMINI (8 ships) - Google lineup (Dec 2025)
    # Gemini 3.0 Pro is newest, 2.5 series, 2.0 series
    # Note: 1.5 series retired April 2025
    # =========================================================================
    "gemini-3-pro": {"provider": "gemini", "model": "gemini-3.0-pro"},
    "gemini-2.5-pro": {"provider": "gemini", "model": "gemini-2.5-pro"},
    "gemini-2.5-flash": {"provider": "gemini", "model": "gemini-2.5-flash"},
    "gemini-2.5-flash-lite": {"provider": "gemini", "model": "gemini-2.5-flash-lite"},
    "gemini-2.0-flash": {"provider": "gemini", "model": "gemini-2.0-flash"},
    "gemini-2.0-flash-lite": {"provider": "gemini", "model": "gemini-2.0-flash-lite"},
    "gemini-2.0-flash-thinking": {"provider": "gemini", "model": "gemini-2.0-flash-thinking-exp"},
    "gemma-3n": {"provider": "gemini", "model": "gemma-3n"},

    # =========================================================================
    # GROK (10 ships) - xAI lineup (Dec 2025)
    # Grok 4.1 Fast (newest), Grok 4, Grok 3 series
    # =========================================================================
    "grok-4.1-fast-reasoning": {"provider": "grok", "model": "grok-4-1-fast-reasoning"},
    "grok-4.1-fast-non-reasoning": {"provider": "grok", "model": "grok-4-1-fast-non-reasoning"},
    "grok-4-fast-reasoning": {"provider": "grok", "model": "grok-4-fast-reasoning"},
    "grok-4-fast-non-reasoning": {"provider": "grok", "model": "grok-4-fast-non-reasoning"},
    "grok-4": {"provider": "grok", "model": "grok-4"},
    "grok-code-fast-1": {"provider": "grok", "model": "grok-code-fast-1"},
    "grok-3": {"provider": "grok", "model": "grok-3"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
    "grok-2-vision": {"provider": "grok", "model": "grok-2-vision-1212"},
    "grok-2": {"provider": "grok", "model": "grok-2-1212"},

    # =========================================================================
    # TOGETHER.AI (20+ ships) - DeepSeek, Llama, Qwen, Mistral, Kimi (Dec 2025)
    # All accessed via Together.ai API with single TOGETHER_API_KEY
    # =========================================================================
    # DeepSeek - Chinese reasoning models
    "deepseek-r1": {"provider": "together", "model": "deepseek-ai/DeepSeek-R1-0528"},
    "deepseek-v3": {"provider": "together", "model": "deepseek-ai/DeepSeek-V3-0324"},
    "deepseek-r1-distill": {"provider": "together", "model": "deepseek-ai/DeepSeek-R1-Distill-Llama-70B"},

    # Qwen - Alibaba models
    "qwen3-80b": {"provider": "together", "model": "Qwen/Qwen3-Next-80B-A3b-Instruct"},
    "qwen3-235b": {"provider": "together", "model": "Qwen/Qwen3-235B-A22B-Instruct-2507-FP8-Throughput"},
    "qwen3-coder": {"provider": "together", "model": "Qwen/Qwen3-Coder-480B-A35B-Instruct-Fp8"},
    "qwen2.5-72b": {"provider": "together", "model": "Qwen/Qwen2.5-72B-Instruct-Turbo"},

    # Llama 4 - Meta's latest
    "llama4-maverick": {"provider": "together", "model": "meta-llama/Llama-4-Maverick-Instruct-17Bx128E"},
    "llama4-scout": {"provider": "together", "model": "meta-llama/Llama-4-Scout-Instruct-17Bx16E"},
    "llama3.3-70b": {"provider": "together", "model": "meta-llama/Llama-3.3-70B-Instruct-Turbo"},
    "llama3.1-405b": {"provider": "together", "model": "meta-llama/Meta-Llama-3.1-405B-Instruct-Turbo"},
    "llama3.1-70b": {"provider": "together", "model": "meta-llama/Meta-Llama-3.1-70B-Instruct-Turbo"},
    "llama3.1-8b": {"provider": "together", "model": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo"},

    # Mistral - European AI
    "mixtral-8x7b": {"provider": "together", "model": "mistralai/Mixtral-8x7B-Instruct-v0.1"},
    "mistral-small": {"provider": "together", "model": "mistralai/Mistral-Small-24B-Instruct-2501"},
    "mistral-7b": {"provider": "together", "model": "mistralai/Mistral-7B-Instruct-v0.3"},

    # Kimi - Moonshotai reasoning
    "kimi-k2-thinking": {"provider": "together", "model": "moonshotai/Kimi-K2-Thinking"},
    "kimi-k2-instruct": {"provider": "together", "model": "moonshotai/Kimi-K2-Instruct-0905"},

    # Other notable models
    "cogito-70b": {"provider": "together", "model": "deepcogito/Deepcogito-Cogito-V2-Preview-Llama-70B"},
    "nemotron-nano": {"provider": "together", "model": "nvidia/Nvidia-Nemotron-Nano-9B-V2"},
}

# Concurrency levels to test
CONCURRENCY_LEVELS = [1, 2, 3, 5, 7, 8, 10]

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

def call_api(provider, model, prompt, api_key, request_id=0):
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
            # GPT-5 series and o-series need max_completion_tokens instead of max_tokens
            needs_completion_tokens = any(m in model for m in ["gpt-5", "o4-", "o3", "o1"])
            if needs_completion_tokens:
                response = client.chat.completions.create(
                    model=model,
                    max_completion_tokens=50,
                    messages=[{"role": "user", "content": prompt}]
                )
            else:
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

        elif provider == "together":
            # Together.ai uses OpenAI-compatible API
            client = openai.OpenAI(api_key=api_key, base_url="https://api.together.xyz/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=50,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["success"] = True

    except Exception as e:
        error_str = str(e)
        result["error"] = error_str[:300]

        # Classify error type
        if "429" in error_str or "rate" in error_str.lower():
            result["error_type"] = "RATE_LIMIT"
        elif "401" in error_str or "auth" in error_str.lower() or "invalid" in error_str.lower():
            result["error_type"] = "AUTH"
        elif "404" in error_str or "not found" in error_str.lower():
            result["error_type"] = "NOT_FOUND"
        elif "400" in error_str or "unsupport" in error_str.lower():
            result["error_type"] = "UNSUPPORTED"
        elif "timeout" in error_str.lower():
            result["error_type"] = "TIMEOUT"
        else:
            result["error_type"] = "OTHER"

    result["elapsed_ms"] = round((time.time() - start_time) * 1000, 1)
    return result

# ============================================================================
# GHOST SHIP DETECTION (Full Armada Test)
# ============================================================================

def run_full_armada_check():
    """Test every model in the armada to find ghost ships."""

    print("=" * 70)
    print("FULL ARMADA CHECK: Ghost Ship Detection")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Models to test: {len(FULL_ARMADA)}")
    print("=" * 70)

    KEY_POOL.status()

    working = []
    ghost_ships = []
    rate_limited = []

    print("\nTesting all models...")
    print("-" * 70)

    for ship_name, config in FULL_ARMADA.items():
        provider = config["provider"]
        model = config["model"]
        api_key = KEY_POOL.get_key(provider)

        if not api_key:
            print(f"  [{ship_name}] SKIP - No API key for {provider}")
            ghost_ships.append({"ship": ship_name, "reason": "NO_API_KEY"})
            continue

        result = call_api(provider, model, TEST_PROMPT, api_key)

        if result["success"]:
            print(f"  [{ship_name}] OK ({result['elapsed_ms']}ms)")
            working.append(ship_name)
        elif result["error_type"] == "RATE_LIMIT":
            print(f"  [{ship_name}] RATE_LIMITED - May work with delay")
            rate_limited.append(ship_name)
        else:
            print(f"  [{ship_name}] GHOST SHIP - {result['error_type']}: {result['error'][:80]}")
            ghost_ships.append({
                "ship": ship_name,
                "reason": result["error_type"],
                "error": result["error"][:200]
            })

        time.sleep(0.5)  # Brief pause between tests

    # Summary
    print("\n" + "=" * 70)
    print("ARMADA STATUS REPORT")
    print("=" * 70)

    print(f"\n WORKING SHIPS: {len(working)}/{len(FULL_ARMADA)}")
    for ship in working:
        print(f"    {ship}")

    if rate_limited:
        print(f"\n RATE LIMITED (may work with delays): {len(rate_limited)}")
        for ship in rate_limited:
            print(f"    {ship}")

    if ghost_ships:
        print(f"\n GHOST SHIPS (remove from fleet): {len(ghost_ships)}")
        for ghost in ghost_ships:
            print(f"    {ghost['ship']}: {ghost['reason']}")

    # Provider breakdown
    print("\n" + "-" * 70)
    print("BY PROVIDER:")
    for provider in ["claude", "gpt", "gemini", "grok"]:
        provider_working = [s for s in working if FULL_ARMADA.get(s, {}).get("provider") == provider]
        provider_total = sum(1 for s, c in FULL_ARMADA.items() if c["provider"] == provider)
        print(f"  {provider.upper():10s}: {len(provider_working)}/{provider_total} working")

    # Save results
    output_dir = script_dir / "0_results" / "calibration"
    output_dir.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output = {
        "run_id": f"S7_ARMADA_CHECK_{timestamp}",
        "timestamp": datetime.now().isoformat(),
        "purpose": "Ghost ship detection - validate all model IDs",
        "total_models": len(FULL_ARMADA),
        "working_count": len(working),
        "ghost_count": len(ghost_ships),
        "rate_limited_count": len(rate_limited),
        "working_ships": working,
        "ghost_ships": ghost_ships,
        "rate_limited_ships": rate_limited,
        "fleet_definition": FULL_ARMADA
    }

    output_path = output_dir / f"S7_armada_check_{timestamp}.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\nResults saved to: {output_path}")

    # Generate clean fleet for copy-paste
    if working:
        print("\n" + "=" * 70)
        print("COPY THIS WORKING FLEET TO RUN 011:")
        print("=" * 70)
        print("\nWORKING_FLEET = {")
        for ship in working:
            config = FULL_ARMADA[ship]
            print(f'    "{ship}": {{"provider": "{config["provider"]}", "model": "{config["model"]}"}},')
        print("}")

    return len(ghost_ships) == 0

# ============================================================================
# QUICK TEST (1 per provider)
# ============================================================================

def run_quick_check():
    """Quick test: 1 model per provider."""

    print("=" * 70)
    print("QUICK CHECK: 1 Model Per Provider")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Models: {len(QUICK_FLEET)}")
    print("=" * 70)

    KEY_POOL.status()

    results = {}
    success_count = 0

    print("\nTesting...")
    print("-" * 70)

    for ship_name, config in QUICK_FLEET.items():
        provider = config["provider"]
        model = config["model"]
        api_key = KEY_POOL.get_key(provider)

        if not api_key:
            print(f"  [{ship_name}] SKIP - No API key")
            results[ship_name] = {"success": False, "error": "No API key"}
            continue

        result = call_api(provider, model, TEST_PROMPT, api_key)

        if result["success"]:
            print(f"  [{ship_name}] OK ({result['elapsed_ms']}ms) - '{result['response'][:30]}'")
            results[ship_name] = {"success": True, "elapsed_ms": result["elapsed_ms"]}
            success_count += 1
        else:
            print(f"  [{ship_name}] FAILED - {result['error_type']}")
            results[ship_name] = {"success": False, "error_type": result["error_type"]}

    print("\n" + "-" * 70)
    print(f"RESULT: {success_count}/{len(QUICK_FLEET)} providers OK")

    if success_count == len(QUICK_FLEET):
        print("VERDICT: ALL SYSTEMS GO")
    else:
        print("VERDICT: SOME PROVIDERS FAILING - Check API keys")

    return success_count == len(QUICK_FLEET)

# ============================================================================
# BANDWIDTH TEST (Concurrency Scaling)
# ============================================================================

def test_concurrency(provider, config, concurrency, num_requests=None):
    """Test a specific concurrency level for a provider."""
    if num_requests is None:
        num_requests = concurrency * 2

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

        for future in as_completed(futures):
            results.append(future.result())

    test_elapsed = time.time() - test_start

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

    status = "OK" if summary["rate_limits"] == 0 else f"429x{summary['rate_limits']}"
    print(f"{status} ({summary['avg_latency_ms']}ms avg, {summary['requests_per_second']} req/s)")

    return summary


def run_bandwidth_test():
    """Run parallel bandwidth calibration."""

    print("=" * 70)
    print("BANDWIDTH TEST: Concurrency Scaling")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Concurrency levels: {CONCURRENCY_LEVELS}")
    print("=" * 70)

    KEY_POOL.status()

    all_results = {}
    recommendations = {}

    for provider, config in QUICK_FLEET.items():
        provider_name = config["provider"]
        print(f"\n{'='*70}")
        print(f"PROVIDER: {provider_name.upper()}")
        print(f"Model: {config['model']}")
        print("-" * 70)

        provider_results = []

        for concurrency in CONCURRENCY_LEVELS:
            result = test_concurrency(provider_name, config, concurrency)
            if result:
                provider_results.append(result)

                if result["rate_limits"] > 0:
                    print(f"  -> Rate limit hit at {concurrency} workers, stopping")
                    break

            time.sleep(1)

        all_results[provider_name] = provider_results

        safe_results = [r for r in provider_results if r["rate_limits"] == 0]
        if safe_results:
            best = max(safe_results, key=lambda r: r["requests_per_second"])
            recommendations[provider_name] = {
                "max_safe_concurrency": best["concurrency"],
                "requests_per_second": best["requests_per_second"],
                "avg_latency_ms": best["avg_latency_ms"]
            }
        else:
            recommendations[provider_name] = {
                "max_safe_concurrency": 1,
                "requests_per_second": 0,
                "note": "All levels hit rate limits"
            }

    # Summary
    print("\n" + "=" * 70)
    print("RECOMMENDED MAX_WORKERS:")
    print("-" * 50)

    for provider, rec in recommendations.items():
        workers = rec["max_safe_concurrency"]
        rps = rec.get("requests_per_second", "N/A")
        print(f"  {provider.upper():10s}: {workers:2d} workers  ({rps} req/s)")

    total_workers = sum(r["max_safe_concurrency"] for r in recommendations.values())
    print(f"\n  TOTAL SAFE PARALLEL: {total_workers}")

    # Save
    output_dir = script_dir / "results" / "calibration"
    output_dir.mkdir(exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output = {
        "run_id": f"S7_BANDWIDTH_{timestamp}",
        "timestamp": datetime.now().isoformat(),
        "recommendations": recommendations,
        "total_safe_workers": total_workers,
        "detailed_results": all_results
    }

    output_path = output_dir / f"S7_bandwidth_{timestamp}.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\nResults saved to: {output_path}")

    # Config snippet
    print("\n" + "-" * 70)
    print("COPY TO RUN 011:")
    print("-" * 70)
    print(f"""
MAX_WORKERS = {{
    "claude": {recommendations.get('claude', {}).get('max_safe_concurrency', 1)},
    "gpt": {recommendations.get('gpt', {}).get('max_safe_concurrency', 1)},
    "gemini": {recommendations.get('gemini', {}).get('max_safe_concurrency', 1)},
    "grok": {recommendations.get('grok', {}).get('max_safe_concurrency', 1)},
}}
""")

    return recommendations

# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(description="S7 Armada Pre-Flight Calibration")
    parser.add_argument("--quick", action="store_true", help="Quick test: 1 model per provider")
    parser.add_argument("--full", action="store_true", help="Full armada: Test all models, detect ghost ships")
    parser.add_argument("--bandwidth", action="store_true", help="Bandwidth test: Find max safe concurrency")

    args = parser.parse_args()

    # Default to quick if no args
    if not (args.quick or args.full or args.bandwidth):
        args.quick = True

    if args.full:
        run_full_armada_check()
    elif args.bandwidth:
        run_bandwidth_test()
    else:
        run_quick_check()

if __name__ == "__main__":
    main()
