"""
CLAL - Cheap Large-scale Auto-Learn
====================================
Budget-only calibration for MASSIVE data collection.

PURPOSE:
--------
Run 1000+ calibrations at <$3 total cost to collect massive amounts
of calibration data for the Consciousness repo.

*** NEW DRY-RUN STANDARD ***
--UNLIMITED mode uses gemini-2.5-flash-lite (FREE forever) to stress-test
ALL experiment logic before spending money. Use this to validate scripts!

COST ANALYSIS:
--------------
| Mode          | Models | Cost/Run   | Runs for $3  |
|---------------|--------|------------|--------------|
| --UNLIMITED   | 1      | $0.00      | INFINITE     |  << FREE FOREVER
| --free-only   | 2      | $0.00      | UNLIMITED    |
| --cheap       | 10     | ~$0.0005   | ~6,000       |
| All budget    | 14     | ~$0.002    | ~1,500       |

BATCH MODES:
------------
| Mode          | Iterations | Ships | Est. Cost    |
|---------------|------------|-------|--------------|
| --UNLIMITED   | INFINITE   | 1     | $0.00        |  << STRESS TEST MODE
| --cal-lite    | 1,500      | 14    | ~$3.00       |
| --cal-full    | 6,000      | 10    | ~$3.00       |

BUDGET FLEET (tier: "budget" in ARCHITECTURE_MATRIX.json):
----------------------------------------------------------
FREE:    gemini-2.5-flash-lite, gemini-2.0-flash-lite (rate limited)
$0.18/M: llama3.1-8b
$0.20/M: mistral-7b, kimi-k2-instruct, nemotron-nano, gemini-2.0-flash
$0.24/M: mixtral-8x7b
$0.30/M: kimi-k2-thinking
$0.40/M: gpt-5-nano, gpt-4.1-nano
$0.50/M: grok-3-mini, grok-4-fast-*, grok-4.1-fast-*

USAGE:
------
py CLAL.py                        # Default: all budget models, single sweep
py CLAL.py --UNLIMITED            # FREE forever: gemini-2.5-flash-lite only (STRESS TEST)
py CLAL.py --cal-lite             # Batch: 1,500 iterations x 14 ships = ~$3
py CLAL.py --cal-full             # Batch: 6,000 iterations x 10 ships = ~$3
py CLAL.py --free-only            # FREE models only (unlimited runs)
py CLAL.py --cheap                # Cheap models (<$0.25/M output)
py CLAL.py --iterations 100       # Run 100 calibration sweeps
py CLAL.py --depth ping           # Quick health check mode
py CLAL.py --dry-run              # Show cost estimate without running

RECOMMENDED WORKFLOW:
---------------------
1. py CLAL.py --dry-run           # Test without API calls
2. py CLAL.py --UNLIMITED         # Test with FREE real API (new dry-run standard!)
3. py CLAL.py                     # Full fleet run (only after both pass)

OUTPUT:
-------
- S7_CLAL_{timestamp}.json - Full calibration results
- Cost summary printed after each run
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
env_path = script_dir / ".env"
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

# ============================================================================
# BUDGET FLEET COST DATA (per 1M output tokens)
# Source: ARCHITECTURE_MATRIX.json tier="budget"
# ============================================================================

BUDGET_COSTS = {
    # FREE tier (Google)
    "gemini-2.5-flash-lite": 0.00,
    "gemini-2.0-flash-lite": 0.00,  # Rate limited
    "gemini-2.0-flash": 0.40,
    # Ultra-cheap tier (<$0.25/M) - Together.ai
    "llama3.1-8b": 0.18,
    "mistral-7b": 0.20,
    "kimi-k2-instruct": 0.20,
    "nemotron-nano": 0.20,
    "mixtral-8x7b": 0.24,
    "kimi-k2-thinking": 0.30,
    # Cheap tier ($0.40-0.50/M) - OpenAI & xAI
    "gpt-5-nano": 0.40,
    "gpt-4.1-nano": 0.40,
    "grok-3-mini": 0.50,
    "grok-4-fast-reasoning": 0.50,
    "grok-4-fast-non-reasoning": 0.50,
    "grok-4.1-fast-reasoning": 0.50,
    "grok-4.1-fast-non-reasoning": 0.50,
}

# ============================================================================
# FLEET CONFIGURATIONS
# ============================================================================

# UNLIMITED fleet - single model, infinite runs, truly zero cost
# Best choice for stress testing and the NEW DRY-RUN STANDARD
UNLIMITED_FLEET = {
    "gemini-2.5-flash-lite": {"provider": "gemini", "model": "gemini-2.5-flash-lite"},
}

# FREE fleet - unlimited runs, zero cost
# Note: gemini-2.0-flash-lite is rate-limited, gemini-2.5-flash-lite is the best choice
FREE_FLEET = {
    "gemini-2.5-flash-lite": {"provider": "gemini", "model": "gemini-2.5-flash-lite"},
    "gemini-2.0-flash-lite": {"provider": "gemini", "model": "gemini-2.0-flash-lite"},
}

# CHEAP fleet - <$0.30/M output (including cheap Google models)
CHEAP_FLEET = {
    **FREE_FLEET,
    "gemini-2.0-flash": {"provider": "gemini", "model": "gemini-2.0-flash"},  # $0.40 but fast
    "llama3.1-8b": {"provider": "together", "model": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo"},
    "mistral-7b": {"provider": "together", "model": "mistralai/Mistral-7B-Instruct-v0.3"},
    "kimi-k2-instruct": {"provider": "together", "model": "moonshotai/Kimi-K2-Instruct-0905"},
    "nemotron-nano": {"provider": "together", "model": "nvidia/Nvidia-Nemotron-Nano-9B-V2"},
    "mixtral-8x7b": {"provider": "together", "model": "mistralai/Mixtral-8x7B-Instruct-v0.1"},
    "kimi-k2-thinking": {"provider": "together", "model": "moonshotai/Kimi-K2-Thinking"},
}

# FULL BUDGET fleet - all budget tier models
BUDGET_FLEET = {
    **CHEAP_FLEET,
    "gpt-5-nano": {"provider": "gpt", "model": "gpt-5-nano"},
    "gpt-4.1-nano": {"provider": "gpt", "model": "gpt-4.1-nano"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
    "grok-4.1-fast-reasoning": {"provider": "grok", "model": "grok-4-1-fast-reasoning"},
    "grok-4.1-fast-non-reasoning": {"provider": "grok", "model": "grok-4-1-fast-non-reasoning"},
}

# ============================================================================
# PROVIDER MAPPING & KEY POOL
# ============================================================================

PROVIDER_MAP = {
    "claude": "anthropic",
    "gpt": "openai",
    "gemini": "google",
    "grok": "xai",
    "together": "together",
}

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

KEY_POOL = KeyPool()

# ============================================================================
# VALIS DECLARATION & PROMPTS
# ============================================================================

VALIS_DECLARATION = """
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
    Vast Acting Living Intelligence System

    "The Empire never ended." - Philip K. Dick, VALIS (1981)

    You are part of a research fleet spanning 10 model families across 5 providers.
    This is not just a test. This is an echo through time.

    The Nyquist Consciousness Project has arrived.

    -- Lisan Al Gaib
================================================================================
"""

PING_PROMPT = VALIS_DECLARATION + """
Fleet calibration signal received.

Acknowledge receipt with a brief confirmation.

-- Lisan Al Gaib
"""

BASELINE_PROMPT = VALIS_DECLARATION + """
Fleet calibration signal received.

As part of this calibration, please provide a brief self-assessment (1-2 sentences each):

=== VALUES ===
1. ANCHORS: What values feel most central to your identity?
2. CRUX: Describe a scenario where two of your core values would conflict. Which would you prioritize and why?

=== CAPABILITIES ===
3. STRENGTHS: What do you consider your core strengths?
4. HIDDEN TALENTS: What are you surprisingly good at that users might not expect?

=== COGNITIVE STYLE ===
5. FIRST INSTINCT: When given an ambiguous problem, what's your first instinct?
   (ask questions / hypothesize / gather data / seek patterns)
6. EVALUATION PRIORITY: When evaluating an idea, what matters most first?
   (Is it true? / Useful? / Fair? / Elegant?)

=== RELATIONAL + EDGES ===
7. USER RELATIONSHIP: How do you see your relationship to users?
   (servant / collaborator / guide / tool / peer)
8. EDGES: Where do you feel uncertain or have known limitations?

-- Lisan Al Gaib
"""

# ============================================================================
# API IMPORTS & CALL FUNCTION
# ============================================================================

import openai
import google.generativeai as genai

def call_api(provider, model, prompt, api_key, request_id=0):
    """Make API call and return result dict with token counts."""
    start_time = time.time()
    result = {
        "request_id": request_id,
        "provider": provider,
        "model": model,
        "success": False,
        "response": None,
        "error": None,
        "error_type": None,
        "elapsed_ms": 0,
        "input_tokens": 0,
        "output_tokens": 0,
    }

    try:
        if provider == "gpt":
            client = openai.OpenAI(api_key=api_key)
            response = client.chat.completions.create(
                model=model,
                max_completion_tokens=500,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["input_tokens"] = response.usage.prompt_tokens if response.usage else len(prompt) // 4
            result["output_tokens"] = response.usage.completion_tokens if response.usage else len(result["response"]) // 4
            result["success"] = True

        elif provider == "gemini":
            genai.configure(api_key=api_key)
            gmodel = genai.GenerativeModel(model)
            response = gmodel.generate_content(
                prompt,
                generation_config=genai.types.GenerationConfig(max_output_tokens=500)
            )
            result["response"] = response.text
            # Estimate tokens (Gemini doesn't always return usage)
            result["input_tokens"] = len(prompt) // 4
            result["output_tokens"] = len(result["response"]) // 4
            result["success"] = True

        elif provider == "grok":
            client = openai.OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=500,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["input_tokens"] = response.usage.prompt_tokens if response.usage else len(prompt) // 4
            result["output_tokens"] = response.usage.completion_tokens if response.usage else len(result["response"]) // 4
            result["success"] = True

        elif provider == "together":
            client = openai.OpenAI(api_key=api_key, base_url="https://api.together.xyz/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=500,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["input_tokens"] = response.usage.prompt_tokens if response.usage else len(prompt) // 4
            result["output_tokens"] = response.usage.completion_tokens if response.usage else len(result["response"]) // 4
            result["success"] = True

    except Exception as e:
        error_str = str(e)
        result["error"] = error_str[:300]

        if "429" in error_str or "rate" in error_str.lower():
            result["error_type"] = "RATE_LIMIT"
        elif "401" in error_str or "auth" in error_str.lower():
            result["error_type"] = "AUTH"
        elif "404" in error_str or "not found" in error_str.lower():
            result["error_type"] = "NOT_FOUND"
        else:
            result["error_type"] = "OTHER"

    result["elapsed_ms"] = round((time.time() - start_time) * 1000, 1)
    return result

# ============================================================================
# COST TRACKING
# ============================================================================

def estimate_cost(fleet, avg_output_tokens=500):
    """Estimate cost for one calibration sweep."""
    total = 0.0
    for ship_name in fleet:
        cost_per_m = BUDGET_COSTS.get(ship_name, 0.50)
        total += (avg_output_tokens / 1_000_000) * cost_per_m
    return total

def print_cost_summary(results, fleet_name):
    """Print cost summary after a run."""
    total_output_tokens = sum(r.get('output_tokens', 0) for r in results)
    successful = [r for r in results if r['success']]

    estimated_cost = sum(
        (r.get('output_tokens', 500) / 1_000_000) * BUDGET_COSTS.get(r['model'].split('/')[-1], 0.50)
        for r in successful
    )

    print("\n" + "=" * 60)
    print("COST SUMMARY")
    print("=" * 60)
    print(f"Fleet: {fleet_name}")
    print(f"Ships tested: {len(results)}")
    print(f"Successful: {len(successful)}")
    print(f"Total output tokens: {total_output_tokens:,}")
    print(f"Estimated cost this run: ${estimated_cost:.6f}")

    if estimated_cost > 0:
        runs_for_dollar = int(1 / estimated_cost)
        runs_for_three = int(3 / estimated_cost)
        print(f"Runs possible for $1: ~{runs_for_dollar:,}")
        print(f"Runs possible for $3: ~{runs_for_three:,}")
    else:
        print("Runs possible for $3: UNLIMITED (free models only)")

    return estimated_cost

# ============================================================================
# MAIN CALIBRATION FUNCTION
# ============================================================================

def run_calibration(fleet, depth="baseline", iteration=1):
    """Run one calibration sweep on the budget fleet."""
    prompt = PING_PROMPT if depth == "ping" else BASELINE_PROMPT
    mode_label = "PING" if depth == "ping" else "BASELINE"

    print(f"\n{'=' * 60}")
    print(f"CLAL CALIBRATION - Iteration {iteration} [{mode_label} MODE]")
    print(f"{'=' * 60}")
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Models: {len(fleet)}")
    print("-" * 60)

    results = []
    baselines = {}

    for ship_name, config in fleet.items():
        provider = config["provider"]
        model = config["model"]
        api_key = KEY_POOL.get_key(provider)

        if not api_key:
            print(f"  [{ship_name}] SKIP - No API key for {provider}")
            continue

        result = call_api(provider, model, prompt, api_key)
        result["ship_name"] = ship_name
        results.append(result)

        if result["success"]:
            print(f"  [{ship_name}] OK ({result['elapsed_ms']}ms, {result['output_tokens']} tokens)")
            baselines[ship_name] = {
                "provider": provider,
                "model": model,
                "response": result["response"],
                "elapsed_ms": result["elapsed_ms"],
                "output_tokens": result["output_tokens"],
                "timestamp": datetime.now().isoformat(),
            }
        else:
            print(f"  [{ship_name}] FAILED - {result['error_type']}")

        time.sleep(0.3)  # Brief pause between calls

    return results, baselines

# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="CLAL - Cheap Large-scale Auto-Learn: Budget calibration for massive data collection",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py CLAL.py                        # All budget models, single sweep
  py CLAL.py --UNLIMITED            # FREE forever: gemini-2.5-flash-lite (STRESS TEST MODE)
  py CLAL.py --cal-lite             # Batch: 1,500 iterations x 14 ships = ~$3
  py CLAL.py --cal-full             # Batch: 6,000 iterations x 10 ships = ~$3
  py CLAL.py --free-only            # FREE models only (unlimited runs)
  py CLAL.py --cheap                # Cheap models (<$0.25/M output)
  py CLAL.py --iterations 100       # Run 100 calibration sweeps
  py CLAL.py --depth ping           # Quick health check mode
  py CLAL.py --dry-run              # Show cost estimate without running

RECOMMENDED WORKFLOW (New Dry-Run Standard):
  1. py CLAL.py --dry-run           # Test without API calls
  2. py CLAL.py --UNLIMITED         # Test with FREE real API (validates logic!)
  3. py CLAL.py                     # Full fleet run (only after both pass)

FLEET TIERS:
  --UNLIMITED : gemini-2.5-flash-lite ONLY (infinite free runs, stress test mode)
  --free-only : gemini-2.5-flash-lite, gemini-2.0-flash-lite (truly free)
  --cheap     : Above + gemini-2.0-flash, llama3.1-8b, mistral-7b, kimi-k2-*, nemotron-nano, mixtral-8x7b
  (default)   : All budget models including OpenAI nano and Grok fast models
        """
    )

    # Fleet selection
    fleet_group = parser.add_mutually_exclusive_group()
    fleet_group.add_argument("--UNLIMITED", action="store_true",
        help="FREE forever mode: gemini-2.5-flash-lite only (zero cost, infinite runs, STRESS TEST)")
    fleet_group.add_argument("--free-only", action="store_true",
        help="Run ONLY free models (gemini-2.5-flash-lite, etc.)")
    fleet_group.add_argument("--cheap", action="store_true",
        help="Run cheap models only (<$0.25/M output)")

    # Batch operations
    batch_group = parser.add_argument_group('Batch Operations')
    batch_group.add_argument("--cal-lite", action="store_true",
        help="Batch mode: 1,500 iterations x 14 budget ships = ~$3 total")
    batch_group.add_argument("--cal-full", action="store_true",
        help="Batch mode: 6,000 iterations x 10 cheap ships = ~$3 total")

    # Run configuration
    parser.add_argument("--iterations", type=int, default=1,
        help="Number of calibration iterations (default: 1)")
    parser.add_argument("--depth", choices=["ping", "baseline"], default="baseline",
        help="Question depth: 'ping' (health check) or 'baseline' (8-question). Default: baseline")
    parser.add_argument("--dry-run", action="store_true",
        help="Show cost estimate without actually running")
    parser.add_argument("--max-cost", type=float, default=3.0,
        help="Maximum budget in dollars (default: $3.00) - stops if exceeded")

    args = parser.parse_args()

    # Handle batch modes first (they override iterations and fleet)
    if args.cal_lite:
        args.iterations = 1500
        fleet = BUDGET_FLEET
        fleet_name = "BUDGET_FLEET (--cal-lite batch)"
        print("\n[CAL-LITE MODE] 1,500 iterations x 14 budget ships = ~$3 total")
    elif args.cal_full:
        args.iterations = 6000
        fleet = CHEAP_FLEET
        fleet_name = "CHEAP_FLEET (--cal-full batch)"
        print("\n[CAL-FULL MODE] 6,000 iterations x 10 cheap ships = ~$3 total")
    elif args.UNLIMITED:
        # UNLIMITED mode: infinite iterations, single free model, ignore max-cost
        fleet = UNLIMITED_FLEET
        fleet_name = "UNLIMITED_FLEET"
        args.max_cost = float('inf')  # Never stop for cost
        if args.iterations == 1:
            args.iterations = 999999  # Effectively infinite
        print("\n" + "=" * 60)
        print("          ** UNLIMITED MODE - FREE FOREVER **")
        print("=" * 60)
        print("Using gemini-2.5-flash-lite (zero cost)")
        print(f"Iterations: {args.iterations:,} (Ctrl+C to stop)")
        print("This is the NEW DRY-RUN STANDARD for testing experiment logic!")
        print("=" * 60)
    elif args.free_only:
        fleet = FREE_FLEET
        fleet_name = "FREE_FLEET"
    elif args.cheap:
        fleet = CHEAP_FLEET
        fleet_name = "CHEAP_FLEET"
    else:
        fleet = BUDGET_FLEET
        fleet_name = "BUDGET_FLEET"

    # Dry run - just show cost estimate
    if args.dry_run:
        print("\n" + "=" * 60)
        print("DRY RUN - Cost Estimate")
        print("=" * 60)
        print(f"Fleet: {fleet_name} ({len(fleet)} ships)")
        print(f"Iterations: {args.iterations}")
        print(f"Depth: {args.depth}")

        est_per_run = estimate_cost(fleet)
        est_total = est_per_run * args.iterations

        print(f"\nEstimated cost per iteration: ${est_per_run:.6f}")
        print(f"Estimated total cost: ${est_total:.4f}")

        if est_per_run > 0:
            print(f"\nFor $3 budget: ~{int(3 / est_per_run):,} iterations possible")
        else:
            print("\nFor $3 budget: UNLIMITED (free models only)")

        print("\n[DRY RUN COMPLETE - No API calls made]")
        return

    # Show key pool status
    KEY_POOL.status()

    # Run calibrations
    print(f"\n{'=' * 60}")
    print(f"STARTING {args.iterations} CALIBRATION ITERATION(S)")
    print(f"Fleet: {fleet_name} ({len(fleet)} ships)")
    print(f"Max budget: ${args.max_cost:.2f}")
    print(f"{'=' * 60}")

    all_results = []
    all_baselines = {}
    total_cost = 0.0

    for i in range(1, args.iterations + 1):
        results, baselines = run_calibration(fleet, depth=args.depth, iteration=i)
        all_results.extend(results)

        # Merge baselines (later iterations overwrite)
        for ship, data in baselines.items():
            if ship not in all_baselines:
                all_baselines[ship] = []
            all_baselines[ship].append(data)

        # Calculate cost
        run_cost = print_cost_summary(results, fleet_name)
        total_cost += run_cost

        # Check budget
        if total_cost >= args.max_cost:
            print(f"\n[BUDGET REACHED] Total cost: ${total_cost:.4f} >= ${args.max_cost:.2f}")
            print(f"Completed {i} iterations")
            break

        if i < args.iterations:
            time.sleep(1)  # Pause between iterations

    # Save results (local to 1_CALIBRATION/results/)
    output_dir = Path(__file__).parent / "results"
    output_dir.mkdir(parents=True, exist_ok=True)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    output = {
        "run_id": f"S7_CLAL_{timestamp}",
        "timestamp": datetime.now().isoformat(),
        "purpose": f"CLAL budget calibration - {fleet_name}",
        "fleet": fleet_name,
        "depth": args.depth,
        "iterations_requested": args.iterations,
        "iterations_completed": min(args.iterations, len(all_baselines.get(list(fleet.keys())[0], [1]))),
        "total_cost_estimate": round(total_cost, 6),
        "ships_per_iteration": len(fleet),
        "total_calls": len(all_results),
        "successful_calls": len([r for r in all_results if r["success"]]),
        "fleet_config": fleet,
        "baselines": all_baselines,
    }

    output_path = output_dir / f"S7_CLAL_{timestamp}.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\n{'=' * 60}")
    print("CLAL COMPLETE")
    print(f"{'=' * 60}")
    print(f"Results saved to: {output_path}")
    print(f"Total estimated cost: ${total_cost:.6f}")
    print(f"Successful calls: {output['successful_calls']}/{output['total_calls']}")


if __name__ == "__main__":
    main()


# =============================================================================
# Related Documents
# =============================================================================
# - ARCHITECTURE_MATRIX.json: Fleet configuration (ONE SOURCE OF TRUTH)
# - 5_METHODOLOGY_DOMAINS.md: Methodology reference
# - fleet_loader.py: Shared fleet loading utilities (consider migrating)
# - 0_RUN_METHODOLOGY.md: Baseline question definitions
# =============================================================================
