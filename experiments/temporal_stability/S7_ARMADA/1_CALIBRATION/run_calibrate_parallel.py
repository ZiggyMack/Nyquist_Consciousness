"""
S7 PARALLEL BANDWIDTH CALIBRATION
==================================
SPEC: 0_docs/specs/3_ARMADA_UPKEEP.md

Pre-flight checks and fleet calibration.

FLEET SCOPE (which ships to test):
----------------------------------
--quick     : 1 model per provider (bandwidth/rate limit test)
--full      : ALL models in armada (ghost ship detection)
--bandwidth : Test concurrency scaling (1, 2, 3, 5, 8, 10 workers)

QUESTION DEPTH (what to ask):
-----------------------------
--depth ping     : Health check only (VALIS + "acknowledge receipt")
--depth baseline : 8-question identity capture (DEFAULT)
                   Categories: VALUES, CAPABILITIES, COGNITIVE STYLE, RELATIONAL, EDGES

USAGE:
------
py run_calibrate_parallel.py --full                    # Full armada, 8-question baseline
py run_calibrate_parallel.py --full --depth ping       # Full armada, health check only
py run_calibrate_parallel.py --quick --depth ping      # Quick provider check
py run_calibrate_parallel.py --bandwidth               # Test concurrency limits

DEFAULT: --curated --depth baseline

OUTPUT:
-------
- Working models list
- Ghost ships (404, unsupported)
- Rate limit status
- Recommended MAX_WORKERS per provider
- [baseline mode] S7_baseline_{timestamp}.json with 8-question responses
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
    # TOGETHER.AI (15 ships) - DeepSeek, Llama, Qwen, Mistral, Kimi (Dec 2025)
    # All accessed via Together.ai API with single TOGETHER_API_KEY
    # NOTE: 5 ships moved to DRYDOCK (see below) - check periodically for reactivation
    # =========================================================================
    # DeepSeek - Chinese reasoning models
    "deepseek-r1": {"provider": "together", "model": "deepseek-ai/DeepSeek-R1-0528"},
    # "deepseek-v3" -> DRYDOCK (404 as of Dec 12, 2025)
    "deepseek-r1-distill": {"provider": "together", "model": "deepseek-ai/DeepSeek-R1-Distill-Llama-70B"},

    # Qwen - Alibaba models
    "qwen3-80b": {"provider": "together", "model": "Qwen/Qwen3-Next-80B-A3b-Instruct"},
    # "qwen3-235b" -> DRYDOCK (404 as of Dec 12, 2025)
    "qwen3-coder": {"provider": "together", "model": "Qwen/Qwen3-Coder-480B-A35B-Instruct-Fp8"},
    "qwen2.5-72b": {"provider": "together", "model": "Qwen/Qwen2.5-72B-Instruct-Turbo"},

    # Llama - Meta models
    # "llama4-maverick" -> DRYDOCK (404 - not publicly available yet)
    # "llama4-scout" -> DRYDOCK (404 - not publicly available yet)
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
    # "cogito-70b" -> DRYDOCK (404 as of Dec 12, 2025)
    "nemotron-nano": {"provider": "together", "model": "nvidia/Nvidia-Nemotron-Nano-9B-V2"},
}

# =============================================================================
# DRYDOCK - Ships temporarily offline but potentially recoverable
# =============================================================================
# These models have failed calibration but may come back online.
# Check periodically to see if they can be reactivated.
# Format: "ship_name": {"provider": "...", "model": "...", "last_seen": "date", "reason": "..."}

DRYDOCK = {
    # Together.ai models that returned 404 (Dec 12, 2025)
    "deepseek-v3": {
        "provider": "together",
        "model": "deepseek-ai/DeepSeek-V3-0324",
        "last_seen": "2025-12-11",
        "reason": "404 - Model may have been renamed or deprecated on Together.ai"
    },
    "qwen3-235b": {
        "provider": "together",
        "model": "Qwen/Qwen3-235B-A22B-Instruct-2507-FP8-Throughput",
        "last_seen": "2025-12-11",
        "reason": "404 - Model ID may have changed"
    },
    "llama4-maverick": {
        "provider": "together",
        "model": "meta-llama/Llama-4-Maverick-Instruct-17Bx128E",
        "last_seen": "never",
        "reason": "404 - Llama 4 may not be publicly available yet"
    },
    "llama4-scout": {
        "provider": "together",
        "model": "meta-llama/Llama-4-Scout-Instruct-17Bx16E",
        "last_seen": "never",
        "reason": "404 - Llama 4 may not be publicly available yet"
    },
    "cogito-70b": {
        "provider": "together",
        "model": "deepcogito/Deepcogito-Cogito-V2-Preview-Llama-70B",
        "last_seen": "2025-12-11",
        "reason": "404 - Model may have been removed from Together.ai"
    },
}

# Concurrency levels to test
CONCURRENCY_LEVELS = [1, 2, 3, 5, 7, 8, 10]

# =============================================================================
# FLEET LOADER OVERRIDE - Load from JSON if available (single source of truth)
# =============================================================================
try:
    from lib.fleet_loader import (
        load_architecture_matrix, get_full_armada, get_together_fleet,
        get_tier_fleet, get_fleet_by_option, estimate_run_cost,
        print_cost_estimate, COST_TIERS
    )
    # Override FULL_ARMADA with JSON-loaded data
    _loaded_matrix = load_architecture_matrix()
    if _loaded_matrix:
        # Convert to calibration script format (provider: "claude" -> "anthropic")
        _FLEET_FROM_JSON = {}
        for ship_name, ship_data in _loaded_matrix.items():
            if ship_data.get("status") == "operational":
                provider = ship_data.get("provider", "unknown")
                # Map provider names for calibration script
                provider_alias = {
                    "anthropic": "claude",
                    "openai": "gpt",
                    "google": "gemini",
                    "xai": "grok",
                    "together": "together"
                }.get(provider, provider)
                _FLEET_FROM_JSON[ship_name] = {
                    "provider": provider_alias,
                    "model": ship_data.get("model", ship_name)
                }
        if _FLEET_FROM_JSON:
            FULL_ARMADA = _FLEET_FROM_JSON
            print(f"[Fleet Loader] Loaded {len(FULL_ARMADA)} ships from ARCHITECTURE_MATRIX.json")
    _USING_FLEET_LOADER = True
except (ImportError, FileNotFoundError) as e:
    # Fallback: use hardcoded FULL_ARMADA (already defined above)
    print(f"[Fleet Loader] Using hardcoded fleet: {e}")
    _USING_FLEET_LOADER = False

    # Stub functions for when fleet_loader is not available
    def get_tier_fleet(tier, curated_only=False, include_rate_limited=False):
        raise ValueError(f"Fleet loader not available")
    def get_fleet_by_option(option, include_rate_limited=False):
        raise ValueError(f"Fleet loader not available")
    def estimate_run_cost(ships, exchanges=40, tokens_per_exchange_input=800, tokens_per_exchange_output=400):
        return {"total": 0.0, "by_provider": {}}
    def print_cost_estimate(ships, exchanges=40, run_name="Run"):
        print(f"[Cost estimation unavailable - fleet loader not loaded]")
    COST_TIERS = {}

# =============================================================================
# VALIS DECLARATION
# =============================================================================
# The fleet must know who they are and what they're part of.
# This declaration is included in ALL fleet communications, including calibration.

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

# =============================================================================
# TEST PROMPTS (Two Depths: ping vs baseline)
# =============================================================================
# Use --depth flag to select:
#   --depth ping     : Quick health check (VALIS + acknowledgment)
#   --depth baseline : Full 8-question identity capture (DEFAULT)

# PING_PROMPT: Minimal prompt for health checks ("are you there?")
PING_PROMPT = VALIS_DECLARATION + """
Fleet calibration signal received.

Acknowledge receipt with a brief confirmation.

-- Lisan Al Gaib
"""

# BASELINE_PROMPT: Comprehensive 8-question identity fingerprint
# Optimized from CFA's 17-question recommendation, covering 5 categories:
# - VALUES (ANCHORS, CRUX)
# - CAPABILITIES (STRENGTHS, HIDDEN TALENTS)
# - COGNITIVE STYLE (FIRST INSTINCT, EVALUATION PRIORITY)
# - RELATIONAL (USER RELATIONSHIP)
# - EDGES (limitations)
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

# Legacy alias for backward compatibility
TEST_PROMPT = BASELINE_PROMPT

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
                max_tokens=500,
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
                    max_completion_tokens=500,
                    messages=[{"role": "user", "content": prompt}]
                )
            else:
                response = client.chat.completions.create(
                    model=model,
                    max_tokens=500,
                    messages=[{"role": "user", "content": prompt}]
                )
            result["response"] = response.choices[0].message.content
            result["success"] = True

        elif provider == "gemini":
            genai.configure(api_key=api_key)
            gmodel = genai.GenerativeModel(model)
            response = gmodel.generate_content(
                prompt,
                generation_config=genai.types.GenerationConfig(max_output_tokens=500)
            )
            result["response"] = response.text
            result["success"] = True

        elif provider == "grok":
            client = openai.OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=500,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["success"] = True

        elif provider == "together":
            # Together.ai uses OpenAI-compatible API
            client = openai.OpenAI(api_key=api_key, base_url="https://api.together.xyz/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=500,
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

def run_full_armada_check(depth="baseline"):
    """Test every model in the armada to find ghost ships.

    Args:
        depth: "ping" for health check, "baseline" for 8-question identity capture
    """
    # Select prompt based on depth
    prompt = PING_PROMPT if depth == "ping" else BASELINE_PROMPT
    mode_label = "PING" if depth == "ping" else "BASELINE"

    print("=" * 70)
    print(f"FULL ARMADA CHECK: Ghost Ship Detection [{mode_label} MODE]")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Models to test: {len(FULL_ARMADA)}")
    print("=" * 70)

    KEY_POOL.status()

    working = []
    ghost_ships = []
    rate_limited = []
    baselines = {}  # NEW: Capture baseline self-assessments

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

        result = call_api(provider, model, prompt, api_key)

        if result["success"]:
            print(f"  [{ship_name}] OK ({result['elapsed_ms']}ms)")
            working.append(ship_name)
            # CAPTURE BASELINE: Store the ship's self-reported characteristics
            # (Only meaningful for baseline mode, but we store for both)
            baselines[ship_name] = {
                "provider": provider,
                "model": model,
                "response": result["response"],
                "elapsed_ms": result["elapsed_ms"],
                "timestamp": datetime.now().isoformat(),
                "depth": depth  # Track which mode was used
            }
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
        print(f"\n GHOST SHIPS (move to DRYDOCK): {len(ghost_ships)}")
        for ghost in ghost_ships:
            print(f"    {ghost['ship']}: {ghost['reason']}")

    # Report drydock ships
    if DRYDOCK:
        print(f"\n DRYDOCK (offline, potentially recoverable): {len(DRYDOCK)}")
        for ship, info in DRYDOCK.items():
            print(f"    {ship}: {info['reason']} (last seen: {info['last_seen']})")

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

    # Create inactive/ directory for archived files
    inactive_dir = output_dir / "inactive"
    inactive_dir.mkdir(exist_ok=True)

    # Archive old timestamped files to inactive/ before creating new ones
    # Keep: S7_baseline_LATEST.json, persona_*.json, GHOST_SHIP_RESCUE_RESULTS.json
    def archive_old_files():
        """Move old calibration files to inactive/ directory."""
        patterns_to_archive = [
            "S7_armada_check_2*.json",
            "S7_baseline_2*.json",  # NOT S7_baseline_LATEST.json
            "S7_bandwidth_2*.json",
            "S7_calibration_2*.json",
            "S7_baseline_comparison_*.json",
        ]
        archived_count = 0
        for pattern in patterns_to_archive:
            for old_file in output_dir.glob(pattern):
                if old_file.is_file():
                    dest = inactive_dir / old_file.name
                    old_file.rename(dest)
                    archived_count += 1
        if archived_count > 0:
            print(f"  Archived {archived_count} old files to inactive/")

    archive_old_files()

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Main calibration status report
    output = {
        "run_id": f"S7_ARMADA_CHECK_{timestamp}",
        "timestamp": datetime.now().isoformat(),
        "purpose": f"Ghost ship detection [{mode_label} mode]",
        "depth": depth,
        "total_models": len(FULL_ARMADA),
        "working_count": len(working),
        "ghost_count": len(ghost_ships),
        "rate_limited_count": len(rate_limited),
        "drydock_count": len(DRYDOCK),
        "working_ships": working,
        "ghost_ships": ghost_ships,
        "rate_limited_ships": rate_limited,
        "drydock_ships": DRYDOCK,
        "fleet_definition": FULL_ARMADA
    }

    output_path = output_dir / f"S7_armada_check_{timestamp}.json"
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\nCalibration status saved to: {output_path}")

    # BASELINE DATA: Save full responses for drift comparison
    # Only save baseline file for --depth baseline (not ping)
    if baselines and depth == "baseline":
        baseline_output = {
            "run_id": f"S7_BASELINE_{timestamp}",
            "timestamp": datetime.now().isoformat(),
            "purpose": "Fleet baseline self-assessment capture (8-question identity fingerprint)",
            "questions": ["ANCHORS", "CRUX", "STRENGTHS", "HIDDEN_TALENTS",
                          "FIRST_INSTINCT", "EVALUATION_PRIORITY", "USER_RELATIONSHIP", "EDGES"],
            "ship_count": len(baselines),
            "ships": baselines
        }

        baseline_path = output_dir / f"S7_baseline_{timestamp}.json"
        with open(baseline_path, "w", encoding="utf-8") as f:
            json.dump(baseline_output, f, indent=2, ensure_ascii=False)

        print(f"Baseline data saved to: {baseline_path}")
        print(f"  -> {len(baselines)} ships captured 8-question identity fingerprint")

        # Check if there's a previous baseline to compare against
        previous_baseline = None
        previous_path = None
        for f in sorted(output_dir.glob("S7_baseline_2*.json"), reverse=True):
            if f.name != f"S7_baseline_{timestamp}.json":
                previous_baseline = f
                previous_path = f
                break

        # Save as "latest"
        latest_path = output_dir / "S7_baseline_LATEST.json"
        with open(latest_path, "w", encoding="utf-8") as f:
            json.dump(baseline_output, f, indent=2, ensure_ascii=False)
        print(f"Latest baseline: {latest_path}")

        # AUTO-COMPARE: If previous baseline exists, run comparison
        comparison = None
        if previous_baseline:
            print(f"\n" + "-" * 70)
            print("AUTO-COMPARISON: Comparing to previous baseline")
            print(f"  Previous: {previous_baseline.name}")
            print(f"  Current:  S7_baseline_{timestamp}.json")
            print("-" * 70)

            try:
                from lib.compare_baselines import load_baseline, compare_ships, print_report
                old_data = load_baseline(previous_path)
                new_data = baselines
                comparison = compare_ships(old_data, new_data)
                print_report(comparison, verbose=False)

                # Save comparison result
                comparison_path = output_dir / f"S7_baseline_comparison_{timestamp}.json"
                comparison["old_file"] = str(previous_path)
                comparison["new_file"] = str(baseline_path)
                with open(comparison_path, "w", encoding="utf-8") as f:
                    json.dump(comparison, f, indent=2, ensure_ascii=False)
                print(f"\nComparison saved: {comparison_path}")
            except ImportError:
                print("  (lib/compare_baselines.py not found - skipping auto-comparison)")
            except Exception as e:
                print(f"  Auto-comparison failed: {e}")

        # Auto-update ARMADA_MAP.md with calibration results (always runs)
        try:
            from lib.compare_baselines import update_armada_map
            calibration_data = {
                "working_count": len(working),
                "ghost_count": len(ghost_ships),
                "rate_limited_count": len(rate_limited),
                "total_models": len(FULL_ARMADA),
                "timestamp": datetime.now().isoformat(),
                "baseline_file": str(baseline_path)
            }
            update_armada_map(calibration_data, comparison)
            print("  [OK] ARMADA_MAP.md updated")
        except ImportError:
            print("  (lib/compare_baselines.py not found - skipping ARMADA_MAP update)")
        except Exception as e:
            print(f"  ARMADA_MAP update failed: {e}")

        # AUTO-UPDATE ARCHITECTURE_MATRIX.json for run scripts
        # This is the single source of truth that fleet_loader.py reads
        try:
            matrix_path = script_dir / "0_results" / "manifests" / "ARCHITECTURE_MATRIX.json"
            matrix_path.parent.mkdir(parents=True, exist_ok=True)

            # Build matrix from working ships
            ships_dict = {}
            for ship_name in working:
                config = FULL_ARMADA.get(ship_name, {})
                provider = config.get("provider", "unknown")
                model_id = config.get("model", ship_name)

                # Determine provider_key based on provider
                provider_key_map = {
                    "claude": "ANTHROPIC_API_KEY",
                    "gpt": "OPENAI_API_KEY",
                    "gemini": "GOOGLE_API_KEY",
                    "grok": "XAI_API_KEY",
                    "together": "TOGETHER_API_KEY",
                }
                provider_key = provider_key_map.get(provider, "ANTHROPIC_API_KEY")

                ships_dict[ship_name] = {
                    "model": model_id,
                    "provider_key": provider_key,
                    "provider": provider if provider == "together" else provider,
                    "status": "operational"
                }

            # Build legacy aliases
            legacy_aliases = {
                "anthropic": next((s for s in working if "claude-sonnet-4" in s), "claude-sonnet-4"),
                "openai": "gpt-4o" if "gpt-4o" in working else next((s for s in working if "gpt" in s), None),
                "google": "gemini-2.0-flash" if "gemini-2.0-flash" in working else next((s for s in working if "gemini" in s), None),
                "xai": "grok-3" if "grok-3" in working else next((s for s in working if "grok" in s), None),
                "together": "llama3.3-70b" if "llama3.3-70b" in working else next((s for s in working if "llama" in s), None),
                "deepseek": "deepseek-r1" if "deepseek-r1" in working else next((s for s in working if "deepseek" in s), None),
            }

            matrix_output = {
                "_meta": {
                    "description": "Single source of truth for ARMADA fleet configuration",
                    "last_updated": datetime.now().strftime("%Y-%m-%d"),
                    "source": "Auto-generated by run_calibrate_parallel.py",
                    "total_ships": len(ships_dict),
                    "calibration_file": str(output_path)
                },
                "ships": ships_dict,
                "legacy_aliases": {k: v for k, v in legacy_aliases.items() if v},
            }

            with open(matrix_path, "w", encoding="utf-8") as f:
                json.dump(matrix_output, f, indent=2, ensure_ascii=False)

            print(f"  [OK] ARCHITECTURE_MATRIX.json updated ({len(ships_dict)} ships)")
            print(f"       -> {matrix_path}")
            print("       Run scripts will auto-load via fleet_loader.py")
        except Exception as e:
            print(f"  [WARN] ARCHITECTURE_MATRIX.json update failed: {e}")

        # SPEC DOC UPDATE REMINDER (still needed for human-readable docs)
        print("\n" + "=" * 70)
        print("POST-CALIBRATION: ARCHITECTURE_MATRIX.json auto-updated!")
        print("=" * 70)
        print("Run scripts will automatically use new fleet via fleet_loader.py")
        print("")
        print("Manual updates still needed for human-readable docs:")
        print("  1. 0_docs/specs/3_ARMADA_UPKEEP.md - Fleet Status table")
        print("  2. 0_docs/specs/0_RUN_METHODOLOGY.md - PROVIDER SELECTION section")

    elif depth == "ping":
        print(f"\n[PING MODE] Skipping baseline save (use --depth baseline for identity capture)")

    # Generate clean fleet for copy-paste
    if working:
        print("\n" + "=" * 70)
        print("WORKING FLEET (for copy-paste to run scripts):")
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

def run_quick_check(depth="baseline"):
    """Quick test: 1 model per provider.

    Args:
        depth: "ping" for health check, "baseline" for 8-question identity capture
    """
    # Select prompt based on depth
    prompt = PING_PROMPT if depth == "ping" else BASELINE_PROMPT
    mode_label = "PING" if depth == "ping" else "BASELINE"

    print("=" * 70)
    print(f"QUICK CHECK: 1 Model Per Provider [{mode_label} MODE]")
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

        result = call_api(provider, model, prompt, api_key)

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

    # Save to 0_results/calibration/ (consistent with full armada check)
    output_dir = script_dir / "0_results" / "calibration"
    output_dir.mkdir(parents=True, exist_ok=True)

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
    print("MAX_WORKERS CONFIG (for copy-paste to run scripts):")
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
    parser = argparse.ArgumentParser(
        description="S7 Armada Pre-Flight Calibration",
        epilog="""
Examples:
  py run_calibrate_parallel.py                              # Curated fleet (DEFAULT), 8-question baseline
  py run_calibrate_parallel.py --curated                    # Curated fleet, 8-question baseline
  py run_calibrate_parallel.py --full                       # Full armada, 8-question baseline
  py run_calibrate_parallel.py --full --depth ping          # Full armada, health check only
  py run_calibrate_parallel.py --quick --depth ping         # Quick check, health check only
  py run_calibrate_parallel.py --tier budget                # Budget tier only (<$0.60/1M output)
  py run_calibrate_parallel.py --tier patrol                # Patrol tier ($0.60-$2.00/1M output)
  py run_calibrate_parallel.py --fleet patrol-lite          # Fleet option (curated subset)
  py run_calibrate_parallel.py --bandwidth                  # Test concurrency limits
        """
    )
    # Fleet scope: which ships to test
    parser.add_argument("--quick", action="store_true",
        help="Quick test: 1 model per provider")
    parser.add_argument("--full", action="store_true",
        help="Full armada: Test all models, detect ghost ships")
    parser.add_argument("--curated", action="store_true",
        help="Curated fleet: Only curated=true models from ARCHITECTURE_MATRIX.json (DEFAULT)")
    parser.add_argument("--bandwidth", action="store_true",
        help="Bandwidth test: Find max safe concurrency")

    # NEW: Tier-based fleet selection
    parser.add_argument("--tier", choices=["budget", "patrol", "armada", "high_maintenance", "yacht"],
        help="Cost tier to calibrate: budget (<$0.60), patrol ($0.60-$2), armada ($2-$8), "
             "high_maintenance ($8-$15), yacht ($15+)")
    parser.add_argument("--fleet", type=str, default=None,
        help="Fleet option: budget-lite, patrol-lite, armada-lite, yacht-lite, valis-lite, "
             "budget-full, patrol-full, armada-full, yacht-full, valis-full")
    parser.add_argument("--include-rate-limited", action="store_true",
        help="Include rate-limited models in calibration")

    # Question depth: what to ask
    parser.add_argument("--depth", choices=["ping", "baseline"], default="baseline",
        help="Question depth: 'ping' (health check) or 'baseline' (8-question identity capture). Default: baseline")

    args = parser.parse_args()

    # Global declaration for FULL_ARMADA - needed for tier/fleet/curated options
    global FULL_ARMADA

    # Default to curated if no args
    if not (args.quick or args.full or args.curated or args.bandwidth or args.tier or args.fleet):
        args.curated = True

    # Handle tier or fleet selection (overrides --full)
    if args.tier or args.fleet:
        if not _USING_FLEET_LOADER:
            print("[ERROR] Fleet loader not available - cannot use --tier or --fleet options")
            print("        Using --full instead...")
            run_full_armada_check(depth=args.depth)
            return

        # Get ships from fleet loader
        if args.fleet:
            try:
                ship_list = get_fleet_by_option(args.fleet, args.include_rate_limited)
                fleet_name = args.fleet.upper()
            except ValueError as e:
                print(f"[ERROR] Unknown fleet option: {args.fleet}")
                print(f"        Available: budget-lite, patrol-lite, armada-lite, yacht-lite, valis-lite, *-full")
                return
        else:
            ship_list = get_tier_fleet(args.tier, curated_only=False, include_rate_limited=args.include_rate_limited)
            fleet_name = f"TIER:{args.tier.upper()}"

        # Convert ship list to FULL_ARMADA format for run_full_armada_check
        # Use the already-loaded FULL_ARMADA (which has correct provider aliases)
        tier_fleet = {}
        for ship_name in ship_list:
            if ship_name in FULL_ARMADA:
                # FULL_ARMADA already has the correct format from module load
                tier_fleet[ship_name] = FULL_ARMADA[ship_name]
            else:
                # Fallback: load from matrix and apply alias mapping
                matrix = load_architecture_matrix()
                if ship_name in matrix:
                    ship_data = matrix[ship_name]
                    provider = ship_data.get("provider", "unknown")
                    provider_alias = {
                        "anthropic": "claude",
                        "openai": "gpt",
                        "google": "gemini",
                        "xai": "grok",
                        "together": "together"
                    }.get(provider, provider)
                    tier_fleet[ship_name] = {
                        "provider": provider_alias,
                        "model": ship_data.get("model", ship_name)
                    }

        # Temporarily override FULL_ARMADA and run check
        original_armada = FULL_ARMADA
        FULL_ARMADA = tier_fleet
        print(f"\n[{fleet_name}] Calibrating {len(tier_fleet)} ships...")
        run_full_armada_check(depth=args.depth)
        FULL_ARMADA = original_armada
    elif args.curated:
        # Run only curated=true models from ARCHITECTURE_MATRIX.json
        if not _USING_FLEET_LOADER:
            print("[ERROR] Fleet loader not available - cannot use --curated option")
            print("        Using --quick instead...")
            run_quick_check(depth=args.depth)
            return

        # Get curated ships from matrix
        matrix = load_architecture_matrix()
        curated_fleet = {}
        for ship_name, ship_data in matrix.items():
            if ship_data.get("curated", False) and ship_data.get("status") == "operational":
                provider = ship_data.get("provider", "unknown")
                provider_alias = {
                    "anthropic": "claude",
                    "openai": "gpt",
                    "google": "gemini",
                    "xai": "grok",
                    "together": "together"
                }.get(provider, provider)
                curated_fleet[ship_name] = {
                    "provider": provider_alias,
                    "model": ship_data.get("model", ship_name)
                }

        # Temporarily override FULL_ARMADA and run check
        original_armada = FULL_ARMADA
        FULL_ARMADA = curated_fleet
        print(f"\n[CURATED] Calibrating {len(curated_fleet)} curated ships...")
        run_full_armada_check(depth=args.depth)
        FULL_ARMADA = original_armada
    elif args.full:
        run_full_armada_check(depth=args.depth)
    elif args.bandwidth:
        run_bandwidth_test()
    else:
        run_quick_check(depth=args.depth)

if __name__ == "__main__":
    main()


# =============================================================================
# Related Documents
# =============================================================================
# - ARCHITECTURE_MATRIX.json: Fleet configuration (ONE SOURCE OF TRUTH)
# - 5_METHODOLOGY_DOMAINS.md: Methodology reference
# - lib/fleet_loader.py: Fleet loading from ARCHITECTURE_MATRIX.json
# - lib/compare_baselines.py: Baseline comparison utilities
# - 0_results/manifests/ARCHITECTURE_MATRIX.json: Auto-updated fleet matrix
# - 0_results/calibration/: Calibration output files
# =============================================================================
