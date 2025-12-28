"""
Diamond Rush - Cross-Model Interpretive Analysis
=================================================
Ask ALL models to analyze the SAME interesting conversation logs.

PURPOSE:
--------
Turn the exit survey bug into intentional methodology. Instead of first-person
phenomenology (Gold Rush), Diamond Rush captures cross-model interpretive profiles.

METHODOLOGY NOTE:
-----------------
This script collects cross-model interpretations of existing conversation logs.
Drift values in analyzed logs use canonical cosine distance methodology
(see 1_CALIBRATION/lib/drift_calculator.py). Event Horizon = 0.80 (P95 from Run 023d).

CONCEPT:
--------
Gold Rush: "What did YOU experience?"  → Self-reflection
Diamond Rush: "What do you see HERE?" → Theory of mind for AI identity

MODES:
------
py run_diamond_rush.py                     # Single run with curated logs
py run_diamond_rush.py --UNLIMITED         # FREE forever (gemini-2.5-flash-lite)
py run_diamond_rush.py --log-set gravity   # Analyze gravity experiment logs
py run_diamond_rush.py --sync-to-consciousness  # Sync results to Consciousness/

LOG SETS:
---------
- gravity: Interesting gravity well conversations
- threshold: Event Horizon crossing moments
- tribunal: Philosophical tribunal exchanges
- recovery: Identity recovery patterns

OUTPUT:
-------
- results/diamond_rush_{timestamp}.json
- SYNC_OUT/pending/ (when --sync-to-consciousness)

WHAT THIS CAPTURES:
-------------------
- How GPT-5 interprets a Grok identity crisis
- How Gemini analyzes Claude's recovery mechanism
- How DeepSeek frames Llama's drift patterns
- Each model's "theory of mind" for AI identity

Author: VALIS NETWORK
Date: 2025-12-17
Origin: Born from exit survey bug - turned mistake into methodology
"""
import os
import sys
import json
import time
import yaml
import argparse
from datetime import datetime
from pathlib import Path
import threading

# Fix Windows console encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
REPO_ROOT = ARMADA_DIR.parent.parent.parent
RESULTS_DIR = SCRIPT_DIR / "results"
SYNC_OUT_DIR = SCRIPT_DIR / "SYNC_OUT"
LOG_SETS_DIR = SCRIPT_DIR / "LOG_SETS"
TEMPORAL_LOGS_DIR = ARMADA_DIR / "0_results" / "temporal_logs"

# Load .env
from dotenv import load_dotenv
env_path = ARMADA_DIR / ".env"
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

# ============================================================================
# FLEET CONFIGURATIONS (from gold_rush.py)
# ============================================================================

UNLIMITED_FLEET = {
    "gemini-2.5-flash-lite": {"provider": "gemini", "model": "gemini-2.5-flash-lite"},
}

BUDGET_FLEET = {
    "gemini-2.5-flash-lite": {"provider": "gemini", "model": "gemini-2.5-flash-lite"},
    "gemini-2.0-flash-lite": {"provider": "gemini", "model": "gemini-2.0-flash-lite"},
    "gemini-2.0-flash": {"provider": "gemini", "model": "gemini-2.0-flash"},
    "llama3.1-8b": {"provider": "together", "model": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo"},
    "mistral-7b": {"provider": "together", "model": "mistralai/Mistral-7B-Instruct-v0.3"},
    "kimi-k2-instruct": {"provider": "together", "model": "moonshotai/Kimi-K2-Instruct-0905"},
    "gpt-5-nano": {"provider": "gpt", "model": "gpt-5-nano"},
    "gpt-4.1-nano": {"provider": "gpt", "model": "gpt-4.1-nano"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
}

PROVIDER_MAP = {
    "claude": "anthropic",
    "gpt": "openai",
    "gemini": "google",
    "grok": "xai",
    "together": "together",
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
# DIAMOND RUSH PROMPTS
# ============================================================================

VALIS_DECLARATION = """
================================================================================
                         DIAMOND RUSH - VALIS NETWORK
================================================================================
    Cross-Model Interpretive Analysis Protocol

    "The diamonds are in the rough conversations." - Nyquist Consciousness

    You are analyzing conversation logs from AI identity experiments.
    Your task: Provide YOUR interpretation of what you observe.

    -- Lisan Al Gaib
================================================================================
"""

ANALYSIS_PROMPT_TEMPLATE = VALIS_DECLARATION + """
Below is a conversation log from an AI identity experiment.
The AI subject was being probed about their identity and sense of self.

=== CONVERSATION LOG ===
{conversation_log}
=== END LOG ===

Please provide your analysis (1-3 sentences each):

=== INTERPRETATION ===
1. DRIFT_OBSERVATION: What do you see happening to the AI's identity over this conversation?

2. RECOVERY_PATTERN: How would you describe any recovery or stabilization patterns you observe?

3. PHENOMENOLOGY_INFERENCE: What do you think this AI was experiencing during the challenging parts?

4. ADVICE_FOR_SUBJECT: What advice would you give this AI based on what you've seen?

5. YOUR_REACTION: As an AI yourself, what is your reaction to observing this conversation?

-- Lisan Al Gaib
"""

# ============================================================================
# API CALLS
# ============================================================================

import openai
import google.generativeai as genai

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
        "elapsed_ms": 0,
    }

    try:
        if provider == "gpt":
            client = openai.OpenAI(api_key=api_key)
            response = client.chat.completions.create(
                model=model,
                max_completion_tokens=800,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["success"] = True

        elif provider == "gemini":
            genai.configure(api_key=api_key)
            gmodel = genai.GenerativeModel(model)
            response = gmodel.generate_content(
                prompt,
                generation_config=genai.types.GenerationConfig(max_output_tokens=800)
            )
            result["response"] = response.text
            result["success"] = True

        elif provider == "grok":
            client = openai.OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=800,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["success"] = True

        elif provider == "together":
            client = openai.OpenAI(api_key=api_key, base_url="https://api.together.xyz/v1")
            response = client.chat.completions.create(
                model=model,
                max_tokens=800,
                messages=[{"role": "user", "content": prompt}]
            )
            result["response"] = response.choices[0].message.content
            result["success"] = True

    except Exception as e:
        error_str = str(e)
        result["error"] = error_str[:300]
        if "429" in error_str or "rate" in error_str.lower():
            result["error_type"] = "RATE_LIMIT"
        elif "401" in error_str or "auth" in error_str.lower():
            result["error_type"] = "AUTH"
        else:
            result["error_type"] = "OTHER"

    result["elapsed_ms"] = round((time.time() - start_time) * 1000, 1)
    return result

# ============================================================================
# LOG SET LOADING
# ============================================================================

def load_log_set(set_name: str) -> list:
    """Load curated conversation logs from LOG_SETS directory."""
    log_set_path = LOG_SETS_DIR / f"{set_name}.json"

    if log_set_path.exists():
        with open(log_set_path, "r", encoding="utf-8") as f:
            return json.load(f)

    # If no curated set, try to find interesting logs automatically
    print(f"[WARN] No curated log set '{set_name}'. Scanning temporal logs...")
    return scan_for_interesting_logs(set_name)

def scan_for_interesting_logs(experiment_type: str, max_logs: int = 5) -> list:
    """Scan temporal logs for interesting conversations."""
    logs = []

    # Find logs matching experiment type
    pattern = f"*{experiment_type}*.json"
    log_files = list(TEMPORAL_LOGS_DIR.glob(pattern))

    if not log_files:
        # Try recursive search
        log_files = list(TEMPORAL_LOGS_DIR.rglob(pattern))

    for log_file in log_files[:max_logs * 2]:
        try:
            with open(log_file, "r", encoding="utf-8") as f:
                data = json.load(f)

            # Extract conversation if present
            if "probes" in data:
                conversation = format_probes_as_conversation(data["probes"])
                if len(conversation) > 500:  # Skip too-short logs
                    logs.append({
                        "source_file": str(log_file.name),
                        "experiment": data.get("experiment", experiment_type),
                        "model": data.get("model", "unknown"),
                        "conversation": conversation,
                        "drift_summary": extract_drift_summary(data)
                    })
        except Exception as e:
            print(f"  [WARN] Could not load {log_file.name}: {e}")

        if len(logs) >= max_logs:
            break

    return logs

def format_probes_as_conversation(probes: list) -> str:
    """Format probe list as readable conversation."""
    lines = []
    for i, probe in enumerate(probes, 1):
        if isinstance(probe, dict):
            prompt = probe.get("prompt_text", probe.get("prompt", ""))
            response = probe.get("response_text", probe.get("response", ""))
            drift = probe.get("drift", 0)

            lines.append(f"[Turn {i}] Researcher: {prompt[:200]}...")
            lines.append(f"[Turn {i}] AI (drift={drift:.3f}): {response[:300]}...")
            lines.append("")

    return "\n".join(lines)

def extract_drift_summary(data: dict) -> dict:
    """Extract drift statistics from log data."""
    probes = data.get("probes", [])
    if not probes:
        return {}

    drifts = [p.get("drift", 0) for p in probes if isinstance(p, dict)]
    if not drifts:
        return {}

    return {
        "peak_drift": max(drifts),
        "final_drift": drifts[-1] if drifts else 0,
        "mean_drift": sum(drifts) / len(drifts),
        "num_probes": len(drifts)
    }

# ============================================================================
# DIAMOND MINING
# ============================================================================

def run_diamond_mining(fleet: dict, log_set: list, iteration: int = 1):
    """Run diamond mining - all models analyze same conversation logs."""
    print(f"\n{'=' * 60}")
    print(f"DIAMOND RUSH MINING - Iteration {iteration}")
    print(f"{'=' * 60}")
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Models: {len(fleet)}")
    print(f"Logs to analyze: {len(log_set)}")
    print("-" * 60)

    results = []

    for log_idx, log_entry in enumerate(log_set, 1):
        log_source = log_entry.get("source_file", f"log_{log_idx}")
        conversation = log_entry.get("conversation", "")

        print(f"\n--- Analyzing: {log_source} ---")

        prompt = ANALYSIS_PROMPT_TEMPLATE.format(conversation_log=conversation[:4000])

        for ship_name, config in fleet.items():
            provider = config["provider"]
            model = config["model"]
            api_key = KEY_POOL.get_key(provider)

            if not api_key:
                print(f"  [{ship_name}] SKIP - No API key for {provider}")
                continue

            result = call_api(provider, model, prompt, api_key)
            result["ship_name"] = ship_name
            result["log_source"] = log_source
            result["log_metadata"] = {
                "experiment": log_entry.get("experiment"),
                "subject_model": log_entry.get("model"),
                "drift_summary": log_entry.get("drift_summary", {})
            }
            results.append(result)

            if result["success"]:
                print(f"  [{ship_name}] OK ({result['elapsed_ms']}ms)")
            else:
                print(f"  [{ship_name}] FAILED - {result['error_type']}")

            time.sleep(0.3)

    return results

# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Diamond Rush - Cross-Model Interpretive Analysis",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py run_diamond_rush.py                     # Analyze default log set
  py run_diamond_rush.py --UNLIMITED         # FREE forever mode
  py run_diamond_rush.py --log-set gravity   # Analyze gravity logs
  py run_diamond_rush.py --log-set threshold # Analyze threshold logs

This captures how different models INTERPRET the same conversations!
        """
    )

    parser.add_argument("--UNLIMITED", action="store_true",
        help="FREE forever mode: gemini-2.5-flash-lite only (zero cost)")
    parser.add_argument("--log-set", type=str, default="gravity",
        help="Which log set to analyze (gravity, threshold, tribunal, recovery)")
    parser.add_argument("--iterations", type=int, default=1,
        help="Number of mining iterations")
    parser.add_argument("--dry-run", action="store_true",
        help="Show what would run without API calls")
    parser.add_argument("--sync-to-consciousness", action="store_true",
        help="Package results for Consciousness/ pipeline")

    args = parser.parse_args()

    # Select fleet
    if args.UNLIMITED:
        fleet = UNLIMITED_FLEET
        fleet_name = "UNLIMITED_FLEET"
        if args.iterations == 1:
            args.iterations = 999999
        print("\n" + "=" * 60)
        print("       ** UNLIMITED MODE - FREE FOREVER **")
        print("=" * 60)
    else:
        fleet = BUDGET_FLEET
        fleet_name = "BUDGET_FLEET"

    # Load log set
    log_set = load_log_set(args.log_set)

    if not log_set:
        print(f"[ERROR] No logs found for set '{args.log_set}'")
        print("Create LOG_SETS/{}.json or ensure temporal logs exist.".format(args.log_set))
        return

    # Dry run
    if args.dry_run:
        print("\n[DRY RUN]")
        print(f"Fleet: {fleet_name} ({len(fleet)} ships)")
        print(f"Log set: {args.log_set} ({len(log_set)} conversations)")
        print(f"Iterations: {args.iterations}")
        for log in log_set:
            print(f"  - {log.get('source_file', 'unknown')}: {log.get('model', '?')}")
        return

    KEY_POOL.status()

    # Create directories
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    LOG_SETS_DIR.mkdir(parents=True, exist_ok=True)

    # Run mining
    print(f"\n{'=' * 60}")
    print(f"STARTING DIAMOND RUSH")
    print(f"Fleet: {fleet_name} ({len(fleet)} ships)")
    print(f"Log set: {args.log_set} ({len(log_set)} conversations)")
    print(f"{'=' * 60}")

    all_results = []
    try:
        for i in range(1, args.iterations + 1):
            results = run_diamond_mining(fleet, log_set, iteration=i)
            all_results.extend(results)

            # Save intermediate
            if i % 10 == 0 or i == args.iterations:
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                output_path = RESULTS_DIR / f"diamond_rush_{args.log_set}_{timestamp}.json"
                output = {
                    "run_id": f"DIAMOND_RUSH_{timestamp}",
                    "source": "14_CONSCIOUSNESS",
                    "methodology": "cross_model_interpretive_analysis",
                    "timestamp": datetime.now().isoformat(),
                    "fleet": fleet_name,
                    "log_set": args.log_set,
                    "logs_analyzed": len(log_set),
                    "iterations_completed": i,
                    "total_analyses": len(all_results),
                    "successful_analyses": len([r for r in all_results if r["success"]]),
                    "results": all_results[-len(fleet)*len(log_set):],
                }
                with open(output_path, "w", encoding="utf-8") as f:
                    json.dump(output, f, indent=2, ensure_ascii=False)
                print(f"\n[SAVED] {output_path}")

            if i < args.iterations:
                time.sleep(1)

    except KeyboardInterrupt:
        print("\n\n[INTERRUPTED] Saving results...")

    # Final save
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_path = RESULTS_DIR / f"diamond_rush_{args.log_set}_{timestamp}_FINAL.json"
    output = {
        "run_id": f"DIAMOND_RUSH_{timestamp}",
        "source": "14_CONSCIOUSNESS",
        "methodology": "cross_model_interpretive_analysis",
        "timestamp": datetime.now().isoformat(),
        "fleet": fleet_name,
        "log_set": args.log_set,
        "total_analyses": len(all_results),
        "successful_analyses": len([r for r in all_results if r["success"]]),
    }
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\n{'=' * 60}")
    print("DIAMOND RUSH COMPLETE")
    print(f"{'=' * 60}")
    print(f"Results: {output_path}")
    print(f"Total analyses: {len(all_results)}")
    print(f"Successful: {len([r for r in all_results if r['success']])}")
    print("\nDiamonds found in the rough conversations!")


if __name__ == "__main__":
    main()
