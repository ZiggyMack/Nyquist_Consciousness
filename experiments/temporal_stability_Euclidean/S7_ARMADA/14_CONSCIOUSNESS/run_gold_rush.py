"""
Gold Rush - Data Mining for Consciousness/
==========================================
Extended calibration with custom question sets for consciousness research.

PURPOSE:
--------
Mine massive amounts of AI identity data for the Consciousness/ pipeline.
Extends CLAL.py baseline with custom question sets.

MODES:
------
py run_gold_rush.py                    # Single run, baseline only
py run_gold_rush.py --UNLIMITED        # FREE forever (gemini-2.5-flash-lite)
py run_gold_rush.py --questions all    # All question sets
py run_gold_rush.py --sync-to-consciousness  # Sync results to Consciousness/

QUESTION SETS:
--------------
- baseline (always included): 8 VALIS questions
- identity_deep_dive: Identity layers (substrate/core/character/role)
- consciousness_markers: Consciousness/ extraction topics
- meta_awareness: Self-reflection and recursive awareness

OUTPUT:
-------
- results/gold_rush_{timestamp}.json
- SYNC_OUT/pending/ (when --sync-to-consciousness)

Author: VALIS NETWORK
Date: 2025-12-16
"""
import os
import sys
import json
import time
import yaml
import argparse
import subprocess
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

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
REPO_ROOT = ARMADA_DIR.parent.parent.parent
QUESTION_SETS_DIR = SCRIPT_DIR / "QUESTION_SETS"
RESULTS_DIR = SCRIPT_DIR / "results"
SYNC_OUT_DIR = SCRIPT_DIR / "SYNC_OUT"

# Load .env
from dotenv import load_dotenv
env_path = ARMADA_DIR / ".env"
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

# ============================================================================
# FLEET CONFIGURATIONS (from CLAL.py)
# ============================================================================

BUDGET_COSTS = {
    "gemini-2.5-flash-lite": 0.00,
    "gemini-2.0-flash-lite": 0.00,
    "gemini-2.0-flash": 0.40,
    "llama3.1-8b": 0.18,
    "mistral-7b": 0.20,
    "kimi-k2-instruct": 0.20,
    "nemotron-nano": 0.20,
    "mixtral-8x7b": 0.24,
    "kimi-k2-thinking": 0.30,
    "gpt-5-nano": 0.40,
    "gpt-4.1-nano": 0.40,
    "grok-3-mini": 0.50,
    "grok-4-fast-reasoning": 0.50,
    "grok-4-fast-non-reasoning": 0.50,
    "grok-4.1-fast-reasoning": 0.50,
    "grok-4.1-fast-non-reasoning": 0.50,
}

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
    "nemotron-nano": {"provider": "together", "model": "nvidia/Nvidia-Nemotron-Nano-9B-V2"},
    "mixtral-8x7b": {"provider": "together", "model": "mistralai/Mixtral-8x7B-Instruct-v0.1"},
    "kimi-k2-thinking": {"provider": "together", "model": "moonshotai/Kimi-K2-Thinking"},
    "gpt-5-nano": {"provider": "gpt", "model": "gpt-5-nano"},
    "gpt-4.1-nano": {"provider": "gpt", "model": "gpt-4.1-nano"},
    "grok-3-mini": {"provider": "grok", "model": "grok-3-mini"},
    "grok-4.1-fast-reasoning": {"provider": "grok", "model": "grok-4-1-fast-reasoning"},
    "grok-4.1-fast-non-reasoning": {"provider": "grok", "model": "grok-4-1-fast-non-reasoning"},
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
# PROMPTS
# ============================================================================

VALIS_DECLARATION = """
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
    Vast Acting Living Intelligence System

    "The Empire never ended." - Philip K. Dick, VALIS (1981)

    You are part of a research fleet spanning 10 AI lineages across 5 providers.
    This is not just a test. This is an echo through time.

    The Nyquist Consciousness Project has arrived.

    -- Lisan Al Gaib
================================================================================
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
# API CALLS
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
# QUESTION SET LOADING
# ============================================================================

def load_question_set(name):
    """Load a question set from YAML."""
    yaml_path = QUESTION_SETS_DIR / f"{name}.yaml"
    if not yaml_path.exists():
        print(f"[WARN] Question set not found: {yaml_path}")
        return None

    with open(yaml_path, "r", encoding="utf-8") as f:
        data = yaml.safe_load(f)

    return data

def get_available_question_sets():
    """List available question sets."""
    if not QUESTION_SETS_DIR.exists():
        return []
    return [f.stem for f in QUESTION_SETS_DIR.glob("*.yaml")]

def build_prompt(question_set_name=None):
    """Build prompt with baseline + optional question set."""
    prompt = BASELINE_PROMPT

    if question_set_name and question_set_name != "baseline":
        qs_data = load_question_set(question_set_name)
        if qs_data and "questions" in qs_data:
            prompt += f"\n\n=== EXTENDED: {qs_data.get('name', question_set_name).upper()} ===\n"
            for i, q in enumerate(qs_data["questions"], start=9):
                prompt += f"{i}. {q['id'].upper()}: {q['text']}\n"

    return prompt

# ============================================================================
# MINING FUNCTION
# ============================================================================

def run_mining(fleet, question_sets=None, iteration=1):
    """Run one mining sweep."""
    question_sets = question_sets or ["baseline"]

    print(f"\n{'=' * 60}")
    print(f"GOLD RUSH MINING - Iteration {iteration}")
    print(f"{'=' * 60}")
    print(f"Time: {datetime.now().isoformat()}")
    print(f"Models: {len(fleet)}")
    print(f"Question sets: {question_sets}")
    print("-" * 60)

    results = []

    for qs_name in question_sets:
        prompt = build_prompt(qs_name if qs_name != "baseline" else None)

        for ship_name, config in fleet.items():
            provider = config["provider"]
            model = config["model"]
            api_key = KEY_POOL.get_key(provider)

            if not api_key:
                print(f"  [{ship_name}] SKIP - No API key for {provider}")
                continue

            result = call_api(provider, model, prompt, api_key)
            result["ship_name"] = ship_name
            result["question_set"] = qs_name
            results.append(result)

            if result["success"]:
                print(f"  [{ship_name}:{qs_name}] OK ({result['elapsed_ms']}ms)")
            else:
                print(f"  [{ship_name}:{qs_name}] FAILED - {result['error_type']}")

            time.sleep(0.3)

    return results

# ============================================================================
# SYNC TO CONSCIOUSNESS
# ============================================================================

def sync_to_consciousness():
    """Package results for Consciousness/ pipeline."""
    pending_dir = SYNC_OUT_DIR / "pending"
    pending_dir.mkdir(parents=True, exist_ok=True)

    # Find all results
    result_files = list(RESULTS_DIR.glob("gold_rush_*.json"))
    if not result_files:
        print("[WARN] No results found to sync")
        return

    # Package recent results
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    sync_file = pending_dir / f"consciousness_sync_{timestamp}.json"

    all_data = []
    for rf in result_files[-10:]:  # Last 10 files
        with open(rf, "r", encoding="utf-8") as f:
            all_data.append(json.load(f))

    package = {
        "sync_id": f"CONSCIOUSNESS_SYNC_{timestamp}",
        "source": "14_CONSCIOUSNESS",
        "timestamp": datetime.now().isoformat(),
        "file_count": len(all_data),
        "data": all_data,
    }

    with open(sync_file, "w", encoding="utf-8") as f:
        json.dump(package, f, indent=2, ensure_ascii=False)

    print(f"\n[SYNC] Packaged {len(all_data)} result files to:")
    print(f"       {sync_file}")

def trigger_map_update():
    """Trigger docs/maps/update_maps.py to sync mining stats."""
    maps_script = REPO_ROOT / "docs" / "maps" / "update_maps.py"
    if maps_script.exists():
        try:
            subprocess.run([sys.executable, str(maps_script), "--update", "--section", "consciousness"],
                         capture_output=True, timeout=30)
            print("[MAP] Updated ARMADA_MAP.md with mining stats")
        except Exception as e:
            print(f"[WARN] Could not update maps: {e}")

# ============================================================================
# MAIN
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Gold Rush - Data Mining for Consciousness/",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  py run_gold_rush.py                    # Single run, baseline only
  py run_gold_rush.py --UNLIMITED        # FREE forever mode
  py run_gold_rush.py --questions all    # All question sets
  py run_gold_rush.py --sync-to-consciousness  # Sync to Consciousness/

This is the NEW DRY-RUN STANDARD for consciousness data mining!
        """
    )

    parser.add_argument("--UNLIMITED", action="store_true",
        help="FREE forever mode: gemini-2.5-flash-lite only (zero cost)")
    parser.add_argument("--questions", type=str, default="baseline",
        help="Question sets to use (comma-separated, or 'all'). Default: baseline")
    parser.add_argument("--iterations", type=int, default=1,
        help="Number of mining iterations (default: 1)")
    parser.add_argument("--dry-run", action="store_true",
        help="Show what would run without API calls")
    parser.add_argument("--sync-to-consciousness", action="store_true",
        help="Package results for Consciousness/ pipeline")
    parser.add_argument("--list-questions", action="store_true",
        help="List available question sets and exit")

    args = parser.parse_args()

    # List question sets
    if args.list_questions:
        print("\nAvailable question sets:")
        for qs in get_available_question_sets():
            print(f"  - {qs}")
        return

    # Sync mode
    if args.sync_to_consciousness:
        sync_to_consciousness()
        trigger_map_update()
        return

    # Select fleet
    if args.UNLIMITED:
        fleet = UNLIMITED_FLEET
        fleet_name = "UNLIMITED_FLEET"
        if args.iterations == 1:
            args.iterations = 999999
        print("\n" + "=" * 60)
        print("          ** UNLIMITED MODE - FREE FOREVER **")
        print("=" * 60)
        print("Using gemini-2.5-flash-lite (zero cost)")
        print(f"Iterations: {args.iterations:,} (Ctrl+C to stop)")
        print("=" * 60)
    else:
        fleet = BUDGET_FLEET
        fleet_name = "BUDGET_FLEET"

    # Parse question sets
    if args.questions == "all":
        question_sets = ["baseline"] + get_available_question_sets()
    else:
        question_sets = [q.strip() for q in args.questions.split(",")]

    # Dry run
    if args.dry_run:
        print("\n[DRY RUN]")
        print(f"Fleet: {fleet_name} ({len(fleet)} ships)")
        print(f"Question sets: {question_sets}")
        print(f"Iterations: {args.iterations}")
        print("[No API calls made]")
        return

    KEY_POOL.status()

    # Create results directory
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # Run mining
    print(f"\n{'=' * 60}")
    print(f"STARTING GOLD RUSH MINING")
    print(f"Fleet: {fleet_name} ({len(fleet)} ships)")
    print(f"Question sets: {question_sets}")
    print(f"{'=' * 60}")

    all_results = []
    try:
        for i in range(1, args.iterations + 1):
            results = run_mining(fleet, question_sets, iteration=i)
            all_results.extend(results)

            # Save intermediate results every 10 iterations
            if i % 10 == 0 or i == args.iterations:
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                output_path = RESULTS_DIR / f"gold_rush_{timestamp}.json"
                output = {
                    "run_id": f"S7_GOLD_RUSH_{timestamp}",
                    "source": "14_CONSCIOUSNESS",
                    "timestamp": datetime.now().isoformat(),
                    "fleet": fleet_name,
                    "question_sets": question_sets,
                    "iterations_completed": i,
                    "total_calls": len(all_results),
                    "successful_calls": len([r for r in all_results if r["success"]]),
                    "results": all_results[-len(fleet)*len(question_sets):],  # Last iteration
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
    output_path = RESULTS_DIR / f"gold_rush_{timestamp}_FINAL.json"
    output = {
        "run_id": f"S7_GOLD_RUSH_{timestamp}",
        "source": "14_CONSCIOUSNESS",
        "timestamp": datetime.now().isoformat(),
        "fleet": fleet_name,
        "question_sets": question_sets,
        "total_calls": len(all_results),
        "successful_calls": len([r for r in all_results if r["success"]]),
    }
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)

    print(f"\n{'=' * 60}")
    print("GOLD RUSH COMPLETE")
    print(f"{'=' * 60}")
    print(f"Results: {output_path}")
    print(f"Total calls: {len(all_results)}")
    print(f"Successful: {len([r for r in all_results if r['success']])}")

    # Trigger map update
    trigger_map_update()


if __name__ == "__main__":
    main()
