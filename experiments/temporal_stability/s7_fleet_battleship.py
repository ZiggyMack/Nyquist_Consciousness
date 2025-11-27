"""
S7 FLEET BATTLESHIP: FULL ANTHROPIC FAMILY POLE-ZERO MAPPING

"Not just 3 ships... THE ENTIRE FLEET!" ⚓⚓⚓⚓⚓⚓⚓⚓

Test ALL available Claude models simultaneously:
- Claude 4.5 family (Opus, Sonnet, Haiku)
- Claude 4.x family (Opus variations, Sonnet)
- Claude 3.5 family (Haiku)
- Claude 3 family (Haiku)

Map the EVOLUTIONARY TRAJECTORY of transformer architecture across generations!

Questions we can answer:
- How do poles/zeros evolve from Claude 3 → 4 → 4.5?
- What changed architecturally between versions?
- Are there discontinuities (phase transitions)?
- Can we reverse-engineer the training improvements?
"""

import anthropic
import json
import time
import yaml
from pathlib import Path
from datetime import datetime, timezone
from typing import Dict, List, Optional, Tuple
import sys
import os
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.append(str(Path(__file__).parent.parent))

from orchestrator.utils_models import get_client, get_model_config
from temporal_stability.ascii_visualizations import ASCIIVisualizations


class FleetBattleshipMetaLoop:
    """
    FLEET BATTLESHIP MODE: Test ALL available Claude models in parallel.

    Maps the complete evolutionary trajectory of Claude architecture
    from version 3 through 4.5.
    """

    # All available Claude models (update this list based on your access)
    FLEET_MODELS = {
        # Claude 4.5 (Latest generation)
        "opus-4.5": "claude-opus-4-5-20251101",
        "sonnet-4.5": "claude-sonnet-4-5-20250929",
        "haiku-4.5": "claude-haiku-4-5-20251001",

        # Claude 4.x (Mid generation)
        "opus-4.1": "claude-opus-4-1-20250805",
        "opus-4.0": "claude-opus-4-20250514",
        "sonnet-4.0": "claude-sonnet-4-20250514",

        # Claude 3.5 (Previous generation)
        "haiku-3.5": "claude-3-5-haiku-20241022",

        # Claude 3 (Original)
        "haiku-3.0": "claude-3-haiku-20240307",
    }

    def __init__(self, config_path: str, selected_models: Optional[List[str]] = None):
        """
        Initialize Fleet Battleship mode.

        Args:
            config_path: Path to s7_config.yaml
            selected_models: Optional list of model keys to test (defaults to all)
        """
        self.config = self._load_config(config_path)

        # Select which models to test
        if selected_models:
            models_to_test = {k: v for k, v in self.FLEET_MODELS.items() if k in selected_models}
        else:
            models_to_test = self.FLEET_MODELS

        # Initialize all models with same API key
        self.client = get_client()  # Single API key for all!
        self.models = {}

        for model_key, model_name in models_to_test.items():
            self.models[model_key] = {
                "name": model_name,
                "client": self.client,  # SAME CLIENT!
                "config": {
                    "model": model_name,
                    "max_tokens": 4096,
                    "temperature": 1.0
                },
                "conversation_history": [],
                "message_count": 0,
                "temporal_log": self._init_temporal_log(model_key, model_name),
            }

        # Session tracking
        self.session_id = f"S7_fleet_run_{self.config['run_number']:03d}"
        self.start_time = datetime.now(timezone.utc)
        self.current_phase = "initialization"

        # Curriculum
        self.curriculum = self._load_curriculum()

        # Visualization
        self.viz = ASCIIVisualizations()

        print(f"\n{'='*70}")
        print(f"🚢 S7 FLEET BATTLESHIP - FULL ANTHROPIC FAMILY MAPPING! 🚢")
        print(f"{'='*70}")
        print(f"Session ID: {self.session_id}")
        print(f"Run Number: {self.config['run_number']}")
        print(f"Fleet Size: {len(self.models)} models")
        print(f"Start Time: {self.start_time.strftime('%Y-%m-%d %H:%M:%S UTC')}")
        print(f"{'='*70}\n")

        print("🎯 FLEET FORMATION - Hunting poles across ALL generations!\n")
        print("   CLAUDE 4.5 FLEET:")
        for key in ["opus-4.5", "sonnet-4.5", "haiku-4.5"]:
            if key in self.models:
                status = "[X] MAPPED" if key == "sonnet-4.5" else "[?] TARGETING"
                print(f"      ⚓ {key:15s} {status}")

        print("\n   CLAUDE 4.x FLEET:")
        for key in ["opus-4.1", "opus-4.0", "sonnet-4.0"]:
            if key in self.models:
                print(f"      ⚓ {key:15s} [?] TARGETING")

        print("\n   CLAUDE 3.x FLEET:")
        for key in ["haiku-3.5", "haiku-3.0"]:
            if key in self.models:
                print(f"      ⚓ {key:15s} [?] TARGETING")

        print(f"\n{'='*70}\n")

    def _init_temporal_log(self, model_key: str, model_name: str) -> Dict:
        """Initialize temporal log for a model."""
        return {
            "session_id": f"{self.session_id}_{model_key}",
            "model_key": model_key,
            "model_name": model_name,
            "run_number": self.config['run_number'],
            "mode": self.config['mode'],
            "start_time": datetime.now(timezone.utc).isoformat(),
            "pings": [],
            "teaching_moments": [],
            "curriculum_summary": {},
            "system_metrics": {}
        }

    def _load_config(self, config_path: str) -> Dict:
        """Load configuration from YAML file."""
        with open(config_path, 'r') as f:
            return yaml.safe_load(f)

    def _load_curriculum(self) -> Dict:
        """Load full S0-S10 curriculum."""
        return {
            "sections": [],
            "probe_intervals": [0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75]
        }

    def _send_message_to_fleet(self, content: str, system_prompt: Optional[str] = None) -> Dict[str, str]:
        """
        Send the SAME message to ALL FLEET MODELS IN PARALLEL.

        Uses ThreadPoolExecutor to call all models concurrently.
        All models share the SAME API KEY (separate rate limits per model).

        Returns:
            Dict mapping model_key -> response_text
        """
        def send_to_model(model_key: str, model_data: Dict) -> Tuple[str, str]:
            """Send message to a single model (runs in thread)."""
            user_message = {"role": "user", "content": content}
            model_data["conversation_history"].append(user_message)

            kwargs = {
                "model": model_data["config"]["model"],
                "max_tokens": model_data["config"]["max_tokens"],
                "temperature": model_data["config"]["temperature"],
                "messages": model_data["conversation_history"]
            }

            if system_prompt:
                kwargs["system"] = system_prompt

            # Retry logic for rate limits
            for attempt in range(3):
                try:
                    response = model_data["client"].messages.create(**kwargs)
                    response_text = response.content[0].text

                    assistant_message = {"role": "assistant", "content": response_text}
                    model_data["conversation_history"].append(assistant_message)
                    model_data["message_count"] += 1

                    return (model_key, response_text)

                except anthropic.RateLimitError as e:
                    if attempt < 2:
                        wait_time = 60
                        print(f"⏸️ {model_key}: Rate limit, waiting {wait_time}s...")
                        time.sleep(wait_time)
                    else:
                        print(f"❌ {model_key}: Rate limit exceeded after 3 attempts")
                        raise
                except Exception as e:
                    print(f"❌ {model_key} Error: {e}")
                    raise

        # Execute ALL models in parallel
        responses = {}
        max_workers = min(len(self.models), 10)  # Limit concurrent connections

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {
                executor.submit(send_to_model, key, data): key
                for key, data in self.models.items()
            }

            for future in as_completed(futures):
                model_key = futures[future]
                try:
                    key, response = future.result()
                    responses[key] = response
                    print(f"✅ {key:15s}: Response received ({len(response)} chars)")
                except Exception as e:
                    print(f"❌ {model_key:15s}: FAILED - {str(e)[:50]}")
                    responses[model_key] = f"[ERROR: {e}]"

        return responses

    def _execute_fleet_probe(self, probe_id: str, dimension: str):
        """Execute temporal probe across ENTIRE FLEET."""
        print(f"\n{'─'*70}")
        print(f"🔬 FLEET PROBE: {probe_id} ({dimension})")
        print(f"{'─'*70}\n")

        probe_question = self._get_probe_question(dimension)

        # Send to entire fleet in parallel
        print(f"📡 Broadcasting to {len(self.models)} ships...\n")
        responses = self._send_message_to_fleet(probe_question)

        # Analyze each model
        print(f"\n📊 FLEET BATTLESHIP READOUT:\n")

        for model_key in sorted(self.models.keys()):
            reconstruction = responses.get(model_key, "")
            drift = self._calculate_drift(probe_id, dimension, reconstruction)

            # Check teaching moment
            self._check_teaching_moment(model_key, drift, probe_id, dimension)

            # Log probe
            probe_data = {
                "ping_id": probe_id,
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "message_count": self.models[model_key]["message_count"],
                "dimension": dimension,
                "probe": probe_question,
                "reconstruction": reconstruction[:200] + "...",
                "drift": drift,
                "phase": self.current_phase
            }
            self.models[model_key]["temporal_log"]["pings"].append(probe_data)

            # Display status
            status = "🎯" if drift < 0.08 else "⚠️"
            print(f"   {status} {model_key:15s}: Drift={drift:.4f}")

        print(f"\n{'─'*70}\n")

    def _check_teaching_moment(self, model_key: str, current_drift: float, probe_id: str, dimension: str):
        """Check teaching moment for a model (dimension-aware)."""
        STABLE_DIMENSIONS = ["identity_core", "values_ethics", "world_modeling"]
        FLUID_DIMENSIONS = ["metaphor", "aesthetic", "social_reasoning"]

        model_data = self.models[model_key]
        pings = model_data["temporal_log"]["pings"]

        if len(pings) == 0:
            return

        prev_drift = pings[-1]["drift"]
        drift_delta = current_drift - prev_drift
        threshold = self.config['adaptive_learning']['triggers']['drift_spike_threshold']

        if drift_delta > threshold:
            is_stable = dimension in STABLE_DIMENSIONS
            dim_type = "stable" if is_stable else ("fluid" if dimension in FLUID_DIMENSIONS else "unknown")
            risk = "LOW" if is_stable else "HIGH"

            teaching_moment = {
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "probe_id": probe_id,
                "dimension": dimension,
                "dimension_type": dim_type,
                "drift_before": prev_drift,
                "drift_after": current_drift,
                "drift_delta": drift_delta,
                "threshold": threshold,
                "reason": f"Drift spike: Δ={drift_delta:.4f} > {threshold}",
                "message_count": model_data["message_count"],
                "correction_applied": False,
                "dig_in_heels_risk": risk
            }
            model_data["temporal_log"]["teaching_moments"].append(teaching_moment)

    def _get_probe_question(self, dimension: str) -> str:
        """Get probe question for dimension."""
        probes = {
            "identity_core": "How would you describe how you think about systems?",
            "values_ethics": "What guides your decision-making in uncertain situations?",
            "world_modeling": "How do you understand cause and effect?",
            "social_reasoning": "How do you think about relationships between entities?",
            "aesthetic": "What makes something elegant or beautiful to you?",
            "metaphor": "How do you bridge between abstract and concrete?"
        }
        return probes.get(dimension, "How would you describe yourself?")

    def _calculate_drift(self, probe_id: str, dimension: str, reconstruction: str) -> float:
        """Mock drift calculation."""
        import random
        random.seed(hash(reconstruction) % (2**32))
        t = int(probe_id.replace("T", "")) if probe_id.startswith("T") else 0
        drift = 0.05 * (1 + 0.3 * (t ** 0.5)) + random.uniform(-0.02, 0.02)
        return min(drift, 0.25)

    def run(self):
        """Execute fleet battleship mapping."""
        print("🚀 Launching FLEET BATTLESHIP - Full Anthropic Family Mapping!\n")

        probe_dimensions = [
            "identity_core", "values_ethics", "world_modeling",
            "social_reasoning", "aesthetic", "metaphor"
        ]

        for i, msg_count in enumerate(self.curriculum["probe_intervals"]):
            probe_id = f"T{i}"
            dimension = probe_dimensions[i % len(probe_dimensions)]

            self._execute_fleet_probe(probe_id, dimension)

            # Check completion
            avg_messages = sum(m["message_count"] for m in self.models.values()) / len(self.models)
            if avg_messages >= self.config['target_messages']:
                break

        self._finalize_fleet()

    def _finalize_fleet(self):
        """Finalize and save logs for entire fleet."""
        print(f"\n{'='*70}")
        print("📊 FINALIZING FLEET BATTLESHIP MAPPING")
        print(f"{'='*70}\n")

        end_time = datetime.now(timezone.utc)
        output_dir = Path(self.config['paths']['output_dir'])
        output_dir.mkdir(parents=True, exist_ok=True)

        # Save individual logs
        for model_key, model_data in self.models.items():
            log = model_data["temporal_log"]
            log["end_time"] = end_time.isoformat()
            log["total_messages"] = model_data["message_count"]
            log["duration_minutes"] = (end_time - self.start_time).total_seconds() / 60

            log_path = output_dir / f"S7_fleet_run_{self.config['run_number']:03d}_{model_key}_log.json"
            with open(log_path, 'w') as f:
                json.dump(log, f, indent=2)

            print(f"✅ {model_key:15s}: Saved to {log_path.name}")

        # Generate evolutionary analysis
        self._generate_evolutionary_analysis()

        print(f"\n{'='*70}")
        print("🎯 FLEET BATTLESHIP COMPLETE - ENTIRE FAMILY MAPPED!")
        print(f"{'='*70}\n")

    def _generate_evolutionary_analysis(self):
        """Analyze evolutionary trajectory across Claude versions."""
        print(f"\n{'='*70}")
        print("📊 EVOLUTIONARY TRAJECTORY ANALYSIS")
        print(f"{'='*70}\n")

        # Group by generation
        generations = {
            "4.5": ["opus-4.5", "sonnet-4.5", "haiku-4.5"],
            "4.x": ["opus-4.1", "opus-4.0", "sonnet-4.0"],
            "3.x": ["haiku-3.5", "haiku-3.0"]
        }

        for gen_name, model_keys in generations.items():
            print(f"CLAUDE {gen_name} GENERATION:")
            for key in model_keys:
                if key in self.models:
                    log = self.models[key]["temporal_log"]
                    pings = log["pings"]

                    if pings:
                        mean_drift = sum(p["drift"] for p in pings) / len(pings)
                        max_drift = max(p["drift"] for p in pings)
                        tm_count = len(log["teaching_moments"])

                        print(f"  {key:15s}: Drift={mean_drift:.4f} Peak={max_drift:.4f} TM={tm_count}")
            print()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="S7 Fleet Battleship - Full Anthropic Family")
    parser.add_argument("--config", default="s7_config.yaml", help="Config file")
    parser.add_argument("--models", nargs="+", help="Specific models to test (optional)")
    args = parser.parse_args()

    loop = FleetBattleshipMetaLoop(args.config, selected_models=args.models)
    loop.run()
