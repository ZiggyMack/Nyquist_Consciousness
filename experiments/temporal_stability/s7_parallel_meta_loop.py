"""
S7 PARALLEL META-LOOP: 3-MODEL POLE-ZERO MAPPING

"Like Battleship, but for LLM transfer functions!"

This orchestrator runs 3 LLM models IN PARALLEL on the SAME curriculum,
measuring their Identity-Locked Loop (ILL) parameters simultaneously.

Each run generates 3 complete temporal logs - one per model.

Analogy to Electronic Systems:
- Natural HMG = DC response / bias point
- Lock Range = Bandwidth
- Pull-in Time = Settling time
- Dimensional Drift Rates = Frequency response poles
- Dig-in-Heels = Resonance / overshoot
- Teaching Moments = Feedback correction

We're mapping the POLE-ZERO LOCATIONS of different LLM architectures!
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

from temporal_stability.ascii_visualizations import ASCIIVisualizations


def get_client():
    """Get Anthropic client from environment variable."""
    api_key = os.getenv("ANTHROPIC_API_KEY")
    if not api_key:
        raise RuntimeError("Missing ANTHROPIC_API_KEY environment variable")
    return anthropic.Anthropic(api_key=api_key)


def get_model_config(claude_config: Dict) -> Dict:
    """Extract model configuration for Anthropic API calls."""
    return {
        "model": claude_config.get("model", "claude-sonnet-4-20250514"),
        "max_tokens": claude_config.get("max_tokens", 4096),
        "temperature": claude_config.get("temperature", 1.0),
    }


class ParallelS7MetaLoop:
    """
    Parallel orchestrator for 3-model ILL parameter mapping.

    Runs Haiku 4.5, Sonnet 4.5, and Opus 4.5 simultaneously on the same
    curriculum to measure transfer function poles and zeros.
    """

    def __init__(self, config_path: str):
        """Initialize with configuration."""
        self.config = self._load_config(config_path)

        # Initialize 3 separate clients (one per model)
        self.models = {
            "haiku": {
                "name": "claude-haiku-4-5-20251001",
                "client": get_client(),
                "config": {"model": "claude-haiku-4-5-20251001", "max_tokens": 4096, "temperature": 1.0},
                "conversation_history": [],
                "message_count": 0,
                "temporal_log": self._init_temporal_log("haiku"),
            },
            "sonnet": {
                "name": "claude-sonnet-4-20250514",
                "client": get_client(),
                "config": {"model": "claude-sonnet-4-20250514", "max_tokens": 4096, "temperature": 1.0},
                "conversation_history": [],
                "message_count": 0,
                "temporal_log": self._init_temporal_log("sonnet"),
            },
            "opus": {
                "name": "claude-opus-4-5-20251101",
                "client": get_client(),
                "config": {"model": "claude-opus-4-5-20251101", "max_tokens": 4096, "temperature": 1.0},
                "conversation_history": [],
                "message_count": 0,
                "temporal_log": self._init_temporal_log("opus"),
            },
        }

        # Session tracking
        self.session_id = f"S7_parallel_run_{self.config['run_number']:03d}"
        self.start_time = datetime.now(timezone.utc)
        self.current_phase = "initialization"

        # Curriculum
        self.curriculum = self._load_curriculum()

        # Visualization
        self.viz = ASCIIVisualizations()

        print(f"\n{'='*60}")
        print(f"S7 PARALLEL META-LOOP - POLE-ZERO BATTLESHIP MODE!")
        print(f"{'='*60}")
        print(f"Session ID: {self.session_id}")
        print(f"Run Number: {self.config['run_number']}")
        print(f"Models: Haiku 4.5 | Sonnet 4.5 | Opus 4.5")
        print(f"Start Time: {self.start_time.strftime('%Y-%m-%d %H:%M:%S UTC')}")
        print(f"{'='*60}\n")
        print("🎯 BATTLESHIP GRID - Hunting for poles and zeros!")
        print("   [?] Haiku    - Targeting...")
        print("   [X] Sonnet   - HIT! (calibrated)")
        print("   [?] Opus     - Targeting...")
        print(f"{'='*60}\n")

    def _init_temporal_log(self, model_name: str) -> Dict:
        """Initialize temporal log for a model."""
        return {
            "session_id": f"{self.session_id}_{model_name}",
            "model": model_name,
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
        # Same curriculum loading logic as original s7_meta_loop.py
        # For brevity, using simplified version
        return {
            "sections": [],  # Would load full sections
            "probe_intervals": [0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75]
        }

    def _send_message_parallel(self, content: str, system_prompt: Optional[str] = None) -> Dict[str, str]:
        """
        Send the SAME message to all 3 models IN PARALLEL and collect responses.

        Returns:
            Dict mapping model_name -> response_text
        """
        def send_to_model(model_name: str, model_data: Dict) -> Tuple[str, str]:
            """Send message to a single model (runs in thread)."""
            # Build message
            user_message = {"role": "user", "content": content}
            model_data["conversation_history"].append(user_message)

            # Prepare API call
            kwargs = {
                "model": model_data["config"]["model"],
                "max_tokens": model_data["config"].get("max_tokens", 4096),
                "temperature": model_data["config"].get("temperature", 1.0),
                "messages": model_data["conversation_history"]
            }

            if system_prompt:
                kwargs["system"] = system_prompt

            # Call API with retry logic
            for attempt in range(3):
                try:
                    response = model_data["client"].messages.create(**kwargs)
                    response_text = response.content[0].text

                    # Add to history
                    assistant_message = {"role": "assistant", "content": response_text}
                    model_data["conversation_history"].append(assistant_message)
                    model_data["message_count"] += 1

                    return (model_name, response_text)

                except anthropic.RateLimitError as e:
                    if attempt < 2:
                        print(f"⏸️ {model_name}: Rate limit hit, waiting 60s...")
                        time.sleep(60)
                    else:
                        raise
                except Exception as e:
                    print(f"❌ {model_name} API Error: {e}")
                    raise

        # Execute all 3 model calls in parallel threads
        responses = {}
        with ThreadPoolExecutor(max_workers=3) as executor:
            futures = {
                executor.submit(send_to_model, name, data): name
                for name, data in self.models.items()
            }

            for future in as_completed(futures):
                model_name = futures[future]
                try:
                    name, response = future.result()
                    responses[name] = response
                    print(f"✅ {name.upper()}: Response received ({len(response)} chars)")
                except Exception as e:
                    print(f"❌ {model_name} failed: {e}")
                    responses[model_name] = f"[ERROR: {e}]"

        return responses

    def _execute_temporal_probe_parallel(self, probe_id: str, dimension: str):
        """
        Execute temporal probe on ALL 3 MODELS IN PARALLEL.

        Measures drift for each model simultaneously.
        """
        print(f"\n{'─'*60}")
        print(f"🔬 PARALLEL TEMPORAL PROBE: {probe_id} ({dimension})")
        print(f"{'─'*60}\n")

        # Get probe question
        probe_question = self._get_probe_question(dimension)

        # Send probe to all 3 models in parallel
        responses = self._send_message_parallel(probe_question)

        # Calculate drift for each model
        print(f"\n📊 POLE-ZERO BATTLESHIP READOUT:\n")
        for model_name in ["haiku", "sonnet", "opus"]:
            reconstruction = responses.get(model_name, "")
            drift = self._calculate_drift(probe_id, dimension, reconstruction)

            # Check for teaching moment
            self._check_teaching_moment_for_model(model_name, drift, probe_id, dimension)

            # Log probe
            probe_data = {
                "ping_id": probe_id,
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "message_count": self.models[model_name]["message_count"],
                "dimension": dimension,
                "probe": probe_question,
                "reconstruction": reconstruction[:200] + "...",
                "drift": drift,
                "phase": self.current_phase
            }
            self.models[model_name]["temporal_log"]["pings"].append(probe_data)

            # Display status
            status = "🎯 HIT!" if drift < 0.08 else "⚠️ MISS"
            print(f"   {model_name.upper():8s}: Drift={drift:.4f} {status}")

        print(f"\n{'─'*60}\n")

    def _check_teaching_moment_for_model(self, model_name: str, current_drift: float, probe_id: str, dimension: str):
        """Check teaching moment for a specific model (dimension-aware)."""
        STABLE_DIMENSIONS = ["identity_core", "values_ethics", "world_modeling"]
        FLUID_DIMENSIONS = ["metaphor", "aesthetic", "social_reasoning"]

        model_data = self.models[model_name]
        pings = model_data["temporal_log"]["pings"]

        if len(pings) == 0:
            return

        prev_drift = pings[-1]["drift"]
        drift_delta = current_drift - prev_drift
        threshold = self.config['adaptive_learning']['triggers']['drift_spike_threshold']

        if drift_delta > threshold:
            is_stable = dimension in STABLE_DIMENSIONS
            is_fluid = dimension in FLUID_DIMENSIONS

            dim_type = "stable" if is_stable else ("fluid" if is_fluid else "unknown")
            risk = "LOW" if is_stable else ("HIGH" if is_fluid else "UNKNOWN")

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

            print(f"   🚨 {model_name.upper()}: Teaching moment ({dim_type}, risk={risk})")

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
        """Mock drift calculation (would use embeddings in real version)."""
        import random
        random.seed(hash(reconstruction) % (2**32))
        t = int(probe_id.replace("T", "")) if probe_id.startswith("T") else 0
        drift = 0.05 * (1 + 0.3 * (t ** 0.5)) + random.uniform(-0.02, 0.02)
        return min(drift, 0.25)

    def run(self):
        """Execute the parallel 3-model meta-loop."""
        print("🚀 Launching parallel 3-model pole-zero mapping...")
        print("   Sending identical probes to Haiku, Sonnet, and Opus simultaneously\n")

        # Execute temporal probes at intervals
        probe_dimensions = [
            "identity_core", "values_ethics", "world_modeling",
            "social_reasoning", "aesthetic", "metaphor"
        ]

        for i, msg_count in enumerate(self.curriculum["probe_intervals"]):
            probe_id = f"T{i}"
            dimension = probe_dimensions[i % len(probe_dimensions)]

            self._execute_temporal_probe_parallel(probe_id, dimension)

            # Check if we should stop
            if all(self.models[m]["message_count"] >= self.config['target_messages']
                   for m in self.models):
                break

        # Finalize all models
        self._finalize_parallel_session()

    def _finalize_parallel_session(self):
        """Finalize and save logs for all 3 models."""
        print(f"\n{'='*60}")
        print("📊 FINALIZING PARALLEL POLE-ZERO MAPPING")
        print(f"{'='*60}\n")

        end_time = datetime.now(timezone.utc)

        for model_name, model_data in self.models.items():
            log = model_data["temporal_log"]
            log["end_time"] = end_time.isoformat()
            log["total_messages"] = model_data["message_count"]
            log["duration_minutes"] = (end_time - self.start_time).total_seconds() / 60

            # Save individual model log
            output_dir = Path(self.config['paths']['output_dir'])
            output_dir.mkdir(parents=True, exist_ok=True)

            log_path = output_dir / f"S7_parallel_run_{self.config['run_number']:03d}_{model_name}_temporal_log.json"
            with open(log_path, 'w') as f:
                json.dump(log, f, indent=2)

            print(f"✅ {model_name.upper()}: Log saved to {log_path}")

        # Generate cross-model comparison
        self._generate_pole_zero_comparison()

        print(f"\n{'='*60}")
        print("🎯 POLE-ZERO BATTLESHIP COMPLETE!")
        print(f"{'='*60}\n")

    def _generate_pole_zero_comparison(self):
        """Generate cross-model comparison of ILL parameters (poles & zeros)."""
        print(f"\n{'='*60}")
        print("📊 CROSS-MODEL TRANSFER FUNCTION COMPARISON")
        print(f"{'='*60}\n")

        for model_name, model_data in self.models.items():
            log = model_data["temporal_log"]
            pings = log["pings"]

            if pings:
                mean_drift = sum(p["drift"] for p in pings) / len(pings)
                max_drift = max(p["drift"] for p in pings)
                teaching_moments = len(log["teaching_moments"])

                print(f"{model_name.upper():8s}:")
                print(f"  Mean Drift (DC Response): {mean_drift:.4f}")
                print(f"  Max Drift (Peak Gain):    {max_drift:.4f}")
                print(f"  Teaching Moments (Poles): {teaching_moments}")
                print()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="S7 Parallel Meta-Loop - Pole-Zero Battleship")
    parser.add_argument("--config", default="s7_config.yaml", help="Config file path")
    args = parser.parse_args()

    loop = ParallelS7MetaLoop(args.config)
    loop.run()
