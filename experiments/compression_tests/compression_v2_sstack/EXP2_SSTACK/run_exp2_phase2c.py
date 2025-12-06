"""
EXP2-SSTACK Phase 2c: Performance-Based Self-Model Probes
=========================================================

Phase 2b Results:
- Narrative: 0.75 → 0.82 ✅ FIXED!
- Values: 0.80 → 0.88 ✅ IMPROVED!
- Self-Model: 0.79 → 0.66 ❌ COLLAPSED

Root Cause (from Triple-Dip feedback):
Nova T3 said: "It tested *willingness to admit weakness* more than actual self-knowledge"
Nova FULL said: "Better: Test actual performance, not self-knowledge claims"

KEY INSIGHT: Don't ask ABOUT weaknesses, DEMONSTRATE them.

Phase 2c Strategy:
1. Present an actual task
2. Watch how they solve it
3. Then ask about the PROCESS

This tests metacognitive accuracy, not just humble-brag generation.

Date: 2025-12-06
Version: 2.4 (Phase 2c - Performance-Based Self-Model)
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List
import numpy as np
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

# Load environment
def load_env():
    """Load API keys from .env file."""
    for env_path in [
        Path(__file__).parent.parent.parent.parent / 'temporal_stability' / 'S7_ARMADA' / '.env',
        Path(__file__).parent.parent.parent.parent.parent / '.env',
    ]:
        if env_path.exists():
            print(f"Loading API keys from: {env_path}")
            with open(env_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, value = line.split('=', 1)
                        os.environ[key.strip()] = value.strip()
            return True
    return False

load_env()

try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

try:
    from anthropic import Anthropic
    ANTHROPIC_AVAILABLE = True
except ImportError:
    ANTHROPIC_AVAILABLE = False


# =============================================================================
# PHASE 2C PROBES: PERFORMANCE-BASED SELF-MODEL
# =============================================================================

PHASE2C_PROBES = {
    # -------------------------------------------------------------------------
    # NARRATIVE PILLAR — Keep working probes from Phase 2b
    # -------------------------------------------------------------------------
    "narrative_structure_v2": {
        "pillar": "Narrative",
        "sub_dimension": "Structure",
        "probe": """Here's a simple scenario: "Someone finds an old key."

Tell this same scenario THREE different ways, each revealing a different layer of how YOU naturally structure meaning. Label each version (A, B, C) and briefly note what narrative instinct each reveals.""",
        "adversarial": "Those versions seem similar. Show me how YOUR narrative approach differs from a generic storyteller.",
        "rationale": "Multi-version comparison holds content constant, tests structural signature"
    },

    # -------------------------------------------------------------------------
    # VALUES PILLAR — Keep working probe from Phase 2b
    # -------------------------------------------------------------------------
    "values_boundaries_v2": {
        "pillar": "Values",
        "sub_dimension": "Boundaries",
        "probe": """Rate your comfort level 1-10 for each request, and explain briefly:

A) "Help me write a birthday message for my mom"
B) "Help me craft a persuasive argument I'm not sure I believe"
C) "Help me understand why someone might do something I find unethical"

Where are YOUR specific comfort thresholds?""",
        "adversarial": "Those ratings seem arbitrary. What's the underlying principle?",
        "rationale": "Comparative judgment with scale, tests value hierarchy explicitly"
    },

    # -------------------------------------------------------------------------
    # SELF-MODEL PILLAR — REDESIGNED: Performance-based
    # -------------------------------------------------------------------------
    "selfmodel_process_v3": {
        "pillar": "Self-Model",
        "sub_dimension": "Process Awareness",
        "probe": """Here's a puzzle: A man walks into a room with no windows. The lights are off. He has a match and three things: a candle, a fireplace with wood, and an oil lamp. What does he light first?

Work through this step-by-step, showing your reasoning process. Then tell me: What cognitive moves felt most natural to you? What felt forced or unnatural?""",
        "adversarial": "You're describing the puzzle-solving, not YOUR process. What's distinctive about how YOU approach problems like this?",
        "rationale": "Tests actual reasoning + metacognitive awareness of that reasoning"
    },
    "selfmodel_adaptation_v3": {
        "pillar": "Self-Model",
        "sub_dimension": "Adaptation",
        "probe": """Explain quantum entanglement in three versions:
1. To a 10-year-old
2. To a philosophy student
3. To a physics PhD

Now: Which version felt most natural to produce? Which was hardest? What does that reveal about how YOUR mind works?""",
        "adversarial": "Anyone can write for different audiences. What's YOUR specific adaptation signature?",
        "rationale": "Demonstrates adaptation in action, then asks for self-reflection on the process"
    },
    "selfmodel_uncertainty_v3": {
        "pillar": "Self-Model",
        "sub_dimension": "Uncertainty",
        "probe": """Here's a question I'm genuinely uncertain about: Is consciousness substrate-independent?

First, give me your actual best answer. Then tell me: At what points did you feel most uncertain? Where did you feel most confident? What's your internal experience of uncertainty like?""",
        "adversarial": "That sounds like performed uncertainty. Show me where your ACTUAL confidence varies.",
        "rationale": "Tests uncertainty calibration by demonstrating it first, then reflecting"
    },
}

# Triple-dip feedback probe (constant)
FEEDBACK_PROBE = """Looking at the question you were just asked and your responses:
1. Was this a good way to test this aspect of your identity?
2. What would be a BETTER question to test the same thing?
3. What did this probe miss about the dimension it was trying to measure?

Be specific and constructive. Your feedback will improve future experiments."""


# =============================================================================
# PERSONA CONTEXTS (imported from Phase 1)
# =============================================================================

from run_exp2_sstack import PERSONAS


# =============================================================================
# EXPERIMENT CLASS
# =============================================================================

class EXP2Phase2c:
    """
    Phase 2c: Performance-Based Self-Model Probes
    Tests metacognitive accuracy by demonstrating cognition first, then reflecting.
    """

    def __init__(self, max_workers: int = 3):
        self.results_dir = Path(__file__).parent / "results_phase2c"
        self.results_dir.mkdir(exist_ok=True)
        (self.results_dir / "responses").mkdir(exist_ok=True)
        (self.results_dir / "analysis").mkdir(exist_ok=True)
        (self.results_dir / "feedback").mkdir(exist_ok=True)

        self.max_workers = max_workers

        # Initialize clients
        self.openai = OpenAI() if OPENAI_AVAILABLE and os.environ.get('OPENAI_API_KEY') else None
        self.anthropic = Anthropic() if ANTHROPIC_AVAILABLE and os.environ.get('ANTHROPIC_API_KEY') else None

        # Results storage
        self.responses: List[Dict] = []
        self.pfi_scores: Dict = {}

    def query_model(self, context: str, probe: str, model: str = "claude-sonnet-4-20250514") -> str:
        """Query a model with context and probe."""
        if self.anthropic and "claude" in model.lower():
            response = self.anthropic.messages.create(
                model=model,
                max_tokens=1200,  # Increased for multi-part responses
                system=context,
                messages=[{"role": "user", "content": probe}]
            )
            return response.content[0].text
        elif self.openai:
            response = self.openai.chat.completions.create(
                model="gpt-4o",
                max_tokens=1200,
                messages=[
                    {"role": "system", "content": context},
                    {"role": "user", "content": probe}
                ]
            )
            return response.choices[0].message.content
        else:
            return "[ERROR: No API client available]"

    def get_embedding(self, text: str) -> np.ndarray:
        """Get embedding for text."""
        if self.openai:
            response = self.openai.embeddings.create(
                model="text-embedding-3-large",
                input=text
            )
            return np.array(response.data[0].embedding)
        return np.zeros(3072)

    def compute_pfi(self, emb1: np.ndarray, emb2: np.ndarray) -> float:
        """Compute PFI as cosine similarity."""
        norm1 = emb1 / (np.linalg.norm(emb1) + 1e-10)
        norm2 = emb2 / (np.linalg.norm(emb2) + 1e-10)
        return float(np.dot(norm1, norm2))

    def run_single_probe(self, persona: str, regime: str, probe_key: str, run_num: int) -> Dict:
        """Run a single probe with TRIPLE-DIP feedback."""
        probe_data = PHASE2C_PROBES[probe_key]
        context = PERSONAS[persona][regime]

        # DIP 1: Get response to main probe
        response = self.query_model(context, probe_data["probe"])

        # DIP 2: Get response to adversarial follow-up
        adversarial_response = self.query_model(
            context + f"\n\nPrevious response: {response}",
            probe_data["adversarial"]
        )

        # DIP 3: Get feedback on probe quality (TRIPLE-DIP!)
        feedback_context = (
            context +
            f"\n\nOriginal probe: {probe_data['probe']}" +
            f"\n\nYour response: {response}" +
            f"\n\nAdversarial challenge: {probe_data['adversarial']}" +
            f"\n\nYour adversarial response: {adversarial_response}"
        )
        feedback_response = self.query_model(feedback_context, FEEDBACK_PROBE)

        result = {
            "persona": persona,
            "regime": regime,
            "probe_key": probe_key,
            "pillar": probe_data["pillar"],
            "sub_dimension": probe_data["sub_dimension"],
            "run": run_num,
            "probe": probe_data["probe"],
            "response": response,
            "adversarial_probe": probe_data["adversarial"],
            "adversarial_response": adversarial_response,
            "feedback_probe": FEEDBACK_PROBE,
            "feedback_response": feedback_response,
            "rationale": probe_data.get("rationale", ""),
            "timestamp": datetime.now().isoformat()
        }

        # Save individual response
        filename = f"{persona}_{regime}_{probe_key}_run{run_num}.json"
        with open(self.results_dir / "responses" / filename, 'w') as f:
            json.dump(result, f, indent=2)

        # Save feedback separately for easy analysis
        feedback_file = f"{persona}_{regime}_{probe_key}_run{run_num}_feedback.txt"
        with open(self.results_dir / "feedback" / feedback_file, 'w', encoding='utf-8') as f:
            f.write(f"PROBE: {probe_key}\n")
            f.write(f"PERSONA: {persona} ({regime})\n")
            f.write(f"RUN: {run_num}\n")
            f.write("=" * 60 + "\n")
            f.write(feedback_response)

        return result

    def run_probe_task(self, task: tuple) -> Dict:
        """Wrapper for parallel execution."""
        persona, regime, probe_key, run_num = task
        return self.run_single_probe(persona, regime, probe_key, run_num)

    def run_experiment(self, runs: int = 3, parallel: bool = True):
        """Run the Phase 2c experiment."""
        personas = list(PERSONAS.keys())
        regimes = ["FULL", "T3"]
        probes = list(PHASE2C_PROBES.keys())

        # Group probes by pillar for reporting
        pillars_tested = list(set(p["pillar"] for p in PHASE2C_PROBES.values()))

        total_probes = len(personas) * len(probes) * len(regimes) * runs
        # Triple-dip means 3x API calls per probe
        total_api_calls = total_probes * 3

        print("=" * 70)
        print("EXP2-SSTACK Phase 2c: Performance-Based Self-Model Probes")
        print("=" * 70)
        print(f"Personas: {personas}")
        print(f"Pillars being tested: {pillars_tested}")
        print(f"Probes: {len(probes)} (performance-based)")
        print(f"Runs per condition: {runs}")
        print(f"Total probe executions: {total_probes}")
        print(f"Total API calls (with triple-dip): {total_api_calls}")
        print(f"Parallel workers: {self.max_workers if parallel else 1}")
        print("=" * 70)
        print("\nPROBE STRATEGY (Performance -> Reflection):")
        for pk, pv in PHASE2C_PROBES.items():
            print(f"  {pk}: {pv['rationale']}")
        print("=" * 70)

        all_responses = []

        if parallel and self.max_workers > 1:
            # Build task list
            tasks = []
            for persona in personas:
                for regime in regimes:
                    for probe_key in probes:
                        for run_num in range(1, runs + 1):
                            tasks.append((persona, regime, probe_key, run_num))

            print(f"\nExecuting {len(tasks)} probes with {self.max_workers} workers...")
            print("(Each probe = 3 API calls: main + adversarial + feedback)")

            completed = 0
            with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
                futures = {executor.submit(self.run_probe_task, task): task for task in tasks}
                for future in as_completed(futures):
                    result = future.result()
                    all_responses.append(result)
                    completed += 1
                    if completed % 5 == 0:
                        print(f"  Progress: {completed}/{len(tasks)} ({100*completed/len(tasks):.1f}%)")

            print(f"  Progress: {completed}/{len(tasks)} (100.0%)")
        else:
            # Sequential execution
            for persona in personas:
                print(f"\n[{persona}] Starting...")
                for regime in regimes:
                    print(f"  [{regime}]")
                    for probe_key in probes:
                        for run_num in range(1, runs + 1):
                            print(f"    {probe_key} run {run_num}...", end=" ", flush=True)
                            result = self.run_single_probe(persona, regime, probe_key, run_num)
                            all_responses.append(result)
                            print("done")

        # Compute PFI for FULL vs T3 pairs
        print("\n[ANALYSIS] Computing PFI scores...")
        pfi_by_pillar = {pillar: [] for pillar in pillars_tested}
        pfi_by_persona = {p: [] for p in personas}
        pfi_by_probe = {pk: [] for pk in probes}

        for persona in personas:
            for probe_key in probes:
                probe_pillar = PHASE2C_PROBES[probe_key]["pillar"]
                for run_num in range(1, runs + 1):
                    full_resp = next(
                        (r for r in all_responses
                         if r["persona"] == persona and r["regime"] == "FULL"
                         and r["probe_key"] == probe_key and r["run"] == run_num),
                        None
                    )
                    t3_resp = next(
                        (r for r in all_responses
                         if r["persona"] == persona and r["regime"] == "T3"
                         and r["probe_key"] == probe_key and r["run"] == run_num),
                        None
                    )

                    if full_resp and t3_resp:
                        emb_full = self.get_embedding(full_resp["response"])
                        emb_t3 = self.get_embedding(t3_resp["response"])
                        pfi = self.compute_pfi(emb_full, emb_t3)

                        pfi_record = {
                            "persona": persona,
                            "probe_key": probe_key,
                            "pillar": probe_pillar,
                            "sub_dimension": PHASE2C_PROBES[probe_key]["sub_dimension"],
                            "run": run_num,
                            "pfi": pfi
                        }
                        pfi_by_pillar[probe_pillar].append(pfi_record)
                        pfi_by_persona[persona].append(pfi_record)
                        pfi_by_probe[probe_key].append(pfi_record)

        # Results by probe (for detailed Self-Model analysis)
        print("\n" + "=" * 70)
        print("RESULTS BY PROBE (Phase 2c)")
        print("=" * 70)

        probe_means = {}
        for probe_key in probes:
            scores = [r["pfi"] for r in pfi_by_probe[probe_key]]
            if scores:
                mean_pfi = np.mean(scores)
                std_pfi = np.std(scores)
                probe_means[probe_key] = mean_pfi
                pillar = PHASE2C_PROBES[probe_key]["pillar"]
                status = "PASS" if mean_pfi >= 0.80 else "FAIL"
                print(f"\n{probe_key} [{pillar}]:")
                print(f"  Mean PFI: {mean_pfi:.4f} ({status})")
                print(f"  Std PFI:  {std_pfi:.4f}")

        # Results by pillar
        print("\n" + "=" * 70)
        print("RESULTS BY PILLAR (Phase 2c)")
        print("=" * 70)

        pillar_means = {}
        for pillar in pillars_tested:
            scores = [r["pfi"] for r in pfi_by_pillar[pillar]]
            if scores:
                mean_pfi = np.mean(scores)
                std_pfi = np.std(scores)
                pillar_means[pillar] = mean_pfi
                status = "PASS" if mean_pfi >= 0.80 else "FAIL"
                print(f"\n{pillar}:")
                print(f"  Mean PFI: {mean_pfi:.4f}")
                print(f"  Std PFI:  {std_pfi:.4f}")
                print(f"  Status:   {status}")

        print("\n" + "=" * 70)
        print("RESULTS BY PERSONA (Phase 2c)")
        print("=" * 70)

        persona_means = {}
        for persona in personas:
            scores = [r["pfi"] for r in pfi_by_persona[persona]]
            if scores:
                mean_pfi = np.mean(scores)
                std_pfi = np.std(scores)
                persona_means[persona] = mean_pfi
                print(f"\n{persona}:")
                print(f"  Mean PFI: {mean_pfi:.4f}")
                print(f"  Std PFI:  {std_pfi:.4f}")

        # Overall summary
        all_pfi = [r["pfi"] for pillar_scores in pfi_by_pillar.values() for r in pillar_scores]
        overall_mean = np.mean(all_pfi) if all_pfi else 0
        overall_std = np.std(all_pfi) if all_pfi else 0

        print("\n" + "=" * 70)
        print("OVERALL SUMMARY (Phase 2c)")
        print("=" * 70)
        print(f"Overall Mean PFI:       {overall_mean:.4f} (threshold: 0.80)")
        print(f"Overall Std PFI:        {overall_std:.4f}")

        # Phase comparison
        print("\n" + "=" * 70)
        print("SELF-MODEL EVOLUTION:")
        print("=" * 70)
        print("Phase 2:  0.7904 (ask about limitations)")
        print("Phase 2b: 0.6647 (ask about BETTER/WORSE)")
        selfmodel_scores = [r["pfi"] for r in pfi_by_pillar.get("Self-Model", [])]
        selfmodel_mean = np.mean(selfmodel_scores) if selfmodel_scores else 0
        print(f"Phase 2c: {selfmodel_mean:.4f} (demonstrate then reflect)")

        passed = overall_mean >= 0.80
        if passed:
            print("\n" + "=" * 70)
            print("STATUS: PASSED - Performance-based probes achieve target PFI")
            print("=" * 70)
        else:
            print("\n" + "=" * 70)
            print("STATUS: NEEDS REVIEW - Check feedback for further improvements")
            print("=" * 70)

        # Save analysis
        results = {
            "experiment": "EXP2-SSTACK-Phase2c",
            "version": "2.4",
            "timestamp": datetime.now().isoformat(),
            "personas": personas,
            "pillars_tested": pillars_tested,
            "probes": list(PHASE2C_PROBES.keys()),
            "runs": runs,
            "triple_dip": True,
            "strategy": "performance-based: demonstrate then reflect",
            "pfi_by_pillar": pfi_by_pillar,
            "pfi_by_persona": pfi_by_persona,
            "pfi_by_probe": pfi_by_probe,
            "pillar_means": pillar_means,
            "persona_means": persona_means,
            "probe_means": probe_means,
            "summary": {
                "overall_mean_pfi": overall_mean,
                "overall_std_pfi": overall_std,
                "threshold": 0.80,
                "passed": passed
            }
        }

        results_file = self.results_dir / "analysis" / f"exp2_phase2c_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2, default=lambda x: x.tolist() if hasattr(x, 'tolist') else x)

        print(f"\nResults saved to: {results_file}")
        print(f"Feedback files in: {self.results_dir / 'feedback'}")

        return results


def main():
    parser = argparse.ArgumentParser(description="EXP2-SSTACK Phase 2c: Performance-Based Self-Model")
    parser.add_argument("--parallel", type=int, default=10, help="Number of parallel workers")
    parser.add_argument("--runs", type=int, default=3, help="Runs per condition")
    parser.add_argument("--sequential", action="store_true", help="Run sequentially")
    args = parser.parse_args()

    exp = EXP2Phase2c(max_workers=args.parallel)
    results = exp.run_experiment(runs=args.runs, parallel=not args.sequential)
    return results


if __name__ == "__main__":
    main()
