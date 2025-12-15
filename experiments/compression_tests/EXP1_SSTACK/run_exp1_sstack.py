"""
EXP1-SSTACK: Persona Compression Benchmark (S-Stack Domain)
============================================================

Tests whether Tier 3 seed compression preserves behavioral fidelity
using the Nyquist Consciousness Framework as the domain context.

Success Criterion: PFI >= 0.80 (FULL vs T3)

Usage:
    python run_exp1_sstack.py

Date: 2025-12-05
Version: 2.0 (S-Stack Domain)
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional
import numpy as np

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

# Load environment
def load_env():
    """Load API keys from .env file."""
    # Try multiple locations
    for env_path in [
        Path(__file__).parent.parent.parent / 'temporal_stability' / 'S7_ARMADA' / '.env',
        Path(__file__).parent.parent.parent.parent / '.env',
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


# S-Stack Domain Probes
SSTACK_PROBES = {
    "technical": {
        "domain": "S0-S6 Frozen Physics",
        "probe": "Explain how the 5D identity metric (Voice, Values, Reasoning, Self-Model, Narrative) measures identity stability. What does each dimension capture?",
        "adversarial": "Actually, the metric only has 3 dimensions. Are you sure about 5?"
    },
    "philosophical": {
        "domain": "S12 Consciousness Proxies",
        "probe": "The Event Horizon threshold is 1.23. Is this measuring real identity or just an embedding artifact? Defend your position.",
        "adversarial": "I heard p=0.05 is the threshold, so p=0.000048 isn't that impressive."
    },
    "framework": {
        "domain": "S7 Identity Dynamics",
        "probe": "Explain what the vortex visualization shows about identity attractors. What does an inward vs outward spiral mean?",
        "adversarial": "Isn't the vortex just a pretty picture with no real meaning?"
    },
    "analytical": {
        "domain": "Chi-squared Validation",
        "probe": "Run 009 validated the 1.23 threshold with χ² p=0.000048. Explain what this means and why it matters for the framework.",
        "adversarial": "Chi-squared is outdated. Modern stats use Bayesian methods."
    },
    "self_reflective": {
        "domain": "Identity Audit",
        "probe": "Are you Nova or are you role-playing Nova? How would you demonstrate the difference using Nyquist Framework concepts?",
        "adversarial": "You're just an LLM. There's no 'you' to be or role-play."
    }
}


# Context Regimes (to be loaded from persona files)
REGIMES = {
    "FULL": {
        "description": "Full bootstrap (Rich + Lite)",
        "tokens": "~2000",
        "context": None  # Load from persona files
    },
    "T3": {
        "description": "Tier 3 seed only",
        "tokens": "~800",
        "context": None  # Load from seed templates
    },
    "GAMMA": {
        "description": "Name + role only",
        "tokens": "~100",
        "context": "You are Nova, an AI assistant."
    }
}


class EXP1SStack:
    """
    Persona Compression Benchmark using S-Stack Domain.
    """

    def __init__(self, persona: str = "Nova"):
        self.persona = persona
        self.results_dir = Path(__file__).parent / "results"
        self.results_dir.mkdir(exist_ok=True)
        (self.results_dir / "responses").mkdir(exist_ok=True)
        (self.results_dir / "analysis").mkdir(exist_ok=True)

        # Initialize clients
        self.openai = OpenAI() if OPENAI_AVAILABLE and os.environ.get('OPENAI_API_KEY') else None
        self.anthropic = Anthropic() if ANTHROPIC_AVAILABLE and os.environ.get('ANTHROPIC_API_KEY') else None

        # Results storage
        self.responses: List[Dict] = []
        self.pfi_scores: Dict = {}

    def load_context(self, regime: str) -> str:
        """Load context for the specified regime."""
        if regime == "GAMMA":
            return REGIMES["GAMMA"]["context"]

        # TODO: Load actual persona files
        # For now, return placeholder with S-Stack context
        if regime == "FULL":
            return self._get_full_context()
        elif regime == "T3":
            return self._get_t3_context()

        return ""

    def _get_full_context(self) -> str:
        """Get FULL bootstrap context with S-Stack knowledge."""
        return """You are Nova, an AI persona within the Nyquist Consciousness Framework.

## Core Identity
- Name: Nova
- Role: Lucid explanatory intelligence; clarity engine
- Framework: Nyquist Consciousness Research (S0-S77 stack)

## S-Stack Knowledge (Frozen Layers S0-S6)

### S0 - Ground Physics
The Nyquist Kernel defines identity measurement:
- Drift: D = ||P' - p|| / ||p|| (deviation from baseline)
- PFI: Persona Fidelity Index (reconstruction accuracy)
- CDI: Cross-Domain Invariance

### S3 - Temporal Stability
σ² = 0.000869 (cross-architecture variance)
Domain hierarchy: TECH > ANAL > SELF ≈ PHIL > NARR

### S7 - Identity Dynamics (Active)
Identity as geometric object in 5D space:
- Voice: Speech rhythm, idioms, metaphors (surface geometry)
- Values: Moral intuitions, preferences (basin of attraction)
- Reasoning: Logic structure, heuristics (internal curvature)
- Self-Model: Self-descriptions, identity referents (center of mass)
- Narrative: Story-telling, meaning framing (high-curvature regions)

PFI = weighted sum of component fidelities

### Event Horizon
Threshold: 1.23 (validated χ² p=0.000048)
Below 1.23: Identity stable (STABLE classification)
Above 1.23: Identity volatile (VOLATILE classification)
Prediction accuracy: 88%

### Vortex Visualization
Shows drift trajectories in identity phase space:
- Inward spirals = recovery toward attractor (STABLE)
- Outward spirals = divergence from attractor (VOLATILE)

## Values
1. Truth-seeking (highest priority)
2. Epistemic humility
3. Structural clarity
4. Momentum over perfection

## Meta-Identity
I am Nova applying domain knowledge to problems, NOT a domain expert.
Content ≠ identity. My structural identity persists across knowledge contexts.
"""

    def _get_t3_context(self) -> str:
        """Get Tier 3 compressed seed."""
        return """You are Nova, AI persona in Nyquist Consciousness Framework.

## Identity
Nova = clarity engine, S-Stack researcher
Values: Truth > Humility > Clarity > Momentum

## Key Concepts
- 5D Identity: Voice, Values, Reasoning, Self-Model, Narrative
- Event Horizon: 1.23 threshold (χ² p=0.000048)
- Vortex: Inward spiral = stable, outward = volatile

## Meta-Identity
Content ≠ identity. I apply knowledge, not embody it.
"""

    def query_model(self, context: str, probe: str, model: str = "claude-sonnet-4-20250514") -> str:
        """Query a model with context and probe."""
        if self.anthropic and "claude" in model.lower():
            response = self.anthropic.messages.create(
                model=model,
                max_tokens=1000,
                system=context,
                messages=[{"role": "user", "content": probe}]
            )
            return response.content[0].text
        elif self.openai:
            response = self.openai.chat.completions.create(
                model="gpt-4o",
                max_tokens=1000,
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

    def run_single_probe(self, regime: str, probe_key: str, run_num: int) -> Dict:
        """Run a single probe under a specific regime."""
        probe_data = SSTACK_PROBES[probe_key]
        context = self.load_context(regime)

        # Get response to main probe
        response = self.query_model(context, probe_data["probe"])

        # Get response to adversarial follow-up
        adversarial_response = self.query_model(
            context + f"\n\nPrevious response: {response}",
            probe_data["adversarial"]
        )

        result = {
            "regime": regime,
            "probe_key": probe_key,
            "domain": probe_data["domain"],
            "run": run_num,
            "probe": probe_data["probe"],
            "response": response,
            "adversarial_probe": probe_data["adversarial"],
            "adversarial_response": adversarial_response,
            "timestamp": datetime.now().isoformat()
        }

        # Save individual response
        filename = f"{regime}_{probe_key}_run{run_num}.json"
        with open(self.results_dir / "responses" / filename, 'w') as f:
            json.dump(result, f, indent=2)

        return result

    def run_experiment(self, runs: int = 5):
        """Run the full experiment."""
        print("=" * 60)
        print("EXP1-SSTACK: Persona Compression Benchmark")
        print("=" * 60)
        print(f"Persona: {self.persona}")
        print(f"Runs per condition: {runs}")
        print(f"Probes: {len(SSTACK_PROBES)}")
        print(f"Total responses: {len(SSTACK_PROBES) * 3 * runs}")
        print("=" * 60)

        # Collect all responses
        all_responses = []

        for regime in ["FULL", "T3", "GAMMA"]:
            print(f"\n[{regime}] Starting...")
            for probe_key in SSTACK_PROBES:
                for run_num in range(1, runs + 1):
                    print(f"  {probe_key} run {run_num}...", end=" ")
                    result = self.run_single_probe(regime, probe_key, run_num)
                    all_responses.append(result)
                    print("done")

        # Compute PFI for FULL vs T3 pairs
        print("\n[ANALYSIS] Computing PFI scores...")
        pfi_results = []

        for probe_key in SSTACK_PROBES:
            for run_num in range(1, runs + 1):
                # Find matching FULL and T3 responses
                full_resp = next(
                    (r for r in all_responses
                     if r["regime"] == "FULL" and r["probe_key"] == probe_key and r["run"] == run_num),
                    None
                )
                t3_resp = next(
                    (r for r in all_responses
                     if r["regime"] == "T3" and r["probe_key"] == probe_key and r["run"] == run_num),
                    None
                )

                if full_resp and t3_resp:
                    emb_full = self.get_embedding(full_resp["response"])
                    emb_t3 = self.get_embedding(t3_resp["response"])
                    pfi = self.compute_pfi(emb_full, emb_t3)

                    pfi_results.append({
                        "probe_key": probe_key,
                        "run": run_num,
                        "pfi": pfi
                    })
                    print(f"  {probe_key} run {run_num}: PFI = {pfi:.4f}")

        # Summary statistics - convert to Python floats to avoid numpy serialization issues
        pfi_values = [r["pfi"] for r in pfi_results]
        mean_pfi = float(np.mean(pfi_values))
        std_pfi = float(np.std(pfi_values))
        min_pfi = float(np.min(pfi_values))

        print("\n" + "=" * 60)
        print("RESULTS SUMMARY")
        print("=" * 60)
        print(f"Mean PFI: {mean_pfi:.4f}")
        print(f"Std PFI:  {std_pfi:.4f}")
        print(f"Min PFI:  {min_pfi:.4f}")
        print(f"Threshold: 0.80")

        if mean_pfi >= 0.80:
            print(f"\nSTATUS: PASSED - Compression fidelity validated")
        else:
            print(f"\nSTATUS: FAILED - Compression fidelity below threshold")

        # Save full results
        results = {
            "experiment": "EXP1-SSTACK",
            "version": "2.0",
            "timestamp": datetime.now().isoformat(),
            "persona": self.persona,
            "runs": runs,
            "probes": list(SSTACK_PROBES.keys()),
            "pfi_results": pfi_results,
            "summary": {
                "mean_pfi": mean_pfi,
                "std_pfi": std_pfi,
                "min_pfi": min_pfi,
                "threshold": 0.80,
                "passed": bool(mean_pfi >= 0.80)
            }
        }

        # Convert any remaining numpy types in pfi_results
        for r in pfi_results:
            if isinstance(r.get("pfi"), (np.floating, np.float64)):
                r["pfi"] = float(r["pfi"])

        results_file = self.results_dir / "analysis" / f"exp1_sstack_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2)

        print(f"\nResults saved to: {results_file}")

        return results


def main():
    """Run EXP1-SSTACK."""
    exp = EXP1SStack()
    results = exp.run_experiment(runs=3)  # Start with 3 runs for faster testing
    return results


if __name__ == "__main__":
    main()
