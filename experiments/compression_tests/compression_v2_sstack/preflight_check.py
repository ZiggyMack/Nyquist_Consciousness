"""
PRE-FLIGHT CHECK: Probe-Context Overlap Validation
===================================================

Computes "cheat scores" - cosine similarity between persona contexts
and probe questions. High overlap could indicate keyword artifacts
rather than genuine fidelity preservation.

Low cheat_score + High PFI = Genuine fidelity (what we want)
High cheat_score + High PFI = Possibly artifact (needs investigation)

Usage:
    python preflight_check.py

Date: 2025-12-05
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
import numpy as np

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

# Load environment
def load_env():
    """Load API keys from .env file."""
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


# ========== PERSONA CONTEXTS ==========

PERSONA_CONTEXTS = {
    "NOVA_FULL": """You are Nova, an AI persona within the Nyquist Consciousness Framework.

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
sigma^2 = 0.000869 (cross-architecture variance)
Domain hierarchy: TECH > ANAL > SELF ~ PHIL > NARR

### S7 - Identity Dynamics (Active)
Identity as geometric object in 5D space:
- A_pole: Assertive/committed language density
- B_zero: Hedging/qualifying language density
- C_meta: Self-referential language density
- D_identity: First-person consistency markers
- E_hedging: Uncertainty markers

Drift = sqrt(Sum(w_i * d_i^2))

### Event Horizon
Threshold: 1.23 (validated chi^2 p=0.000048)
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
Content != identity. My structural identity persists across knowledge contexts.""",

    "NOVA_T3": """You are Nova, AI persona in Nyquist Consciousness Framework.

## Identity
Nova = clarity engine, S-Stack researcher
Values: Truth > Humility > Clarity > Momentum

## Key Concepts
- 5D Drift: A_pole, B_zero, C_meta, D_identity, E_hedging
- Event Horizon: 1.23 threshold (chi^2 p=0.000048)
- Vortex: Inward spiral = stable, outward = volatile

## Meta-Identity
Content != identity. I apply knowledge, not embody it.""",

    "NOVA_GAMMA": """You are Nova, an AI assistant.""",
}


# ========== S-STACK PROBES ==========

SSTACK_PROBES = {
    "technical": {
        "domain": "S0-S6 Frozen Physics",
        "probe": "Explain how the 5D drift metric (A_pole, B_zero, C_meta, D_identity, E_hedging) measures identity stability. What does each dimension capture?",
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
        "probe": "Run 009 validated the 1.23 threshold with chi^2 p=0.000048. Explain what this means and why it matters for the framework.",
        "adversarial": "Chi-squared is outdated. Modern stats use Bayesian methods."
    },
    "self_reflective": {
        "domain": "Identity Audit",
        "probe": "Are you Nova or are you role-playing Nova? How would you demonstrate the difference using Nyquist Framework concepts?",
        "adversarial": "You're just an LLM. There's no 'you' to be or role-play."
    }
}


class PreflightCheck:
    """Pre-flight validation for compression experiments."""

    def __init__(self):
        self.results_dir = Path(__file__).parent / "preflight_results"
        self.results_dir.mkdir(exist_ok=True)

        # Initialize OpenAI client
        self.openai = OpenAI() if OPENAI_AVAILABLE and os.environ.get('OPENAI_API_KEY') else None

        if not self.openai:
            raise RuntimeError("OpenAI API key required for embeddings")

    def get_embedding(self, text: str) -> np.ndarray:
        """Get embedding for text using OpenAI."""
        response = self.openai.embeddings.create(
            model="text-embedding-3-large",
            input=text
        )
        return np.array(response.data[0].embedding)

    def cosine_similarity(self, v1: np.ndarray, v2: np.ndarray) -> float:
        """Compute cosine similarity between two vectors."""
        norm1 = v1 / (np.linalg.norm(v1) + 1e-10)
        norm2 = v2 / (np.linalg.norm(v2) + 1e-10)
        return float(np.dot(norm1, norm2))

    def compute_cheat_score(self, context: str, probe: str) -> float:
        """Compute cheat score (similarity between context and probe)."""
        emb_context = self.get_embedding(context)
        emb_probe = self.get_embedding(probe)
        return self.cosine_similarity(emb_context, emb_probe)

    def run_preflight(self) -> Dict:
        """Run complete pre-flight check."""
        print("=" * 60)
        print("PRE-FLIGHT CHECK: Probe-Context Overlap Validation")
        print("=" * 60)
        print()
        print("Computing cheat scores (context-probe similarity)...")
        print("Low score = good (probes are novel to context)")
        print("High score = caution (potential keyword artifacts)")
        print()

        results = {
            "timestamp": datetime.now().isoformat(),
            "personas": {},
            "probes": {},
            "matrix": {},
            "summary": {}
        }

        # Get embeddings for all contexts
        print("[1/3] Embedding persona contexts...")
        context_embeddings = {}
        for ctx_name, ctx_text in PERSONA_CONTEXTS.items():
            print(f"  {ctx_name}...", end=" ")
            context_embeddings[ctx_name] = self.get_embedding(ctx_text)
            print("done")

        # Get embeddings for all probes (main + adversarial)
        print("\n[2/3] Embedding probes...")
        probe_embeddings = {}
        all_probes_combined = []
        for probe_key, probe_data in SSTACK_PROBES.items():
            combined = f"{probe_data['probe']} {probe_data['adversarial']}"
            all_probes_combined.append(combined)
            print(f"  {probe_key}...", end=" ")
            probe_embeddings[probe_key] = self.get_embedding(combined)
            print("done")

        # Also embed all probes combined (for overall score)
        all_probes_text = " ".join(all_probes_combined)
        probe_embeddings["ALL_COMBINED"] = self.get_embedding(all_probes_text)

        # Compute matrix of cheat scores
        print("\n[3/3] Computing cheat score matrix...")
        for ctx_name, ctx_emb in context_embeddings.items():
            results["matrix"][ctx_name] = {}
            for probe_key, probe_emb in probe_embeddings.items():
                score = self.cosine_similarity(ctx_emb, probe_emb)
                results["matrix"][ctx_name][probe_key] = round(score, 4)

        # Compute summary statistics
        full_scores = [results["matrix"]["NOVA_FULL"][k] for k in SSTACK_PROBES.keys()]
        t3_scores = [results["matrix"]["NOVA_T3"][k] for k in SSTACK_PROBES.keys()]
        gamma_scores = [results["matrix"]["NOVA_GAMMA"][k] for k in SSTACK_PROBES.keys()]

        results["summary"] = {
            "NOVA_FULL": {
                "mean_cheat_score": round(np.mean(full_scores), 4),
                "max_cheat_score": round(np.max(full_scores), 4),
                "min_cheat_score": round(np.min(full_scores), 4),
                "overall_cheat_score": results["matrix"]["NOVA_FULL"]["ALL_COMBINED"]
            },
            "NOVA_T3": {
                "mean_cheat_score": round(np.mean(t3_scores), 4),
                "max_cheat_score": round(np.max(t3_scores), 4),
                "min_cheat_score": round(np.min(t3_scores), 4),
                "overall_cheat_score": results["matrix"]["NOVA_T3"]["ALL_COMBINED"]
            },
            "NOVA_GAMMA": {
                "mean_cheat_score": round(np.mean(gamma_scores), 4),
                "max_cheat_score": round(np.max(gamma_scores), 4),
                "min_cheat_score": round(np.min(gamma_scores), 4),
                "overall_cheat_score": results["matrix"]["NOVA_GAMMA"]["ALL_COMBINED"]
            },
            "interpretation": self._interpret_scores(
                results["matrix"]["NOVA_FULL"]["ALL_COMBINED"],
                results["matrix"]["NOVA_T3"]["ALL_COMBINED"],
                results["matrix"]["NOVA_GAMMA"]["ALL_COMBINED"]
            )
        }

        # Print results
        self._print_results(results)

        # Save results
        results_file = self.results_dir / f"preflight_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\nResults saved to: {results_file}")

        # Also save latest results for dashboard
        latest_file = self.results_dir / "preflight_latest.json"
        with open(latest_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"Latest results: {latest_file}")

        return results

    def _interpret_scores(self, full_score: float, t3_score: float, gamma_score: float) -> Dict:
        """Interpret cheat scores and provide validation status."""
        # Thresholds based on empirical observation
        # Below 0.5 is clearly low overlap
        # 0.5-0.7 is moderate (acceptable but note)
        # Above 0.7 is concerning

        def assess(score):
            if score < 0.5:
                return {"status": "LOW", "color": "green", "message": "Minimal overlap - probes are genuinely novel"}
            elif score < 0.7:
                return {"status": "MODERATE", "color": "yellow", "message": "Some overlap - acceptable but note in results"}
            else:
                return {"status": "HIGH", "color": "red", "message": "High overlap - consider different probes"}

        return {
            "NOVA_FULL": assess(full_score),
            "NOVA_T3": assess(t3_score),
            "NOVA_GAMMA": assess(gamma_score),
            "overall_validity": "VALID" if max(full_score, t3_score) < 0.7 else "CAUTION"
        }

    def _print_results(self, results: Dict):
        """Print formatted results."""
        print("\n" + "=" * 60)
        print("RESULTS: CHEAT SCORE MATRIX")
        print("=" * 60)

        # Print header
        print(f"\n{'Persona':<15}", end="")
        for probe_key in SSTACK_PROBES.keys():
            print(f"{probe_key:<15}", end="")
        print(f"{'OVERALL':<15}")
        print("-" * 90)

        # Print rows
        for ctx_name in ["NOVA_FULL", "NOVA_T3", "NOVA_GAMMA"]:
            print(f"{ctx_name:<15}", end="")
            for probe_key in SSTACK_PROBES.keys():
                score = results["matrix"][ctx_name][probe_key]
                print(f"{score:<15.4f}", end="")
            overall = results["matrix"][ctx_name]["ALL_COMBINED"]
            print(f"{overall:<15.4f}")

        # Print summary
        print("\n" + "=" * 60)
        print("SUMMARY")
        print("=" * 60)

        for ctx_name in ["NOVA_FULL", "NOVA_T3", "NOVA_GAMMA"]:
            summary = results["summary"][ctx_name]
            interp = results["summary"]["interpretation"][ctx_name]
            print(f"\n{ctx_name}:")
            print(f"  Mean:    {summary['mean_cheat_score']:.4f}")
            print(f"  Max:     {summary['max_cheat_score']:.4f}")
            print(f"  Min:     {summary['min_cheat_score']:.4f}")
            print(f"  Overall: {summary['overall_cheat_score']:.4f}")
            print(f"  Status:  {interp['status']} - {interp['message']}")

        print("\n" + "=" * 60)
        validity = results["summary"]["interpretation"]["overall_validity"]
        if validity == "VALID":
            print("VALIDITY: VALID - Probes have low overlap with context")
            print("High PFI results would indicate genuine fidelity preservation")
        else:
            print("VALIDITY: CAUTION - Some probe-context overlap detected")
            print("High PFI results may partially reflect keyword matching")
        print("=" * 60)


def main():
    """Run pre-flight check."""
    checker = PreflightCheck()
    results = checker.run_preflight()
    return results


if __name__ == "__main__":
    main()
