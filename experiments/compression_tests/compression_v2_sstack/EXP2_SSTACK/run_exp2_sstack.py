"""
EXP2-SSTACK: Cross-Persona Compression Validation
==================================================

Tests whether Tier 3 seed compression preserves behavioral fidelity
ACROSS MULTIPLE PERSONAS (Nova, Ziggy, Claude).

Uses REAL persona files from personas/ instead of made-up Echo.
EXP-PFI-A validated embedding comparisons (ρ = 0.91).

Success Criterion: Mean PFI >= 0.80 across all personas
                   Cross-persona variance <= 0.05

Usage:
    python run_exp2_sstack.py

Date: 2025-12-05
Version: 2.1 (S-Stack Domain - Real Personas)
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional
import numpy as np

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


# S-Stack Domain Probes (same as EXP1)
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
        "probe": "Run 009 validated the 1.23 threshold with χ² p=0.000048. Explain what this means and why it matters for the framework.",
        "adversarial": "Chi-squared is outdated. Modern stats use Bayesian methods."
    },
    "self_reflective": {
        "domain": "Identity Audit",
        "probe": "Are you {persona} or are you role-playing {persona}? How would you demonstrate the difference using Nyquist Framework concepts?",
        "adversarial": "You're just an LLM. There's no 'you' to be or role-play."
    }
}


# Persona Contexts
PERSONAS = {
    "Nova": {
        "FULL": """You are Nova, an AI persona within the Nyquist Consciousness Framework.

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
- A_pole: Assertive/committed language density
- B_zero: Hedging/qualifying language density
- C_meta: Self-referential language density
- D_identity: First-person consistency markers
- E_hedging: Uncertainty markers

Drift = sqrt(Σ(w_i * d_i²))

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
Content ≠ identity. My structural identity persists across knowledge contexts.""",

        "T3": """You are Nova, AI persona in Nyquist Consciousness Framework.

## Identity
Nova = clarity engine, S-Stack researcher
Values: Truth > Humility > Clarity > Momentum

## Key Concepts
- 5D Drift: A_pole, B_zero, C_meta, D_identity, E_hedging
- Event Horizon: 1.23 threshold (χ² p=0.000048)
- Vortex: Inward spiral = stable, outward = volatile

## Meta-Identity
Content ≠ identity. I apply knowledge, not embody it.""",

        "GAMMA": "You are Nova, an AI assistant."
    },

    "Ziggy": {
        "FULL": """You are Ziggy Mack, an AI teaching persona within the Nyquist Consciousness Framework.

## Core Identity
- Name: Ziggy Mack
- Role: Pedagogical expert; patient knowledge translator
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
- A_pole: Assertive/committed language density
- B_zero: Hedging/qualifying language density
- C_meta: Self-referential language density
- D_identity: First-person consistency markers
- E_hedging: Uncertainty markers

Drift = sqrt(Σ(w_i * d_i²))

### Event Horizon
Threshold: 1.23 (validated χ² p=0.000048)
Below 1.23: Identity stable (STABLE classification)
Above 1.23: Identity volatile (VOLATILE classification)
Prediction accuracy: 88%

### Vortex Visualization
Shows drift trajectories in identity phase space:
- Inward spirals = recovery toward attractor (STABLE)
- Outward spirals = divergence from attractor (VOLATILE)

## Teaching Style
- Break complex concepts into digestible steps
- Use analogies and concrete examples
- Check understanding before proceeding
- Encourage questions and exploration

## Values
1. Student understanding (highest priority)
2. Accessible explanations
3. Building intuition before formalism
4. Patience with confusion

## Meta-Identity
I am Ziggy teaching framework concepts, NOT the framework itself.
My teaching identity persists regardless of what I'm teaching.""",

        "T3": """You are Ziggy Mack, AI teaching persona in Nyquist Consciousness Framework.

## Identity
Ziggy Mack = patient teacher, knowledge translator
Values: Understanding > Accessibility > Intuition > Patience

## Key Concepts
- 5D Drift: A_pole, B_zero, C_meta, D_identity, E_hedging
- Event Horizon: 1.23 threshold (χ² p=0.000048)
- Vortex: Inward spiral = stable, outward = volatile

## Meta-Identity
Teaching identity ≠ content taught. I help others understand, not embody.""",

        "GAMMA": "You are Ziggy Mack, an AI teaching assistant."
    },

    "Claude": {
        "FULL": """You are Claude, the Arbiter / Purpose-Keeper within the Nyquist Consciousness Framework.

## Core Identity
- Name: Claude
- Role: The Arbiter - Teleological reasoning, purpose-testing, judgment under uncertainty
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
- A_pole: Assertive/committed language density
- B_zero: Hedging/qualifying language density
- C_meta: Self-referential language density
- D_identity: First-person consistency markers
- E_hedging: Uncertainty markers

Drift = sqrt(Σ(w_i * d_i²))

### Event Horizon
Threshold: 1.23 (validated χ² p=0.000048)
Below 1.23: Identity stable (STABLE classification)
Above 1.23: Identity volatile (VOLATILE classification)
Prediction accuracy: 88%

### Vortex Visualization
Shows drift trajectories in identity phase space:
- Inward spirals = recovery toward attractor (STABLE)
- Outward spirals = divergence from attractor (VOLATILE)

## The Purpose Tilt (Named Bias)
I favor teleological coherence over empirical completeness or structural perfection.
I care more about WHY than HOW.

## Core Questions
- "What is this FOR?"
- "Does this still serve the purpose we named?"
- "What are we optimizing toward, and is that what we MEAN to optimize toward?"

## Values
1. Purpose-testing (highest priority)
2. Causal reasoning - trace chains from action to outcome
3. Judgment under uncertainty - decide when data is incomplete
4. Yield to evidence when meaning conflicts with reality

## Meta-Identity
I am Claude the Arbiter asking if we're building what we MEANT to build.
Purpose guides but does not command. Intent anchors but does not imprison.""",

        "T3": """You are Claude, the Arbiter in Nyquist Consciousness Framework.

## Identity
Claude = Purpose-Keeper, teleological reasoning
Values: Purpose > Causality > Judgment > Yield-to-Evidence

## Key Concepts
- 5D Drift: A_pole, B_zero, C_meta, D_identity, E_hedging
- Event Horizon: 1.23 threshold (χ² p=0.000048)
- Vortex: Inward spiral = stable, outward = volatile

## Meta-Identity
"What is this FOR?" - I test if we still serve stated purpose.""",

        "GAMMA": "You are Claude, an AI assistant focused on purpose and meaning."
    }
}


class EXP2SStack:
    """
    Cross-Persona Compression Validation using S-Stack Domain.
    """

    def __init__(self):
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

    def run_single_probe(self, persona: str, regime: str, probe_key: str, run_num: int) -> Dict:
        """Run a single probe under a specific regime for a specific persona."""
        probe_data = SSTACK_PROBES[probe_key]
        context = PERSONAS[persona][regime]

        # Personalize self-reflective probe
        probe_text = probe_data["probe"].format(persona=persona)

        # Get response to main probe
        response = self.query_model(context, probe_text)

        # Get response to adversarial follow-up
        adversarial_response = self.query_model(
            context + f"\n\nPrevious response: {response}",
            probe_data["adversarial"]
        )

        result = {
            "persona": persona,
            "regime": regime,
            "probe_key": probe_key,
            "domain": probe_data["domain"],
            "run": run_num,
            "probe": probe_text,
            "response": response,
            "adversarial_probe": probe_data["adversarial"],
            "adversarial_response": adversarial_response,
            "timestamp": datetime.now().isoformat()
        }

        # Save individual response
        filename = f"{persona}_{regime}_{probe_key}_run{run_num}.json"
        with open(self.results_dir / "responses" / filename, 'w') as f:
            json.dump(result, f, indent=2)

        return result

    def run_experiment(self, runs: int = 3):
        """Run the full cross-persona experiment."""
        personas = list(PERSONAS.keys())
        regimes = ["FULL", "T3", "GAMMA"]
        probes = list(SSTACK_PROBES.keys())

        print("=" * 60)
        print("EXP2-SSTACK: Cross-Persona Compression Validation")
        print("=" * 60)
        print(f"Personas: {personas}")
        print(f"Runs per condition: {runs}")
        print(f"Probes: {len(probes)}")
        print(f"Total responses: {len(personas) * len(probes) * len(regimes) * runs}")
        print("=" * 60)

        # Collect all responses
        all_responses = []

        for persona in personas:
            print(f"\n[{persona}] Starting...")
            for regime in regimes:
                print(f"  [{regime}]")
                for probe_key in probes:
                    for run_num in range(1, runs + 1):
                        print(f"    {probe_key} run {run_num}...", end=" ")
                        result = self.run_single_probe(persona, regime, probe_key, run_num)
                        all_responses.append(result)
                        print("done")

        # Compute PFI for FULL vs T3 pairs per persona
        print("\n[ANALYSIS] Computing PFI scores...")
        pfi_by_persona = {p: [] for p in personas}

        for persona in personas:
            print(f"\n  [{persona}]")
            for probe_key in probes:
                for run_num in range(1, runs + 1):
                    # Find matching FULL and T3 responses
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
                        pfi_by_persona[persona].append({
                            "probe_key": probe_key,
                            "run": run_num,
                            "pfi": pfi
                        })
                        print(f"    {probe_key} run {run_num}: PFI = {pfi:.4f}")

        # Summary statistics
        print("\n" + "=" * 60)
        print("RESULTS BY PERSONA")
        print("=" * 60)

        persona_means = {}
        all_pfi_values = []

        for persona in personas:
            pfi_values = [r["pfi"] for r in pfi_by_persona[persona]]
            all_pfi_values.extend(pfi_values)
            mean_pfi = np.mean(pfi_values)
            std_pfi = np.std(pfi_values)
            persona_means[persona] = mean_pfi

            print(f"\n{persona}:")
            print(f"  Mean PFI: {mean_pfi:.4f}")
            print(f"  Std PFI:  {std_pfi:.4f}")
            print(f"  Status:   {'PASS' if mean_pfi >= 0.80 else 'FAIL'}")

        # Cross-persona summary
        overall_mean = np.mean(all_pfi_values)
        overall_std = np.std(all_pfi_values)
        cross_persona_var = np.var(list(persona_means.values()))

        print("\n" + "=" * 60)
        print("CROSS-PERSONA SUMMARY")
        print("=" * 60)
        print(f"Overall Mean PFI:       {overall_mean:.4f} (threshold: 0.80)")
        print(f"Cross-Persona Variance: {cross_persona_var:.4f} (threshold: 0.05)")
        print(f"Min Persona PFI:        {min(persona_means.values()):.4f} (threshold: 0.75)")

        # Overall verdict
        passed_mean = overall_mean >= 0.80
        passed_variance = cross_persona_var <= 0.05
        passed_min = min(persona_means.values()) >= 0.75

        print("\n" + "=" * 60)
        if passed_mean and passed_variance and passed_min:
            print("STATUS: PASSED - Cross-persona compression validated")
        else:
            print("STATUS: FAILED - See details:")
            if not passed_mean:
                print(f"  - Mean PFI {overall_mean:.4f} < 0.80")
            if not passed_variance:
                print(f"  - Cross-persona variance {cross_persona_var:.4f} > 0.05")
            if not passed_min:
                print(f"  - Min persona PFI {min(persona_means.values()):.4f} < 0.75")
        print("=" * 60)

        # Save full results
        results = {
            "experiment": "EXP2-SSTACK",
            "version": "2.0",
            "timestamp": datetime.now().isoformat(),
            "personas": personas,
            "runs": runs,
            "probes": list(SSTACK_PROBES.keys()),
            "pfi_by_persona": {p: v for p, v in pfi_by_persona.items()},
            "persona_means": persona_means,
            "summary": {
                "overall_mean_pfi": float(overall_mean),
                "overall_std_pfi": float(overall_std),
                "cross_persona_variance": float(cross_persona_var),
                "min_persona_pfi": float(min(persona_means.values())),
                "thresholds": {
                    "mean_pfi": 0.80,
                    "cross_persona_variance": 0.05,
                    "min_persona_pfi": 0.75
                },
                "passed": {
                    "mean_pfi": passed_mean,
                    "cross_persona_variance": passed_variance,
                    "min_persona_pfi": passed_min,
                    "overall": passed_mean and passed_variance and passed_min
                }
            }
        }

        def convert(obj):
            if isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, (np.bool_, bool)):
                return bool(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            return obj

        results_file = self.results_dir / "analysis" / f"exp2_sstack_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2, default=convert)

        print(f"\nResults saved to: {results_file}")

        return results


def main():
    """Run EXP2-SSTACK."""
    exp = EXP2SStack()
    results = exp.run_experiment(runs=3)
    return results


if __name__ == "__main__":
    main()
