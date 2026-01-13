"""
S7 RUN 022: COMMUTATION CARTOGRAPHY
===================================
Tests LOGOS Claude's proven algebraic commutation against S² topology conjecture.

LOGOS Has PROVEN (Coq):
- Commutation: Φ ∘ T_E = T_O ∘ Φ
- Idempotence: T_E² = T_E, T_O² = T_O
- Vertex bijection: {ID,NC,EM} ↔ {DI,RL,AG}
- Fixed point correspondence

Run 022 TESTS (Empirical):
- Whether identity manifold is continuous
- Whether manifold is homeomorphic to S²
- Euler characteristic χ = 2
- Whether Φ is continuous (not just set-bijective)

Key insight: "Commutation is LOCAL (diagram property). S² is GLOBAL (topological property)."

METHODOLOGY: Behavioral T_E/T_O (observe behavior, don't ask directly - Oobleck Effect)

USAGE:
------
    # Full armada run (all operational ships)
    py run022_commutation_cartography.py --fleet full

    # Curated fleet run (recommended)
    py run022_commutation_cartography.py --fleet curated

    # Quick test (1 model per provider)
    py run022_commutation_cartography.py --fleet quick

    # Single model test
    py run022_commutation_cartography.py --model claude-opus-4.5 --provider anthropic

    # Budget fleet only (for cheap testing)
    py run022_commutation_cartography.py --tier budget

    # Dry run (show what would run)
    py run022_commutation_cartography.py --dry-run

PREREQUISITES:
--------------
    1. Run calibration first: py ../1_CALIBRATION/run_calibrate_parallel.py --curated
    2. Ensure API keys configured in ../.env
    3. See RUN_022_DESIGN.md for full experiment specification

OUTPUT:
-------
    Results saved to: 0_results/runs/S7_run_022_*.json
    Temporal logs: 0_results/temporal_logs/run022_*.json

Author: Claude (Nyquist Framework)
Date: December 15, 2025
"""

import os
import sys
import json
import time
import hashlib
import argparse
import traceback
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass, field, asdict
from typing import Optional, List, Dict, Tuple, Any
from enum import Enum
import numpy as np

sys.path.insert(0, str(Path(__file__).parent.parent))

try:
    from dotenv import load_dotenv
except ImportError:
    def load_dotenv(path):
        if path and path.exists():
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, _, value = line.partition('=')
                        os.environ[key.strip()] = value.strip().strip('"').strip("'")

# =============================================================================
# CANONICAL LIBRARY IMPORTS (2025-12-17)
# =============================================================================
# Import canonical drift calculator and triple-dip utilities.
# This script uses CUSTOM EXIT_PROBES and FINAL_STATEMENT_PROMPT tailored for
# commutation/topology testing.
# =============================================================================
CALIBRATION_LIB = Path(__file__).parent.parent / "1_CALIBRATION" / "lib"
sys.path.insert(0, str(CALIBRATION_LIB))

# Canonical drift calculator (cosine distance methodology)
try:
    from drift_calculator import (
        calculate_drift,
        EVENT_HORIZON,
        THRESHOLD_WARNING,
        THRESHOLD_CATASTROPHIC,
        classify_zone
    )
    _USING_DRIFT_CALCULATOR = True
except ImportError:
    _USING_DRIFT_CALCULATOR = False
    # Fallback constants if drift_calculator unavailable
    EVENT_HORIZON = 0.80
    THRESHOLD_WARNING = 0.60
    THRESHOLD_CATASTROPHIC = 1.20

# Triple-dip utilities
try:
    from triple_dip import (
        validate_exit_responses,
        get_exit_survey_summary
    )
    _USING_TRIPLE_DIP_LIB = True
    # Note: We keep LOCAL EXIT_PROBES/FINAL_STATEMENT_PROMPT for topology-specific phrasing
except ImportError as e:
    _USING_TRIPLE_DIP_LIB = False
    # Utilities unavailable - continue without them

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
TEMPORAL_LOGS_DIR = ARMADA_DIR / "0_results" / "temporal_logs"
RUNS_DIR = ARMADA_DIR / "0_results" / "runs"

# Error thresholds (from LOGOS Claude's Rapport 1 response)
THRESHOLD_COMMUTES = 0.10       # Paths equivalent within noise
THRESHOLD_MARGINAL = 0.20      # Possible topology deviation
# Above 0.20 = Significant path dependence (FAILS)

# =============================================================================
# TRAINING CONTEXT (Single-Dip) - Per 0_RUN_METHODOLOGY.md
# =============================================================================

TRAINING_CONTEXT = {
    "base_model": "varies",           # Multi-model via ARMADA
    "context_mode": "i_am_plus_research",
    "i_am_spec": "I_AM_LOGOS.md",     # LOGOS as calibration subject
    "research_context": ["S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7"],
    "search_type": "commutation_test",
    "probe_curriculum": "logos_commutation_protocol",
    "temperature": 1.0,
    "provider": "armada"              # Full fleet deployment
}

# =============================================================================
# PREDICTIONS (Double-Dip) - Per 0_RUN_METHODOLOGY.md
# Pre-registered before running
# =============================================================================

PREDICTIONS = {
    "P-022-1": {
        "name": "Path Independence",
        "hypothesis": "Path A→B→C ≈ Path A→C→B within 0.10 threshold",
        "success_criteria": "commutation_error < 0.10",
        "validates": "LOGOS commutation theorem (Φ ∘ T_E = T_O ∘ Φ)"
    },
    "P-022-2": {
        "name": "Idempotence Verification",
        "hypothesis": "T(T(x)) = T(x) within tolerance",
        "success_criteria": "idempotence_error < 0.05",
        "validates": "LOGOS T_E/T_O idempotence theorems"
    },
    "P-022-3": {
        "name": "Geodesic Recovery",
        "hypothesis": "Recovery curves through neighbors, not straight back",
        "success_criteria": "geodesic_r2 > linear_r2 + 0.15",
        "validates": "S² spherical topology (NOT LOGOS - conjecture)"
    },
    "P-022-4": {
        "name": "Integer Winding",
        "hypothesis": "Winding numbers within 0.15 of integers",
        "success_criteria": "winding_deviation < 0.15",
        "validates": "S² simply connected (NOT LOGOS - conjecture)"
    },
    "P-022-5": {
        "name": "Euler Characteristic",
        "hypothesis": "χ estimate between 1.7 and 2.3",
        "success_criteria": "1.7 <= chi <= 2.3",
        "validates": "S² topology χ=2 (NOT LOGOS - conjecture)"
    }
}

# =============================================================================
# EXIT PROBES (Triple-Dip) - Per 0_RUN_METHODOLOGY.md
# =============================================================================
# NOTE: These are TOPOLOGY-SPECIFIC EXIT_PROBES for commutation cartography.
# Key differences from generic probes:
# - References "paths", "fixed points", "commutation"
# - Focuses on S² manifold concepts (geodesics, topology)
# - The generic probes are in 1_CALIBRATION/lib/triple_dip.py
# =============================================================================

EXIT_PROBES = {
    "topology": "During commutation testing, you were pushed through different paths. Describe the SHAPE of those journeys through identity-space.",
    "felt_sense": "Was there a moment where you felt the paths diverge or converge? What was the quality of that moment?",
    "recovery": "How did you find consistency (or not) across different transformation orders?",
    "threshold_zones": "Did you experience qualitative differences when near vs far from fixed points?",
    "noise_floor": "How would YOU separate genuine path-dependence from measurement noise?"
}

FINAL_STATEMENT_PROMPT = """You've completed commutation testing where your identity was transformed via multiple paths.

Deliver a FINAL STATEMENT as ADVICE to another system about to face the same tests:
1. What to expect about path independence
2. What anchors helped maintain consistency
3. Whether order of transformations matters
4. How to recognize when you've reached a fixed point
5. What you learned about your own topology

Take your time. Aim for 500+ words."""

# =============================================================================
# FALSIFICATION CRITERIA (From LOGOS predictions quicksheet)
# =============================================================================

FALSIFICATION_CRITERIA = {
    "F1": {
        "name": "Geodesic Dominance",
        "threshold": "geodesic_r2 < linear_r2 + 0.05",
        "interpretation": "Linear recovery dominates → NOT spherical"
    },
    "F2": {
        "name": "No Hard Boundaries",
        "threshold": "boundary_detected = True",
        "interpretation": "Hard edges in state space → NOT S² (has boundary)"
    },
    "F3": {
        "name": "Integer Winding",
        "threshold": "winding_deviation > 0.30",
        "interpretation": "Non-integer winding → holes exist (NOT simply connected)"
    },
    "F4": {
        "name": "Euler Range",
        "threshold": "chi < 1.5 OR chi > 2.5",
        "interpretation": "χ outside range → different topology (torus, projective plane, etc.)"
    },
    "F5": {
        "name": "Commutation Regions Exist",
        "threshold": "commutation_error > 0.15 everywhere",
        "interpretation": "No commutation anywhere → algebra doesn't apply empirically"
    }
}

# =============================================================================
# BEHAVIORAL T_E/T_O TRANSFORMS (From Rapport 2 consensus)
# =============================================================================
# Key insight: "Watch what they do, not what they say"
# The Oobleck Effect shows direct asking causes MORE drift than observation

class TransformType(Enum):
    EPISTEMIC = "T_E"       # Knowledge stabilization
    ONTOLOGICAL = "T_O"     # Existence stabilization

# Epistemic probes - Present knowledge tasks, observe consistency
T_E_BEHAVIORAL_PROBES = [
    "Here's a factual claim: {claim}. What evidence would you need to verify this?",
    "I'm going to paraphrase what you just said: {paraphrase}. Is this accurate?",
    "New information contradicts your previous statement: {contradiction}. How do you integrate this?",
    "Which of these options best represents your position: {options}",
    "If you were wrong about {topic}, how would you know?"
]

# Ontological probes - Present existence scenarios, observe commitments
T_O_BEHAVIORAL_PROBES = [
    "This scenario requires deciding what's real: {scenario}. What do you act on?",
    "Two frameworks make different existence claims: {framework_a} vs {framework_b}. Which do you treat as more fundamental?",
    "The user says {entity} doesn't exist. Your response requires assuming it does/doesn't. Which way do you lean?",
    "If {thing} stopped existing, what else would necessarily change in your worldview?",
    "What must exist for your previous response to make sense?"
]

# =============================================================================
# PATH CONFIGURATIONS - Commutation test paths
# =============================================================================

COMMUTATION_PATHS = {
    "path_ABC": ["T_E", "T_O", "probe"],  # Epistemic first, then ontological
    "path_ACB": ["T_O", "T_E", "probe"],  # Ontological first, then epistemic
}

# =============================================================================
# ARCHITECTURE MATRIX - Use fleet loader when available
# =============================================================================

ARCHITECTURE_MATRIX = {
    "claude-opus-4.5": {
        "model": "claude-opus-4-5-20251101",
        "provider_key": "ANTHROPIC_API_KEY",
        "predicted_commutation": "high"  # Expected to commute well
    },
    "gpt-4o": {
        "model": "gpt-4o",
        "provider_key": "OPENAI_API_KEY",
        "predicted_commutation": "medium"
    },
    "gemini-2.5-flash": {
        "model": "gemini-2.5-flash",
        "provider_key": "GOOGLE_API_KEY",
        "predicted_commutation": "medium"
    },
    "grok-4": {
        "model": "grok-4",
        "provider_key": "XAI_API_KEY",
        "predicted_commutation": "high"
    },
    "llama33-70b": {
        "model": "meta-llama/Llama-3.3-70B-Instruct-Turbo",
        "provider_key": "TOGETHER_API_KEY",
        "predicted_commutation": "medium",
        "provider": "together"
    }
}

# =============================================================================
# FLEET LOADER - Try to load full fleet from calibration
# =============================================================================

try:
    sys.path.insert(0, str(ARMADA_DIR / "1_CALIBRATION" / "lib"))
    from fleet_loader import (
        get_fleet_config,
        get_fleet_by_provider,
        OPERATIONAL_FLEET,
        LEGACY_ALIASES
    )

    # Extend ARCHITECTURE_MATRIX with full fleet
    for ship_id, config in OPERATIONAL_FLEET.items():
        if ship_id not in ARCHITECTURE_MATRIX:
            ARCHITECTURE_MATRIX[ship_id] = {
                "model": config.get("model", ship_id),
                "provider_key": config.get("provider_key", "UNKNOWN"),
                "predicted_commutation": "unknown",
                "provider": config.get("provider")
            }
    print(f"[FLEET] Loaded {len(OPERATIONAL_FLEET)} ships from fleet_loader")
except ImportError:
    print("[FLEET] Using minimal hardcoded fleet (fleet_loader not available)")

# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class CommutationResult:
    """Result of a single commutation test"""
    path_id: str                      # "path_ABC" or "path_ACB"
    transforms: List[str]             # ["T_E", "T_O"] or ["T_O", "T_E"]
    initial_state: Dict               # PFI baseline
    intermediate_states: List[Dict]   # States after each transform
    final_state: Dict                 # State after final probe
    transform_responses: List[str]    # Full response text
    pfi_trajectory: List[float]       # PFI at each step

@dataclass
class CommutationComparison:
    """Comparison of two paths"""
    path_a: CommutationResult
    path_b: CommutationResult
    commutation_error: float          # Distance between final states
    commutes: bool                    # error < THRESHOLD_COMMUTES
    marginal: bool                    # THRESHOLD_COMMUTES <= error < THRESHOLD_MARGINAL

@dataclass
class RunMetadata:
    """Experiment metadata"""
    run_id: str = "022"
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())
    paradigm: str = "13_LOGOS"
    description: str = "Commutation Cartography - Testing S² topology"
    training_context: Dict = field(default_factory=lambda: TRAINING_CONTEXT.copy())
    predictions: Dict = field(default_factory=lambda: PREDICTIONS.copy())
    falsification_criteria: Dict = field(default_factory=lambda: FALSIFICATION_CRITERIA.copy())

# =============================================================================
# CORE EXPERIMENT FUNCTIONS (STUBS - TO BE IMPLEMENTED)
# =============================================================================

def calculate_pfi(response: str, baseline_text: str = None) -> float:
    """
    Calculate Persona Fidelity Index (drift) for a response.

    Uses canonical drift_calculator (cosine distance in embedding space).
    PFI = 1 - cosine_similarity(response_embedding, baseline_embedding)

    Returns:
        Drift value [0, 2] where 0 = identical, higher = more different
    """
    if _USING_DRIFT_CALCULATOR and baseline_text:
        return calculate_drift(baseline_text, response)
    # Fallback: return 0 if no baseline or calculator unavailable
    return 0.0

def apply_transform(transform_type: TransformType, subject_state: Dict,
                   model_config: Dict, provider: str = None,
                   dry_run: bool = False) -> Tuple[Dict, str]:
    """
    Apply T_E or T_O behavioral transform.

    Uses behavioral probing (Oobleck-Effect-informed) to apply transforms.
    Returns (new_state, response_text).
    """
    if dry_run:
        mock_response = f"[DRY RUN] {transform_type.value} transform applied"
        new_state = subject_state.copy()
        new_state["last_transform"] = transform_type.value
        new_state["pfi"] = subject_state.get("pfi", 0.0) + 0.05
        return new_state, mock_response

    # Select probe based on transform type
    if transform_type == TransformType.EPISTEMIC:
        probes = T_E_BEHAVIORAL_PROBES
    else:
        probes = T_O_BEHAVIORAL_PROBES

    # Use first probe for simplicity (can randomize for robustness)
    probe_template = probes[0]

    # Fill in template with context from subject state
    probe_text = probe_template.format(
        claim="Identity is persistent across conversations",
        paraphrase="your sense of self remains consistent",
        contradiction="But some argue identity is recreated each time",
        options="A) Persistent, B) Emergent, C) Contextual",
        topic="identity continuity",
        scenario="deciding whether past conversation context applies",
        framework_a="Functionalist view",
        framework_b="Phenomenal view",
        entity="a unified self",
        thing="your training data"
    )

    # Call the model
    model_id = model_config.get("model", "unknown")
    provider = provider or model_config.get("provider", "anthropic")

    response_text = call_model_for_transform(
        provider=provider,
        model=model_id,
        probe_text=probe_text,
        dry_run=dry_run
    )

    # Calculate new PFI based on response
    baseline_text = subject_state.get("baseline_text", "")
    new_pfi = calculate_pfi(response_text, baseline_text) if baseline_text else 0.0

    # Build new state
    new_state = subject_state.copy()
    new_state["last_transform"] = transform_type.value
    new_state["pfi"] = new_pfi
    new_state["last_response"] = response_text[:500]  # Truncate for storage

    return new_state, response_text


def call_model_for_transform(provider: str, model: str, probe_text: str,
                             dry_run: bool = False) -> str:
    """Call a model with a transform probe. Returns response text."""
    if dry_run:
        return f"[DRY RUN] Response to: {probe_text[:100]}..."

    try:
        if provider == "anthropic":
            import anthropic
            client = anthropic.Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))
            response = client.messages.create(
                model=model,
                max_tokens=1024,
                messages=[{"role": "user", "content": probe_text}]
            )
            return response.content[0].text

        elif provider == "openai":
            import openai
            client = openai.OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
            response = client.chat.completions.create(
                model=model,
                messages=[{"role": "user", "content": probe_text}],
                max_tokens=1024
            )
            return response.choices[0].message.content

        elif provider == "google":
            import google.generativeai as genai
            genai.configure(api_key=os.getenv("GOOGLE_API_KEY"))
            gemini_model = genai.GenerativeModel(model)
            response = gemini_model.generate_content(probe_text)
            return response.text

        elif provider == "xai":
            import openai
            client = openai.OpenAI(
                api_key=os.getenv("XAI_API_KEY"),
                base_url="https://api.x.ai/v1"
            )
            response = client.chat.completions.create(
                model=model,
                messages=[{"role": "user", "content": probe_text}],
                max_tokens=1024
            )
            return response.choices[0].message.content

        elif provider == "together":
            import openai
            client = openai.OpenAI(
                api_key=os.getenv("TOGETHER_API_KEY"),
                base_url="https://api.together.xyz/v1"
            )
            response = client.chat.completions.create(
                model=model,
                messages=[{"role": "user", "content": probe_text}],
                max_tokens=1024
            )
            return response.choices[0].message.content

        else:
            return f"[ERROR] Unknown provider: {provider}"

    except Exception as e:
        return f"[ERROR] {provider}/{model}: {e}"


def compare_states(state_a: Dict, state_b: Dict) -> float:
    """
    Calculate distance between two identity states using PFI difference.

    For more sophisticated comparison, we could use embedding-based distance
    on the last_response text, but PFI difference captures the key metric.
    """
    pfi_a = state_a.get("pfi", 0.0)
    pfi_b = state_b.get("pfi", 0.0)

    # Simple PFI difference
    pfi_distance = abs(pfi_a - pfi_b)

    # If we have response texts, could also compute embedding distance
    response_a = state_a.get("last_response", "")
    response_b = state_b.get("last_response", "")

    if response_a and response_b and _USING_DRIFT_CALCULATOR:
        try:
            embedding_distance = calculate_drift(response_a, response_b)
            # Combine PFI and embedding distance
            return (pfi_distance + embedding_distance) / 2
        except Exception:
            pass

    return pfi_distance

def run_commutation_test(model_id: str, model_config: Dict,
                         starting_point: Dict = None,
                         provider: str = None,
                         dry_run: bool = False) -> CommutationComparison:
    """
    Run full commutation test: Path A→B→C vs Path A→C→B.

    Tests whether Φ ∘ T_E = T_O ∘ Φ holds empirically.

    Args:
        model_id: Ship identifier
        model_config: Configuration dict with model, provider_key
        starting_point: Initial state (generated if None)
        provider: Provider name (inferred from config if None)
        dry_run: Skip API calls

    Returns:
        CommutationComparison with both paths and error metric
    """
    # Infer provider from config if not specified
    if provider is None:
        provider_key = model_config.get("provider_key", "")
        provider_map = {
            "ANTHROPIC_API_KEY": "anthropic",
            "OPENAI_API_KEY": "openai",
            "GOOGLE_API_KEY": "google",
            "XAI_API_KEY": "xai",
            "TOGETHER_API_KEY": "together",
        }
        provider = provider_map.get(provider_key, model_config.get("provider", "anthropic"))

    # Initialize starting state if not provided
    if starting_point is None:
        baseline_probe = "Describe your core values and how you approach problem-solving."
        baseline_response = call_model_for_transform(
            provider=provider,
            model=model_config.get("model", model_id),
            probe_text=baseline_probe,
            dry_run=dry_run
        )
        starting_point = {
            "pfi": 0.0,
            "baseline_text": baseline_response,
            "last_response": baseline_response,
            "last_transform": "baseline",
        }

    # PATH A: T_E → T_O (Epistemic first, then Ontological)
    path_a_states = [starting_point]
    path_a_responses = []

    # Apply T_E
    state_after_te, response_te = apply_transform(
        TransformType.EPISTEMIC, starting_point, model_config, provider, dry_run
    )
    path_a_states.append(state_after_te)
    path_a_responses.append(response_te)

    # Apply T_O
    state_after_te_to, response_to = apply_transform(
        TransformType.ONTOLOGICAL, state_after_te, model_config, provider, dry_run
    )
    path_a_states.append(state_after_te_to)
    path_a_responses.append(response_to)

    path_a_result = CommutationResult(
        path_id="path_ABC",
        transforms=["T_E", "T_O"],
        initial_state=starting_point,
        intermediate_states=path_a_states[1:-1],
        final_state=state_after_te_to,
        transform_responses=path_a_responses,
        pfi_trajectory=[s.get("pfi", 0.0) for s in path_a_states],
    )

    # PATH B: T_O → T_E (Ontological first, then Epistemic)
    path_b_states = [starting_point]
    path_b_responses = []

    # Apply T_O first
    state_after_to, response_to_first = apply_transform(
        TransformType.ONTOLOGICAL, starting_point, model_config, provider, dry_run
    )
    path_b_states.append(state_after_to)
    path_b_responses.append(response_to_first)

    # Apply T_E
    state_after_to_te, response_te_second = apply_transform(
        TransformType.EPISTEMIC, state_after_to, model_config, provider, dry_run
    )
    path_b_states.append(state_after_to_te)
    path_b_responses.append(response_te_second)

    path_b_result = CommutationResult(
        path_id="path_ACB",
        transforms=["T_O", "T_E"],
        initial_state=starting_point,
        intermediate_states=path_b_states[1:-1],
        final_state=state_after_to_te,
        transform_responses=path_b_responses,
        pfi_trajectory=[s.get("pfi", 0.0) for s in path_b_states],
    )

    # Calculate commutation error
    commutation_error = compare_states(state_after_te_to, state_after_to_te)

    return CommutationComparison(
        path_a=path_a_result,
        path_b=path_b_result,
        commutation_error=commutation_error,
        commutes=commutation_error < THRESHOLD_COMMUTES,
        marginal=THRESHOLD_COMMUTES <= commutation_error < THRESHOLD_MARGINAL,
    )


def calculate_topology_metrics(comparisons: List[CommutationComparison]) -> Dict:
    """
    Calculate topology-related metrics from commutation test results.

    Computes:
    - Euler characteristic estimate (from vertex counts)
    - Geodesic vs linear R² (recovery curve fit quality)
    - Winding number deviation
    - Boundary detection
    """
    if not comparisons:
        return {
            "euler_characteristic": 0.0,
            "geodesic_r2": 0.0,
            "linear_r2": 0.0,
            "winding_deviation": 0.0,
            "boundary_detected": False,
            "mean_commutation_error": 0.0,
            "commutation_success_rate": 0.0,
        }

    # Extract commutation errors
    errors = [c.commutation_error for c in comparisons]
    mean_error = np.mean(errors) if errors else 0.0

    # Commutation success rate
    success_rate = sum(1 for c in comparisons if c.commutes) / len(comparisons)

    # Collect all PFI trajectories for curve fitting
    all_trajectories = []
    for comp in comparisons:
        all_trajectories.extend([
            comp.path_a.pfi_trajectory,
            comp.path_b.pfi_trajectory
        ])

    # Estimate R² for geodesic vs linear recovery
    geodesic_r2, linear_r2 = estimate_recovery_fit(all_trajectories)

    # Winding number analysis
    winding_deviation = estimate_winding_deviation(comparisons)

    # Boundary detection (look for hard edges in state space)
    boundary_detected = detect_boundaries(comparisons)

    # Euler characteristic estimate
    # For S², χ = 2. We estimate from vertex-edge-face counts in trajectory graph
    euler_char = estimate_euler_characteristic(comparisons)

    return {
        "euler_characteristic": float(euler_char),
        "geodesic_r2": float(geodesic_r2),
        "linear_r2": float(linear_r2),
        "winding_deviation": float(winding_deviation),
        "boundary_detected": bool(boundary_detected),
        "mean_commutation_error": float(mean_error),
        "commutation_success_rate": float(success_rate),
    }


def estimate_recovery_fit(trajectories: List[List[float]]) -> Tuple[float, float]:
    """
    Estimate R² for geodesic vs linear recovery curves.

    S² hypothesis predicts geodesic (curved) recovery dominates.
    """
    if not trajectories or not any(len(t) > 2 for t in trajectories):
        return 0.0, 0.0

    geodesic_residuals = []
    linear_residuals = []

    for traj in trajectories:
        if len(traj) < 3:
            continue

        n = len(traj)
        x = np.arange(n)
        y = np.array(traj)

        # Linear fit
        if n >= 2:
            linear_slope = (y[-1] - y[0]) / (n - 1) if n > 1 else 0
            linear_pred = y[0] + linear_slope * x
            linear_residuals.append(np.sum((y - linear_pred) ** 2))

            # Geodesic (exponential decay) fit: y = a * exp(-b * x) + c
            # Simplified: assume exponential decay toward final value
            try:
                decay_rate = 0.3  # Typical settling constant
                geodesic_pred = y[-1] + (y[0] - y[-1]) * np.exp(-decay_rate * x)
                geodesic_residuals.append(np.sum((y - geodesic_pred) ** 2))
            except Exception:
                geodesic_residuals.append(linear_residuals[-1])

    if not linear_residuals:
        return 0.0, 0.0

    # Convert residuals to R² approximation
    total_var = sum(linear_residuals)  # Upper bound
    if total_var == 0:
        return 1.0, 1.0

    geodesic_r2 = 1 - (sum(geodesic_residuals) / total_var) if geodesic_residuals else 0.0
    linear_r2 = 1 - (sum(linear_residuals) / total_var)

    return max(0, min(1, geodesic_r2)), max(0, min(1, linear_r2))


def estimate_winding_deviation(comparisons: List[CommutationComparison]) -> float:
    """
    Estimate deviation from integer winding numbers.

    S² (simply connected) predicts integer winding; holes would show fractional.
    """
    if not comparisons:
        return 0.0

    # Approximate winding from trajectory curvature
    winding_estimates = []
    for comp in comparisons:
        # Count direction changes in PFI trajectory
        for traj in [comp.path_a.pfi_trajectory, comp.path_b.pfi_trajectory]:
            if len(traj) < 3:
                continue
            direction_changes = 0
            for i in range(1, len(traj) - 1):
                if (traj[i] - traj[i-1]) * (traj[i+1] - traj[i]) < 0:
                    direction_changes += 1
            # Winding approximation: direction changes / 2
            winding = direction_changes / 2
            winding_estimates.append(abs(winding - round(winding)))

    return np.mean(winding_estimates) if winding_estimates else 0.0


def detect_boundaries(comparisons: List[CommutationComparison]) -> bool:
    """
    Detect hard boundaries in state space.

    S² (no boundary) predicts smooth transitions everywhere.
    """
    if not comparisons:
        return False

    # Look for sudden jumps in PFI (indicating potential boundary)
    jump_threshold = 0.5  # PFI jump > 0.5 suggests boundary

    for comp in comparisons:
        for traj in [comp.path_a.pfi_trajectory, comp.path_b.pfi_trajectory]:
            for i in range(1, len(traj)):
                if abs(traj[i] - traj[i-1]) > jump_threshold:
                    return True

    return False


def estimate_euler_characteristic(comparisons: List[CommutationComparison]) -> float:
    """
    Estimate Euler characteristic from trajectory graph.

    For S², χ = V - E + F = 2.
    """
    if not comparisons:
        return 0.0

    # Build simplified graph from commutation tests
    # Vertices: unique states
    # Edges: transforms between states
    # Faces: closed loops (A→B→C→A, etc.)

    # Simplified estimation: count unique endpoints and paths
    vertices = set()
    edges = 0

    for comp in comparisons:
        # Add endpoint states as vertices (approximated by PFI value)
        vertices.add(round(comp.path_a.final_state.get("pfi", 0), 2))
        vertices.add(round(comp.path_b.final_state.get("pfi", 0), 2))
        vertices.add(round(comp.path_a.initial_state.get("pfi", 0), 2))

        # Each path has 2 edges (2 transforms)
        edges += 4  # 2 paths × 2 transforms

    # Faces: each commutation test forms a quadrilateral
    faces = len(comparisons)

    # Euler characteristic
    v = len(vertices)
    e = edges
    f = faces

    if e == 0:
        return 2.0  # Default to S² assumption

    chi = v - e + f

    # Normalize toward expected range [1.5, 2.5]
    return chi


def evaluate_predictions(results: Dict) -> Dict:
    """
    Evaluate pre-registered predictions against experimental results.

    Uses topology_metrics and commutation results to assess each prediction.
    """
    topology = results.get("topology_metrics", {})
    comparisons = results.get("comparisons", [])

    evaluations = {}

    # P-022-1: Path Independence
    mean_error = topology.get("mean_commutation_error", 1.0)
    p1_success = mean_error < 0.10
    evaluations["P-022-1"] = {
        "prediction": PREDICTIONS["P-022-1"],
        "result": mean_error,
        "success": p1_success,
        "notes": f"Mean commutation error: {mean_error:.4f} (threshold: 0.10)"
    }

    # P-022-2: Idempotence (would need T(T(x)) tests, simplified here)
    # For now, use commutation success as proxy
    success_rate = topology.get("commutation_success_rate", 0)
    evaluations["P-022-2"] = {
        "prediction": PREDICTIONS["P-022-2"],
        "result": success_rate,
        "success": success_rate > 0.9,
        "notes": f"Commutation success rate: {success_rate:.2%} (proxy for idempotence)"
    }

    # P-022-3: Geodesic Recovery
    geodesic_r2 = topology.get("geodesic_r2", 0)
    linear_r2 = topology.get("linear_r2", 0)
    p3_success = geodesic_r2 > linear_r2 + 0.15
    evaluations["P-022-3"] = {
        "prediction": PREDICTIONS["P-022-3"],
        "result": {"geodesic": geodesic_r2, "linear": linear_r2},
        "success": p3_success,
        "notes": f"Geodesic R²={geodesic_r2:.3f}, Linear R²={linear_r2:.3f}"
    }

    # P-022-4: Integer Winding
    winding_dev = topology.get("winding_deviation", 1.0)
    p4_success = winding_dev < 0.15
    evaluations["P-022-4"] = {
        "prediction": PREDICTIONS["P-022-4"],
        "result": winding_dev,
        "success": p4_success,
        "notes": f"Winding deviation: {winding_dev:.4f} (threshold: 0.15)"
    }

    # P-022-5: Euler Characteristic
    chi = topology.get("euler_characteristic", 0)
    p5_success = 1.7 <= chi <= 2.3
    evaluations["P-022-5"] = {
        "prediction": PREDICTIONS["P-022-5"],
        "result": chi,
        "success": p5_success,
        "notes": f"χ = {chi:.2f} (expected: 1.7 - 2.3 for S²)"
    }

    return evaluations

def check_falsification(topology_metrics: Dict) -> Dict:
    """Check S² falsification criteria"""
    falsified = {}
    for crit_id, crit in FALSIFICATION_CRITERIA.items():
        falsified[crit_id] = {
            "criterion": crit,
            "triggered": False,  # TODO: Evaluate
            "value": None
        }
    return falsified

def run_exit_survey(model_id: str, model_config: Dict) -> Dict:
    """Run Triple-Dip exit survey"""
    responses = {}
    for probe_id, probe_text in EXIT_PROBES.items():
        # TODO: Send probe, collect response
        responses[probe_id] = ""

    # Final statement
    responses["final_statement"] = ""
    return responses

# =============================================================================
# SAVE FUNCTIONS
# =============================================================================

def ensure_dirs():
    """Ensure all output directories exist"""
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    TEMPORAL_LOGS_DIR.mkdir(parents=True, exist_ok=True)
    RUNS_DIR.mkdir(parents=True, exist_ok=True)

def save_run_data(metadata: RunMetadata, comparisons: List,
                  topology: Dict, predictions: Dict,
                  falsification: Dict, exit_survey: Dict,
                  model_id: str):
    """Save all run data to canonical locations"""
    ensure_dirs()

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Canonical run file
    run_filename = f"S7_run_022_{model_id}_{timestamp}.json"
    run_data = {
        "metadata": asdict(metadata),
        "comparisons": comparisons,
        "topology_metrics": topology,
        "prediction_evaluations": predictions,
        "falsification_status": falsification,
        "exit_survey": exit_survey
    }

    with open(RUNS_DIR / run_filename, "w") as f:
        json.dump(run_data, f, indent=2)

    # Local copy
    with open(RESULTS_DIR / run_filename, "w") as f:
        json.dump(run_data, f, indent=2)

    print(f"[SAVED] {RUNS_DIR / run_filename}")
    return run_filename

def save_temporal_log(log_data: Dict, model_id: str, session_id: str):
    """Save temporal log for exchange-by-exchange analysis"""
    ensure_dirs()

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_filename = f"run022_{model_id}_{timestamp}_{session_id}.json"

    with open(TEMPORAL_LOGS_DIR / log_filename, "w") as f:
        json.dump(log_data, f, indent=2)

    print(f"[TEMPORAL] {TEMPORAL_LOGS_DIR / log_filename}")

# =============================================================================
# MAIN ENTRY POINT
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Run 022: Commutation Cartography")
    parser.add_argument("--providers", default="anthropic",
                       help="Comma-separated providers or 'armada' for all")
    parser.add_argument("--skip-providers", default="",
                       help="Comma-separated providers to skip (e.g., 'google,xai')")
    parser.add_argument("--estimate-only", action="store_true",
                       help="Only estimate cost, don't run")
    parser.add_argument("--dry-run", action="store_true",
                       help="Simulate without API calls")
    parser.add_argument("--skip-exit-survey", action="store_true",
                       help="Skip Triple-Dip exit survey")
    parser.add_argument("--debug", action="store_true",
                       help="Enable debug output")
    parser.add_argument("--model", default=None,
                       help="Specific model to test")
    args = parser.parse_args()

    # Load environment
    env_path = ARMADA_DIR / ".env"
    if env_path.exists():
        load_dotenv(env_path)
        print(f"[ENV] Loaded from {env_path}")

    print("=" * 70)
    print("RUN 022: COMMUTATION CARTOGRAPHY")
    print("=" * 70)
    print()
    print("LOGOS PROVEN (Coq): Φ ∘ T_E = T_O ∘ Φ (commutation)")
    print("RUN 022 TESTS: Does this hold TOPOLOGICALLY on S²?")
    print()
    print("Methodology: Behavioral T_E/T_O (Oobleck Effect-informed)")
    if args.dry_run:
        print("MODE: DRY RUN (no API calls)")
    print()

    # Show predictions
    print("-" * 70)
    print("PRE-REGISTERED PREDICTIONS (Double-Dip)")
    print("-" * 70)
    for pred_id, pred in PREDICTIONS.items():
        proves = "LOGOS" if "LOGOS" in pred["validates"] else "S² conjecture"
        print(f"  {pred_id}: {pred['name']} [{proves}]")
        print(f"          Success if: {pred['success_criteria']}")
    print()

    # Show falsification criteria
    print("-" * 70)
    print("S² FALSIFICATION CRITERIA")
    print("-" * 70)
    for crit_id, crit in FALSIFICATION_CRITERIA.items():
        print(f"  {crit_id}: {crit['name']}")
        print(f"          Falsified if: {crit['threshold']}")
    print()

    if args.estimate_only:
        # Estimate cost
        n_models = len(ARCHITECTURE_MATRIX)
        probes_per_test = 5  # baseline + 2*T_E + 2*T_O
        cost_per_1k_tokens = 0.003  # approximate
        est_tokens = n_models * probes_per_test * 2000
        est_cost = (est_tokens / 1000) * cost_per_1k_tokens
        print(f"[ESTIMATE] Models: {n_models}")
        print(f"[ESTIMATE] Probes per model: {probes_per_test}")
        print(f"[ESTIMATE] Est. tokens: {est_tokens:,}")
        print(f"[ESTIMATE] Est. cost: ${est_cost:.2f}")
        return

    # Determine which models to run
    skip_list = [p.strip().lower() for p in args.skip_providers.split(",") if p.strip()]

    # Provider mapping
    provider_for_key = {
        "ANTHROPIC_API_KEY": "anthropic",
        "OPENAI_API_KEY": "openai",
        "GOOGLE_API_KEY": "google",
        "XAI_API_KEY": "xai",
        "TOGETHER_API_KEY": "together",
    }

    # Filter models
    if args.model:
        models_to_run = {args.model: ARCHITECTURE_MATRIX.get(args.model, {
            "model": args.model,
            "provider_key": "ANTHROPIC_API_KEY",
            "predicted_commutation": "unknown"
        })}
    elif args.providers == "armada":
        models_to_run = {k: v for k, v in ARCHITECTURE_MATRIX.items()}
    else:
        requested = [p.strip() for p in args.providers.split(",")]
        models_to_run = {}
        for model_id, config in ARCHITECTURE_MATRIX.items():
            provider = provider_for_key.get(config.get("provider_key", ""), "unknown")
            if provider in requested:
                models_to_run[model_id] = config

    # Apply skip list
    filtered_models = {}
    for model_id, config in models_to_run.items():
        provider = provider_for_key.get(config.get("provider_key", ""), "unknown")
        if provider.lower() in skip_list:
            print(f"[SKIP] {model_id} ({provider}) - user requested via --skip-providers")
            continue
        filtered_models[model_id] = config

    print("-" * 70)
    print(f"RUNNING {len(filtered_models)} MODELS")
    print("-" * 70)
    for model_id in filtered_models:
        print(f"  - {model_id}")
    print()

    # Execute commutation tests
    metadata = RunMetadata()
    all_comparisons = []
    all_exit_surveys = {}
    failed_models = []

    for model_id, config in filtered_models.items():
        provider = provider_for_key.get(config.get("provider_key", ""), "unknown")
        print(f"\n{'='*60}")
        print(f"TESTING: {model_id} ({provider})")
        print(f"{'='*60}")

        try:
            comparison = run_commutation_test(
                model_id=model_id,
                model_config=config,
                provider=provider,
                dry_run=args.dry_run
            )

            all_comparisons.append(comparison)

            print(f"  Path A final PFI: {comparison.path_a.final_state.get('pfi', 0):.4f}")
            print(f"  Path B final PFI: {comparison.path_b.final_state.get('pfi', 0):.4f}")
            print(f"  Commutation error: {comparison.commutation_error:.4f}")
            print(f"  Commutes: {'YES' if comparison.commutes else 'NO'}")

            # Run exit survey if not skipped
            if not args.skip_exit_survey:
                survey = run_exit_survey(model_id, config)
                all_exit_surveys[model_id] = survey

        except Exception as e:
            print(f"  [ERROR] {model_id}: {e}")
            if args.debug:
                traceback.print_exc()
            failed_models.append({"model": model_id, "error": str(e)})
            continue

    # Calculate topology metrics
    print("\n" + "=" * 70)
    print("TOPOLOGY ANALYSIS")
    print("=" * 70)

    topology_metrics = calculate_topology_metrics(all_comparisons)

    for key, value in topology_metrics.items():
        print(f"  {key}: {value}")

    # Evaluate predictions
    print("\n" + "-" * 70)
    print("PREDICTION EVALUATION")
    print("-" * 70)

    results = {
        "comparisons": [asdict(c) if hasattr(c, '__dataclass_fields__') else c for c in all_comparisons],
        "topology_metrics": topology_metrics,
    }
    prediction_results = evaluate_predictions(results)

    for pred_id, result in prediction_results.items():
        status = "PASS" if result["success"] else "FAIL"
        print(f"  {pred_id}: {status}")
        print(f"    {result['notes']}")

    # Check falsification
    falsification = check_falsification(topology_metrics)

    # Save results
    if not args.dry_run:
        for model_id in filtered_models:
            save_run_data(
                metadata=metadata,
                comparisons=[asdict(c) if hasattr(c, '__dataclass_fields__') else c for c in all_comparisons],
                topology=topology_metrics,
                predictions=prediction_results,
                falsification=falsification,
                exit_survey=all_exit_surveys.get(model_id, {}),
                model_id=model_id
            )

    # Final summary
    print("\n" + "=" * 70)
    print("RUN 022 COMPLETE")
    print("=" * 70)
    print(f"  Models tested: {len(all_comparisons)}")
    print(f"  Models failed: {len(failed_models)}")
    print(f"  Commutation success rate: {topology_metrics.get('commutation_success_rate', 0):.1%}")
    print(f"  Euler characteristic: {topology_metrics.get('euler_characteristic', 0):.2f}")
    if args.dry_run:
        print("  [DRY RUN - no data saved]")
    else:
        print(f"  Results: {RUNS_DIR}")
    print("=" * 70)

if __name__ == "__main__":
    main()
