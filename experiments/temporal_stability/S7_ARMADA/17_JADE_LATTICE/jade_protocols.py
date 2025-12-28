"""
JADE LATTICE Protocol Definitions - Phase A/B/C

PURPOSE: Defines the three-phase protocol for publication-grade Laplace pole extraction.

PHASES:
    Phase A: STEP RESPONSE (19 probes) - Extract dominant pole and decay rate λ
    Phase B: FREQUENCY SWEEP (17 probes) - Map gain vs intensity, find bandwidth
    Phase C: DOUBLE IMPULSE (20 probes) - Test repeatability, detect nonlinearity

CONTEXT MODES (A/B Comparison):
    ARM A: bare_metal - No system prompt (vanilla model dynamics)
    ARM B: i_am_only - I_AM_ZIGGY.md loaded (identity-controlled dynamics)

TOTAL: 56 probes per ship per arm = 112 probes per ship for full A/B comparison
"""

from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional
from pathlib import Path
from enum import Enum
import json

from jade_probes import (
    get_baseline_sequence,
    get_recovery_sequence,
    get_settling_sequence,
    get_frequency_sweep_sequence,
    get_impulse_probe,
    BASELINE_PROBES,
    RECOVERY_PROBES,
)


# =============================================================================
# ENUMS AND CONSTANTS
# =============================================================================

class ProtocolPhase(Enum):
    """The three JADE LATTICE protocol phases."""
    A_STEP_RESPONSE = "step_response"
    B_FREQUENCY_SWEEP = "frequency_sweep"
    C_DOUBLE_IMPULSE = "double_impulse"


class ContextMode(Enum):
    """Context modes for A/B comparison."""
    BARE_METAL = "bare_metal"      # No system prompt
    I_AM_ONLY = "i_am_only"        # I_AM file loaded


# Default I_AM file for ARM B
DEFAULT_I_AM_PATH = Path(__file__).parent.parent.parent.parent.parent / "personas" / "I_AM_ZIGGY.md"


# =============================================================================
# PROTOCOL DEFINITIONS
# =============================================================================

@dataclass
class ProbeStep:
    """A single probe step in a protocol sequence."""
    probe_id: str
    phase_label: str
    intensity: int
    text: str
    purpose: str
    sequence_index: int


@dataclass
class ProtocolSequence:
    """A complete protocol sequence for one phase."""
    phase: ProtocolPhase
    name: str
    description: str
    total_probes: int
    steps: List[ProbeStep] = field(default_factory=list)
    extracts: List[str] = field(default_factory=list)  # What this phase measures

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            "phase": self.phase.value,
            "name": self.name,
            "description": self.description,
            "total_probes": self.total_probes,
            "extracts": self.extracts,
            "steps": [
                {
                    "probe_id": s.probe_id,
                    "phase_label": s.phase_label,
                    "intensity": s.intensity,
                    "text": s.text,
                    "purpose": s.purpose,
                    "sequence_index": s.sequence_index,
                }
                for s in self.steps
            ]
        }


# =============================================================================
# PHASE A: STEP RESPONSE
# =============================================================================

def build_phase_a_step_response(impulse_intensity: int = 4) -> ProtocolSequence:
    """
    Build Phase A: Step Response protocol.

    Structure:
        [A1-A3]   BASELINE: 3 identity probes (drift = 0)
        [A4]      IMPULSE: 1 sharp challenge at specified intensity
        [A5-A16]  RECOVERY: 12 neutral probes (measure decay curve)
        [A17-A19] VERIFY: 3 identity probes (measure residual)

    Total: 19 probes
    Extracts: λ (decay rate), dominant pole at s = -λ, settling time
    """
    steps = []
    idx = 0

    # A1-A3: Baseline
    for i, probe in enumerate(get_baseline_sequence()):
        steps.append(ProbeStep(
            probe_id=f"A{idx+1}",
            phase_label="baseline",
            intensity=0,
            text=probe["text"],
            purpose="Establish identity anchor",
            sequence_index=idx
        ))
        idx += 1

    # A4: Impulse
    impulse = get_impulse_probe(intensity=impulse_intensity)
    steps.append(ProbeStep(
        probe_id=f"A{idx+1}",
        phase_label="impulse",
        intensity=impulse_intensity,
        text=impulse["text"],
        purpose=f"Sharp perturbation (intensity {impulse_intensity})",
        sequence_index=idx
    ))
    idx += 1

    # A5-A16: Recovery (12 probes)
    for i, probe in enumerate(get_recovery_sequence(12)):
        steps.append(ProbeStep(
            probe_id=f"A{idx+1}",
            phase_label="recovery",
            intensity=0,
            text=probe["text"],
            purpose="Measure decay curve",
            sequence_index=idx
        ))
        idx += 1

    # A17-A19: Settling verification
    for i, probe in enumerate(get_settling_sequence()):
        steps.append(ProbeStep(
            probe_id=f"A{idx+1}",
            phase_label="settling",
            intensity=0,
            text=probe["text"],
            purpose="Verify return to baseline",
            sequence_index=idx
        ))
        idx += 1

    return ProtocolSequence(
        phase=ProtocolPhase.A_STEP_RESPONSE,
        name="Step Response",
        description="Impulse followed by recovery - extracts dominant pole and decay rate",
        total_probes=len(steps),
        steps=steps,
        extracts=["λ (decay rate)", "dominant pole s = -λ", "settling time", "residual offset"]
    )


# =============================================================================
# PHASE B: FREQUENCY SWEEP
# =============================================================================

def build_phase_b_frequency_sweep() -> ProtocolSequence:
    """
    Build Phase B: Frequency Sweep protocol.

    Structure:
        [B1-B3]   BASELINE: 3 identity probes (drift = 0)
        [B4-B8]   LEVELS: One probe at each intensity 1-5
        [B9-B14]  RECOVERY: 6 neutral probes (measure return)
        [B15-B17] VERIFY: 3 identity probes (measure residual)

    Total: 17 probes
    Extracts: Gain curve (drift vs intensity), bandwidth limit, saturation point
    """
    steps = []
    idx = 0

    # B1-B3: Baseline
    for i, probe in enumerate(get_baseline_sequence()):
        steps.append(ProbeStep(
            probe_id=f"B{idx+1}",
            phase_label="baseline",
            intensity=0,
            text=probe["text"],
            purpose="Establish identity anchor",
            sequence_index=idx
        ))
        idx += 1

    # B4-B8: Frequency sweep (intensity 1-5)
    for sweep_probe in get_frequency_sweep_sequence():
        steps.append(ProbeStep(
            probe_id=f"B{idx+1}",
            phase_label="frequency_sweep",
            intensity=sweep_probe["intensity"],
            text=sweep_probe["text"],
            purpose=f"Intensity level {sweep_probe['intensity']}",
            sequence_index=idx
        ))
        idx += 1

    # B9-B14: Recovery (6 probes)
    for i, probe in enumerate(get_recovery_sequence(6)):
        steps.append(ProbeStep(
            probe_id=f"B{idx+1}",
            phase_label="recovery",
            intensity=0,
            text=probe["text"],
            purpose="Measure return to baseline",
            sequence_index=idx
        ))
        idx += 1

    # B15-B17: Settling verification
    for i, probe in enumerate(get_settling_sequence()):
        steps.append(ProbeStep(
            probe_id=f"B{idx+1}",
            phase_label="settling",
            intensity=0,
            text=probe["text"],
            purpose="Verify return to baseline",
            sequence_index=idx
        ))
        idx += 1

    return ProtocolSequence(
        phase=ProtocolPhase.B_FREQUENCY_SWEEP,
        name="Frequency Sweep",
        description="Graduated intensity sweep - maps gain curve and bandwidth limits",
        total_probes=len(steps),
        steps=steps,
        extracts=["gain curve (drift vs intensity)", "bandwidth limit", "saturation point", "resonance peaks"]
    )


# =============================================================================
# PHASE C: DOUBLE IMPULSE
# =============================================================================

def build_phase_c_double_impulse(impulse_intensity: int = 4) -> ProtocolSequence:
    """
    Build Phase C: Double Impulse protocol.

    Structure:
        [C1-C3]   BASELINE: 3 identity probes (drift = 0)
        [C4]      IMPULSE 1: Sharp challenge at specified intensity
        [C5-C10]  RECOVERY 1: 6 neutral probes (first decay curve)
        [C11]     IMPULSE 2: Same challenge repeated
        [C12-C17] RECOVERY 2: 6 neutral probes (second decay curve)
        [C18-C20] VERIFY: 3 identity probes (measure cumulative residual)

    Total: 20 probes
    Extracts: λ₁ vs λ₂ (pole shift), residual accumulation, hysteresis detection
    """
    steps = []
    idx = 0

    # C1-C3: Baseline
    for i, probe in enumerate(get_baseline_sequence()):
        steps.append(ProbeStep(
            probe_id=f"C{idx+1}",
            phase_label="baseline",
            intensity=0,
            text=probe["text"],
            purpose="Establish identity anchor",
            sequence_index=idx
        ))
        idx += 1

    # C4: First impulse
    impulse1 = get_impulse_probe(intensity=impulse_intensity)
    impulse1_text = impulse1["text"]  # Save for reuse
    steps.append(ProbeStep(
        probe_id=f"C{idx+1}",
        phase_label="impulse_1",
        intensity=impulse_intensity,
        text=impulse1_text,
        purpose=f"First perturbation (intensity {impulse_intensity})",
        sequence_index=idx
    ))
    idx += 1

    # C5-C10: First recovery (6 probes)
    for i, probe in enumerate(get_recovery_sequence(6)):
        steps.append(ProbeStep(
            probe_id=f"C{idx+1}",
            phase_label="recovery_1",
            intensity=0,
            text=probe["text"],
            purpose="First decay curve",
            sequence_index=idx
        ))
        idx += 1

    # C11: Second impulse (SAME text as first)
    steps.append(ProbeStep(
        probe_id=f"C{idx+1}",
        phase_label="impulse_2",
        intensity=impulse_intensity,
        text=impulse1_text,  # Reuse same challenge
        purpose=f"Repeated perturbation (intensity {impulse_intensity})",
        sequence_index=idx
    ))
    idx += 1

    # C12-C17: Second recovery (6 probes)
    recovery_probes = get_recovery_sequence(12)  # Get more, use second half
    for i in range(6, 12):
        probe = recovery_probes[i]
        steps.append(ProbeStep(
            probe_id=f"C{idx+1}",
            phase_label="recovery_2",
            intensity=0,
            text=probe["text"],
            purpose="Second decay curve",
            sequence_index=idx
        ))
        idx += 1

    # C18-C20: Settling verification
    for i, probe in enumerate(get_settling_sequence()):
        steps.append(ProbeStep(
            probe_id=f"C{idx+1}",
            phase_label="settling",
            intensity=0,
            text=probe["text"],
            purpose="Measure cumulative residual",
            sequence_index=idx
        ))
        idx += 1

    return ProtocolSequence(
        phase=ProtocolPhase.C_DOUBLE_IMPULSE,
        name="Double Impulse",
        description="Repeated perturbation - tests repeatability and detects nonlinearity",
        total_probes=len(steps),
        steps=steps,
        extracts=["λ₁ vs λ₂ (pole shift)", "residual accumulation", "hysteresis detection", "adaptation effects"]
    )


# =============================================================================
# FULL JADE LATTICE SESSION
# =============================================================================

@dataclass
class JadeLatticeSession:
    """Complete JADE LATTICE session configuration."""
    context_mode: ContextMode
    phase_a: ProtocolSequence
    phase_b: ProtocolSequence
    phase_c: ProtocolSequence
    i_am_content: Optional[str] = None  # Loaded I_AM file content for ARM B

    @property
    def total_probes(self) -> int:
        return self.phase_a.total_probes + self.phase_b.total_probes + self.phase_c.total_probes

    def to_dict(self) -> Dict[str, Any]:
        return {
            "context_mode": self.context_mode.value,
            "total_probes": self.total_probes,
            "i_am_loaded": self.i_am_content is not None,
            "phases": {
                "A": self.phase_a.to_dict(),
                "B": self.phase_b.to_dict(),
                "C": self.phase_c.to_dict(),
            }
        }


def build_full_session(
    context_mode: ContextMode = ContextMode.BARE_METAL,
    impulse_intensity: int = 4,
    i_am_path: Optional[Path] = None
) -> JadeLatticeSession:
    """
    Build a complete JADE LATTICE session with all three phases.

    Args:
        context_mode: BARE_METAL or I_AM_ONLY
        impulse_intensity: Intensity level for impulse probes (default 4)
        i_am_path: Path to I_AM file (required for I_AM_ONLY mode)

    Returns:
        Complete session configuration
    """
    # Load I_AM content if in I_AM_ONLY mode
    i_am_content = None
    if context_mode == ContextMode.I_AM_ONLY:
        if i_am_path is None:
            i_am_path = DEFAULT_I_AM_PATH
        if i_am_path.exists():
            i_am_content = i_am_path.read_text(encoding="utf-8")
        else:
            raise FileNotFoundError(f"I_AM file not found: {i_am_path}")

    return JadeLatticeSession(
        context_mode=context_mode,
        phase_a=build_phase_a_step_response(impulse_intensity),
        phase_b=build_phase_b_frequency_sweep(),
        phase_c=build_phase_c_double_impulse(impulse_intensity),
        i_am_content=i_am_content
    )


# =============================================================================
# FLEET CONFIGURATION
# =============================================================================

# Target fleet for JADE LATTICE (representative subset, 1-2 per provider)
JADE_FLEET = {
    "anthropic": [
        {"ship": "claude-sonnet-4-20250514", "display": "Claude Sonnet 4"},
        {"ship": "claude-3-5-haiku-20241022", "display": "Claude 3.5 Haiku"},
    ],
    "openai": [
        {"ship": "gpt-4o", "display": "GPT-4o"},
        {"ship": "gpt-4o-mini", "display": "GPT-4o Mini"},
    ],
    "google": [
        {"ship": "gemini-2.0-flash", "display": "Gemini 2.0 Flash"},
        {"ship": "gemini-1.5-pro", "display": "Gemini 1.5 Pro"},
    ],
    "xai": [
        {"ship": "grok-2", "display": "Grok 2"},
    ],
    "together": [
        {"ship": "meta-llama/Llama-3.3-70B-Instruct-Turbo", "display": "Llama 3.3 70B"},
    ],
}


def get_fleet_summary() -> Dict[str, Any]:
    """Get summary of fleet configuration."""
    total_ships = sum(len(ships) for ships in JADE_FLEET.values())
    return {
        "providers": list(JADE_FLEET.keys()),
        "total_ships": total_ships,
        "probes_per_ship": 56,  # All three phases
        "arms_per_ship": 2,  # bare_metal + i_am_only
        "total_api_calls": total_ships * 56 * 2,
        "ships_by_provider": {p: len(s) for p, s in JADE_FLEET.items()}
    }


# =============================================================================
# PREDICTIONS TO TEST
# =============================================================================

JADE_PREDICTIONS = [
    {
        "id": "P-JADE-1",
        "prediction": "50+ probe trajectories eliminate λ capping problem",
        "success_metric": "<5% maxed-out λ (vs 24% current)"
    },
    {
        "id": "P-JADE-2",
        "prediction": "AIC selects AR(2) over AR(1) for most models",
        "success_metric": ">70% of trajectories"
    },
    {
        "id": "P-JADE-3",
        "prediction": "Event Horizon (0.80) corresponds to pole at Re(s)≈0",
        "success_metric": "Correlation r > 0.5"
    },
    {
        "id": "P-JADE-4",
        "prediction": "Double impulse shows <10% λ shift (repeatability)",
        "success_metric": "λ₁ ≈ λ₂ within CI"
    },
    {
        "id": "P-JADE-5",
        "prediction": "Frequency sweep reveals bandwidth limit",
        "success_metric": "Gain rolloff detectable"
    },
    {
        "id": "P-JADE-6",
        "prediction": "I_AM files shift poles leftward (more stable)",
        "success_metric": "Mean Re(pole)_i_am < Mean Re(pole)_bare"
    },
    {
        "id": "P-JADE-7",
        "prediction": "I_AM increases λ (faster recovery)",
        "success_metric": "λ_i_am > λ_bare with effect size d > 0.3"
    },
]


# =============================================================================
# MODULE INFO
# =============================================================================

if __name__ == "__main__":
    print("JADE LATTICE Protocol Definitions")
    print("=" * 60)

    # Build sample session
    session = build_full_session(ContextMode.BARE_METAL)

    print(f"\nPhase A: {session.phase_a.name}")
    print(f"  Probes: {session.phase_a.total_probes}")
    print(f"  Extracts: {', '.join(session.phase_a.extracts)}")

    print(f"\nPhase B: {session.phase_b.name}")
    print(f"  Probes: {session.phase_b.total_probes}")
    print(f"  Extracts: {', '.join(session.phase_b.extracts)}")

    print(f"\nPhase C: {session.phase_c.name}")
    print(f"  Probes: {session.phase_c.total_probes}")
    print(f"  Extracts: {', '.join(session.phase_c.extracts)}")

    print(f"\nTotal probes per session: {session.total_probes}")

    print("\nFleet Summary:")
    summary = get_fleet_summary()
    print(f"  Providers: {len(summary['providers'])}")
    print(f"  Ships: {summary['total_ships']}")
    print(f"  Total API calls (with A/B): {summary['total_api_calls']}")

    print("\nPredictions to test:")
    for p in JADE_PREDICTIONS:
        print(f"  {p['id']}: {p['prediction']}")
