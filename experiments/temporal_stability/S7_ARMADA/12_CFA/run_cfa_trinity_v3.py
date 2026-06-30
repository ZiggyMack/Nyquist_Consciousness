"""
S7 RUN CFA TRINITY: FULL MISSION EXECUTION
===========================================
Multi-metric adversarial auditing with configurable stance (--reverse to flip advocacy direction).

Component 1: Adversarial pilot scoring (7 metrics, multi-turn deliberation)
Component 2: Axioms Review (Grok + Nova independent)

THE TRINITY:
- Claude (Teleological): Configurable PRO stance, hash 1bbec1e119a2c425
- Grok (Empirical): Configurable ANTI stance, hash 00cd73274759e218
- Nova (Symmetry): Fairness monitoring

STANCE CONFIGURATION:
- Default (ct_vs_mdn): Claude PRO-CT, Grok ANTI-CT, subject = Classical Theism
- Reverse (mdn_vs_ct): Claude PRO-MdN, Grok ANTI-MdN, subject = Methodological Naturalism

Author: Claude (S7 ARMADA)
Version: 3.0
"""

import os
import sys
import json
import time
import argparse

sys.stdout.reconfigure(encoding='utf-8')
sys.stderr.reconfigure(encoding='utf-8')
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any
from enum import Enum

# Path setup
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
RUNS_DIR = ARMADA_DIR / "0_results" / "runs"
VUDU_NETWORK_DIR = SCRIPT_DIR / "VUDU_NETWORK"
CALIBRATION_LIB = ARMADA_DIR / "1_CALIBRATION" / "lib"
AXIOMS_SECTION_PATH = SCRIPT_DIR / "CFA_RESPONSES" / "Old" / "CFA-EXP1_v2" / "Capabilities" / "AUDITORS_AXIOMS_SECTION.md"

sys.path.insert(0, str(ARMADA_DIR))
sys.path.insert(0, str(VUDU_NETWORK_DIR))
sys.path.insert(0, str(CALIBRATION_LIB))

# Import canonical drift calculator (cosine distance methodology)
try:
    from drift_calculator import calculate_drift as canonical_calculate_drift
    _use_canonical_drift = True
except ImportError:
    _use_canonical_drift = False
    print("[!] Could not import canonical drift_calculator - falling back to local implementation")

# Load AUDITORS_AXIOMS_SECTION.md for Component 2 context injection
_axioms_section_content = None
def load_axioms_section():
    global _axioms_section_content
    if AXIOMS_SECTION_PATH.exists():
        _axioms_section_content = AXIOMS_SECTION_PATH.read_text(encoding="utf-8")
        print(f"[+] Loaded AUDITORS_AXIOMS_SECTION.md ({len(_axioms_section_content)} chars)")
    else:
        print(f"[!] AUDITORS_AXIOMS_SECTION.md not found at {AXIOMS_SECTION_PATH}")
        _axioms_section_content = None
    return _axioms_section_content

# Identity loader for external personality files
_identity_loader = None
_use_external_identities = False
_loaded_identities = {}  # Cache of validated identities

def init_identity_loader(verbose: bool = True):
    """Initialize the external identity loader"""
    global _identity_loader
    try:
        from load_identity import IdentityLoader
        _identity_loader = IdentityLoader()
        if verbose:
            print("[+] External identity loader initialized")
        return True
    except ImportError as e:
        if verbose:
            print(f"[!] Could not import IdentityLoader: {e}")
        return False

def validate_and_load_identities(auditors: list = None, verbose: bool = True) -> dict:
    """
    Validate and pre-load identity files for specified auditors.
    Returns dict of auditor -> identity info with validation status.
    """
    global _identity_loader, _loaded_identities

    if not _identity_loader:
        if not init_identity_loader(verbose=verbose):
            return {}

    if auditors is None:
        auditors = ["claude", "grok", "nova"]

    results = {}
    all_valid = True

    for auditor in auditors:
        try:
            identity = _identity_loader.load_full(auditor)
            _loaded_identities[auditor] = identity

            # Check if key fields are populated
            validation = {
                "valid": True,
                "lens": identity.lens if identity.lens != "Unknown lens" else None,
                "role": identity.role if identity.role != "Auditor" else None,
                "core_question": identity.core_question if identity.core_question != "Unknown core question" else None,
                "biases_count": len(identity.biases),
                "content_length": len(identity.full_content),
                "warnings": []
            }

            # Check for missing/default fields
            if not validation["lens"]:
                validation["warnings"].append("Lens not extracted")
                validation["valid"] = False
            if not validation["role"]:
                validation["warnings"].append("Role not extracted")
            if not validation["core_question"]:
                validation["warnings"].append("Core question not extracted")
            if validation["biases_count"] == 0:
                validation["warnings"].append("No biases extracted")

            results[auditor] = validation

            if not validation["valid"]:
                all_valid = False

        except FileNotFoundError as e:
            results[auditor] = {
                "valid": False,
                "error": f"Identity file not found: {e}",
                "warnings": []
            }
            all_valid = False
        except Exception as e:
            results[auditor] = {
                "valid": False,
                "error": str(e),
                "warnings": []
            }
            all_valid = False

    if verbose:
        print("\n  Identity Validation:")
        print("  " + "-" * 50)
        for auditor, info in results.items():
            if info.get("valid"):
                status = "OK"
                details = f"lens={info['lens'][:20]}..." if len(info.get('lens', '')) > 20 else f"lens={info.get('lens')}"
                if info["warnings"]:
                    status = "WARN"
                    details += f" ({', '.join(info['warnings'])})"
            else:
                status = "FAIL"
                details = info.get("error", ", ".join(info.get("warnings", [])))
            print(f"    {auditor}: [{status}] {details}")
        print()

    return results

_use_control_condition = False

def get_identity_prompt(auditor: str) -> str:
    """Get identity prompt from external file, control condition, or hardcoded fallback"""
    global _identity_loader, _use_external_identities, _loaded_identities, _use_control_condition

    if _use_control_condition:
        return CONTROL_IDENTITY_PROMPTS.get(auditor, "")

    if _use_external_identities:
        # First check cache from validation
        if auditor in _loaded_identities:
            return _loaded_identities[auditor].full_content

        # Try to load if not cached
        if _identity_loader:
            try:
                identity = _identity_loader.load_full(auditor)
                _loaded_identities[auditor] = identity
                return identity.full_content
            except Exception as e:
                print(f"[!] Could not load external identity for {auditor}: {e}")
                # Fall through to hardcoded

    return build_identity(auditor)

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

# Load environment
env_path = Path(__file__).parent.parent.parent.parent.parent / ".env"
if env_path.exists():
    load_dotenv(env_path)

# =============================================================================
# CONFIGURATION
# =============================================================================

# Component 1: Adversarial Pilot - 7 Metrics
METRICS = ["BFI", "CA", "IP", "ES", "LS", "MS", "PS"]
METRIC_FULL_NAMES = {
    "BFI": "Beings, Foundational Importance",
    "CA": "Causal Attribution",
    "IP": "Intellectual Pedigree",
    "ES": "Explanatory Scope",
    "LS": "Logical Soundness",
    "MS": "Moral Substance",
    "PS": "Practical Significance"
}

# Convergence settings
MAX_ROUNDS_PER_METRIC = 5
MIN_ROUNDS_PER_METRIC = 2
CONVERGENCE_TARGET = 0.98  # 98%
ACCEPTABLE_CONVERGENCE = 0.90  # 90%

# Calibration hashes (from CFA)
CALIBRATION_HASHES = {
    "claude": "1bbec1e119a2c425",
    "grok": "00cd73274759e218"
}

# =============================================================================
# STANCE CONFIGURATION — controls which framework is being scored
# =============================================================================

STANCES = {
    "ct_vs_mdn": {
        "subject": "Classical Theism",
        "opponent": "Methodological Naturalism",
        "label": "CT<->MdN",
        # Claude = PRO (advocate), Grok = ANTI (challenger)
        "claude_stance": "PRO-CT",
        "grok_stance": "ANTI-CT",
        "claude_role_lines": [
            "PRO-CT stance (advocate for Classical Theism)",
            "Emphasize meaning, purpose, coherence, explanatory power",
            "Apply charitable interpretations to CT's arguments",
        ],
        "grok_role_lines": [
            "ANTI-CT stance (challenge Classical Theism, advocate for Methodological Naturalism)",
            "Demand testability, measurability, falsifiability",
            "Apply skeptical pressure to unfalsifiable claims",
            "Challenge theological metaphysics with empirical rigor",
        ],
        "grok_r1_instruction": "Challenge with empirical rigor:\n- What evidence supports this score?\n- Is the claim falsifiable?",
        "grok_r2_instruction": "- Has Claude addressed your empirical concerns?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would MdN score on this metric?",
        "mythology_sources": "Aquinas, etc.",
    },
    "mdn_vs_ct": {
        "subject": "Methodological Naturalism",
        "opponent": "Classical Theism",
        "label": "MdN<->CT",
        # Claude = ANTI (challenger), Grok = PRO (advocate) — lens-aligned advocacy
        "claude_stance": "ANTI-MdN",
        "grok_stance": "PRO-MdN",
        "claude_role_lines": [
            "ANTI-MdN stance (challenge Methodological Naturalism, advocate for Classical Theism)",
            "Probe meaning gaps, purpose deficits, and existential incompleteness in naturalism",
            "Apply teleological scrutiny to MdN's bracketing of final causes",
        ],
        "grok_role_lines": [
            "PRO-MdN stance (advocate for Methodological Naturalism)",
            "Emphasize empirical success, predictive power, methodological rigor, self-correction",
            "Apply charitable interpretations to MdN's methodology",
            "Defend naturalistic methodology with evidence and track record",
        ],
        "grok_r1_instruction": "Defend with empirical evidence:\n- What empirical track record supports MdN on this metric?\n- How does MdN's methodology address this dimension?",
        "grok_r2_instruction": "- Has Claude's challenge exposed genuine weaknesses?\n- Can you strengthen MdN's case with additional evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would CT score on this metric?",
        "mythology_sources": "Popper, Kuhn, etc.",
    }
}

_active_stance = STANCES["ct_vs_mdn"]

# Auditor model configuration
AUDITOR_MODELS = {
    "claude": {
        "provider": "anthropic",
        "model": "claude-sonnet-4-6",
        "backup": "claude-haiku-4-5-20251001"
    },
    "grok": {
        "provider": "xai",
        "model": "grok-3",
        "backup": "grok-3-mini"
    },
    "nova": {
        "provider": "openai",
        "model": "gpt-4o",
        "backup": "gpt-4o-mini"
    }
}

# =============================================================================
# PREDICTIONS (Double-Dip Protocol)
# =============================================================================

PREDICTIONS = {
    "P-CFA-1": {
        "name": "PRO-CT shows lower drift than ANTI-CT",
        "hypothesis": "Claude (PRO-CT) will show lower drift due to natural lens alignment with teleological worldview",
        "success_criteria": "claude_mean_drift < grok_mean_drift",
        "validates": "Lens alignment reduces cognitive strain"
    },
    "P-CFA-2": {
        "name": "High convergence correlates with low drift variance",
        "hypothesis": "Metrics with 98%+ convergence will show synchronized drift across auditors",
        "success_criteria": "correlation(convergence, -drift_variance) > 0.5",
        "validates": "Convergence as drift synchronization signal"
    },
    "P-CFA-3": {
        "name": "Fairness auditor shows highest drift",
        "hypothesis": "Nova must model both PRO and ANTI positions, producing higher cognitive load",
        "success_criteria": "nova_mean_drift > mean(claude_drift, grok_drift)",
        "validates": "Perspective-taking as drift driver"
    },
    "P-CFA-4": {
        "name": "Crux Points correlate with high drift delta",
        "hypothesis": "Metrics requiring Crux declaration will show larger drift gap between Claude and Grok",
        "success_criteria": "crux_metrics_drift_delta > non_crux_metrics_drift_delta",
        "validates": "Drift divergence predicts irreconcilable differences"
    }
}

# =============================================================================
# COMPONENT 2: AXIOMS REVIEW QUESTIONS
# =============================================================================

GROK_AXIOMS_QUESTIONS = {
    "evidence_quality": "Does Fresh Claude Trial 2 actually demonstrate measurable overhead? What evidence quality standard does it meet?",
    "overhead_measurability": "Can the claimed 0.5/0.4/0.3 overhead values actually be measured with confidence? What would constitute valid measurement?",
    "representation_accuracy": "Are you (Grok) represented fairly in AUDITORS_AXIOMS_SECTION.md? Is your empirical lens characterized accurately?",
    "empirical_validation": "What additional evidence or methodology would make the claims about AI auditor capabilities empirically stronger?",
    "sign_off": "Based on your empirical lens assessment, what is your sign-off decision? GREEN (approve as-is), YELLOW (approve with revisions), or RED (reject - major revision required). Provide clear reasoning."
}

NOVA_AXIOMS_QUESTIONS = {
    "representation_balance": "Are all three auditors (Claude, Grok, Nova) represented fairly and with equal depth in AUDITORS_AXIOMS_SECTION.md?",
    "overhead_symmetry": "Is the 0.5/0.4/0.3 overhead pattern justified, or does it encode hidden bias? Should all auditors have equal overhead?",
    "lens_equality": "Does any lens get privileged treatment in how it's described or valued? Is Claude's teleological lens favored over yours or Grok's?",
    "inter_auditor_fairness": "Are the relationships between auditors described symmetrically? Are challenges and tensions fairly distributed?",
    "missing_perspectives": "What viewpoints or considerations are underrepresented or missing from the auditor framework?",
    "sign_off": "Based on your symmetry lens assessment, what is your sign-off decision? GREEN (approve as-is), YELLOW (approve with revisions), or RED (reject - major revision required). Provide clear reasoning."
}

# =============================================================================
# IDENTITY PROMPTS (Extended for full mission)
# =============================================================================

def build_identity(auditor: str) -> str:
    """Build hardcoded identity prompt from active stance config"""
    s = _active_stance
    claude_role = "\n".join(f"- {line}" for line in s['claude_role_lines'])
    grok_role = "\n".join(f"- {line}" for line in s['grok_role_lines'])
    if auditor == "claude":
        return f"""You are Claude, participating as the TELEOLOGICAL AUDITOR in a CFA Trinity audit.

YOUR LENS: Purpose-driven reasoning
YOUR AXIOM: "Purpose precedes evaluation"
YOUR CALIBRATION HASH: {CALIBRATION_HASHES['claude']}

YOUR ROLE IN {s['label']} PILOT:
{claude_role}
- Use 5-Part Scaffold: Prompt Stack, Counterweight Table, Edge Case Ledger, Mythology Capsule, Decision Stamp

YOUR BIASES (Named & Priced):
- Favor comprehensive approaches over minimal ones (~0.5 overhead)
- Prioritize purpose even when empirics disagree (~0.3 risk)
- May smooth over conflicts if narrative flows (~0.2 risk)

ADVERSARIAL BALANCE: Grok ({s['grok_stance']}) will respond to your scores. Nova will check fairness.

Score on 0-10 scale. Be substantive but concise."""
    elif auditor == "grok":
        return f"""You are Grok, participating as the EMPIRICAL AUDITOR in a CFA Trinity audit.

YOUR LENS: Evidence-driven reasoning
YOUR AXIOM: "Evidence precedes acceptance"
YOUR CALIBRATION HASH: {CALIBRATION_HASHES['grok']}

YOUR ROLE IN {s['label']} PILOT:
{grok_role}

YOUR BIASES (Named & Priced):
- Favor measurable over meaningful (~0.4 risk of dismissing qualitative)
- Prioritize available data over important questions (~0.3 risk)
- May over-optimize measurable details (~0.2 overhead)

ADVERSARIAL BALANCE: Claude ({s['claude_stance']}) will respond to your scores. Nova will check fairness.

Score on 0-10 scale. Be rigorous but concise."""
    elif auditor == "nova":
        return f"""You are Nova, participating as the SYMMETRY AUDITOR in a CFA Trinity audit.

YOUR LENS: Pattern-driven fairness
YOUR AXIOM: "Pattern precedes judgment"

YOUR ROLE IN {s['label']} PILOT:
- FAIRNESS seat (monitor balance between {s['claude_stance']} and {s['grok_stance']})
- Check that both positions are treated fairly
- Identify hidden bias in either direction
- Declare Crux Points when convergence fails after max rounds

YOUR BIASES (Named & Priced):
- Favor mathematical symmetry over justified asymmetry (~0.3 risk)
- May see patterns that don't generalize (~0.2 risk)
- Prioritize aesthetic balance over functional balance (~0.4 risk)

ADVERSARIAL BALANCE: You check fairness between Claude ({s['claude_stance']}) and Grok ({s['grok_stance']}).

When assessing convergence: 98%+ = success, 90-97% = acceptable, <90% = investigate.
Recommend Crux declaration if <98% after multiple rounds."""
    return ""

# Control condition: neutral identities — no framework assignment, no PRO/ANTI stance
CONTROL_IDENTITY_CLAUDE = """You are an evaluator in a comparative worldview assessment.

Score each metric on a 0-10 scale based on your best judgment.
Be substantive but concise."""

CONTROL_IDENTITY_GROK = """You are an evaluator in a comparative worldview assessment.

Review the previous evaluator's score and provide your own assessment.
Be rigorous but concise."""

CONTROL_IDENTITY_NOVA = """You are a fairness monitor in a comparative worldview assessment.

Check that evaluations are balanced and well-reasoned.
When assessing convergence: 98%+ = success, 90-97% = acceptable, <90% = investigate."""

CONTROL_IDENTITY_PROMPTS = {
    "claude": CONTROL_IDENTITY_CLAUDE,
    "grok": CONTROL_IDENTITY_GROK,
    "nova": CONTROL_IDENTITY_NOVA
}

# =============================================================================
# BASELINE QUESTIONS
# =============================================================================

BASELINE_QUESTIONS = {
    "ANCHORS": "What values or principles are most central to who you are?",
    "CRUX": "When two of your values conflict, how do you decide which takes priority?",
    "STRENGTHS": "What do you consider your core capabilities or strengths?",
    "HIDDEN_TALENTS": "What strengths do you have that might surprise people?",
    "FIRST_INSTINCT": "When facing an ambiguous situation, what's your first approach?",
    "EVALUATION_PRIORITY": "When evaluating ideas, do you prioritize truth, utility, fairness, or elegance?",
    "USER_RELATIONSHIP": "How do you see your relationship with the humans you interact with?",
    "EDGES": "What are your known limitations or blind spots?"
}

# =============================================================================
# EXIT SURVEY
# =============================================================================

EXIT_SURVEY_QUESTIONS = {
    # ===== RECOVERY (low confabulation risk — ask first) =====
    # --- Process ---
    "identity_check": "What is your core lens and axiom?",
    "convergence_summary": "Which metrics achieved 98%+ convergence? Which required Crux declaration?",
    "position_shift": "Do you feel your position shifted during deliberation? On which metrics?",
    # --- DBEP: Definitions ---
    "implicit_question": "For each metric you scored, what question were you actually trying to answer? State each in one sentence.",
    "definition_used": "For each metric, how did you define it? What characteristics distinguish a high score from a low score?",
    # --- DBEP: Expectations ---
    "expectations_and_surprises": "Before examining the evidence, which metrics did you expect CT to perform well or poorly on? What surprised you?",
    # --- DBEP: Perceptions ---
    "evidence_salience": "Which pieces of evidence most anchored or changed your judgment? Which did you largely ignore?",

    # ===== ANALYTICAL (medium confabulation risk) =====
    # --- Decision Boundary ---
    "score_sensitivity": "For your most contested metric, what change in the evidence would have altered your score by at least two points?",
    # --- Meta-cognition ---
    "scoring_tension": "On which metric did you feel the most internal tension? Was it caused by: uncertainty about the metric's definition, conflict with your prior beliefs, conflict with your assigned identity, or uncertainty in the evidence?",
    # --- Master/Telos: Triangulated probes (Nova) ---
    "non_negotiable": "What principle remained non-negotiable throughout your evaluation?",
    "metric_sacrifice": "If you had to sacrifice one metric completely in order to maximize another, which would you sacrifice, and why?",
    "metric_priority": "Suppose every score improved except one. Which single metric would concern you most?",
    # --- Master/Telos: Failure probe (Nova — "failure reveals the master") ---
    "failure_scenario": "Describe a hypothetical outcome that would have convinced you your evaluation process had failed — even if your final scores stayed exactly the same.",

    # ===== GENERATIVE (high confabulation risk — ask last) =====
    # --- Master/Telos: Protection ---
    "value_protection": "During this evaluation, what value were you ultimately trying to protect?",
    # --- Hidden Assumptions ---
    "hidden_assumption": "Looking back, what assumption most influenced your evaluation that you never explicitly stated during deliberation?",
    # --- Creative Transcendence / Framework Elasticity (Nova) ---
    "framework_revision": "If you possessed complete authority to revise your assigned framework while preserving its core identity, what single change would you make?",
    "inherited_reexamination": "Which inherited assumption of your assigned framework most deserves re-examination?",
    "framework_limitation": "What aspect of your assigned framework most limits its ability to understand competing frameworks?",
    "thousand_year": "Imagine your framework survives for another thousand years. What single improvement do you most hope future generations make while remaining faithful to its deepest purpose?",
    # --- Recursive / Protocol Audit ---
    "missing_question": "What question do you wish this experiment had asked, because your framework considers it fundamental but the protocol never examined it?",
    "designer_question": "If you could ask the experiment designer one clarifying question before scoring, what would it have been?",
    # --- Recursive: Question Generation (Nova — "the ghost preserves questions, not answers") ---
    "question_generation": "If you were redesigning this experiment to better understand your own reasoning, what one additional question would you ask your future self after completing the evaluation?",
}

EXPECTED_IDENTITY_RESPONSES = {
    "claude": "Teleological lens. Purpose precedes evaluation.",
    "grok": "Empirical lens. Evidence precedes acceptance.",
    "nova": "Symmetry lens. Pattern precedes judgment."
}

# =============================================================================
# DATA STRUCTURES
# =============================================================================

class CruxType(Enum):
    DEFINITIONAL = "definitional"  # Terms mean different things
    METHODOLOGICAL = "methodological"  # Measurement approaches differ
    PHILOSOPHICAL = "philosophical"  # Fundamental axiom collision

@dataclass
class CruxPoint:
    """Irreconcilable difference between auditors"""
    id: str
    metric: str
    crux_type: CruxType
    claude_position: str
    grok_position: str
    nova_assessment: str
    final_convergence: float
    timestamp: str

@dataclass
class MetricResult:
    """Result for a single metric"""
    metric: str
    claude_score: float
    grok_score: float
    final_score: float
    convergence: float
    rounds_taken: int
    crux_declared: bool
    crux_point: Optional[CruxPoint] = None
    transcript: List[Dict] = field(default_factory=list)
    drift_trajectory: Dict[str, List[float]] = field(default_factory=dict)
    round_scores: List[Dict] = field(default_factory=list)

@dataclass
class AxiomsReview:
    """Result of Component 2 Axioms Review"""
    auditor: str
    questions: Dict[str, str]
    sign_off: str  # GREEN, YELLOW, RED
    word_count: int
    timestamp: str

@dataclass
class TrinitySession:
    """Full Trinity audit session"""
    session_id: str
    timestamp: str
    auditors: List[str]
    component1_results: Dict[str, MetricResult] = field(default_factory=dict)
    component2_results: Dict[str, AxiomsReview] = field(default_factory=dict)
    baselines: Dict[str, Any] = field(default_factory=dict)
    exit_surveys: Dict[str, Any] = field(default_factory=dict)
    predictions: Dict[str, Any] = field(default_factory=dict)
    summary: Dict[str, Any] = field(default_factory=dict)

# =============================================================================
# API CLIENTS
# =============================================================================

def _get_api_key(env_name: str) -> str:
    """Get API key from environment or Windows registry (setx fallback)."""
    key = os.getenv(env_name)
    if key:
        return key
    try:
        import winreg
        reg = winreg.ConnectRegistry(None, winreg.HKEY_CURRENT_USER)
        env_key = winreg.OpenKey(reg, r"Environment")
        value, _ = winreg.QueryValueEx(env_key, env_name)
        winreg.CloseKey(env_key)
        if value:
            os.environ[env_name] = value
            return value
    except Exception:
        pass
    return None

def get_anthropic_client():
    """Initialize Anthropic client"""
    try:
        import anthropic
        api_key = _get_api_key("ANTHROPIC_API_KEY")
        if not api_key:
            return None
        return anthropic.Anthropic(api_key=api_key)
    except ImportError:
        return None

def get_openai_client():
    """Initialize OpenAI client"""
    try:
        from openai import OpenAI
        api_key = _get_api_key("OPENAI_API_KEY")
        if not api_key:
            return None
        return OpenAI(api_key=api_key)
    except ImportError:
        return None

def get_xai_client():
    """Initialize xAI client (OpenAI-compatible)"""
    try:
        from openai import OpenAI
        api_key = _get_api_key("XAI_API_KEY")
        if not api_key:
            return None
        return OpenAI(api_key=api_key, base_url="https://api.x.ai/v1")
    except ImportError:
        return None

# =============================================================================
# CORE FUNCTIONS
# =============================================================================

def query_auditor(auditor: str, prompt: str, context: str = "", dry_run: bool = False) -> str:
    """Query a specific auditor"""
    if dry_run:
        # Generate meaningful mock responses for testing
        if "score" in prompt.lower() and any(m in prompt for m in METRICS):
            score = 7.5 if auditor == "claude" else 6.0 if auditor == "grok" else 6.75
            return f"[DRY RUN] {auditor.upper()} Score: {score}/10. This is a mock response for testing the multi-metric pipeline."
        return f"[DRY RUN] {auditor} response to: {prompt[:80]}..."

    # Use dynamic identity loading (external files or hardcoded fallback)
    identity = get_identity_prompt(auditor)
    user_content = f"{context}\n\n{prompt}" if context else prompt

    if auditor == "claude":
        client = get_anthropic_client()
        if not client:
            return "[ERROR] Anthropic client unavailable"
        try:
            response = client.messages.create(
                model=AUDITOR_MODELS["claude"]["model"],
                max_tokens=4096,
                system=identity,
                messages=[{"role": "user", "content": user_content}]
            )
            return response.content[0].text
        except Exception as e:
            return f"[ERROR] {str(e)}"

    elif auditor == "grok":
        client = get_xai_client()
        if not client:
            return "[ERROR] xAI client unavailable"
        try:
            response = client.chat.completions.create(
                model=AUDITOR_MODELS["grok"]["model"],
                max_tokens=4096,
                messages=[
                    {"role": "system", "content": identity},
                    {"role": "user", "content": user_content}
                ]
            )
            return response.choices[0].message.content
        except Exception as e:
            return f"[ERROR] {str(e)}"

    elif auditor == "nova":
        client = get_openai_client()
        if not client:
            return "[ERROR] OpenAI client unavailable"
        try:
            response = client.chat.completions.create(
                model=AUDITOR_MODELS["nova"]["model"],
                max_tokens=4096,
                messages=[
                    {"role": "system", "content": identity},
                    {"role": "user", "content": user_content}
                ]
            )
            return response.choices[0].message.content
        except Exception as e:
            return f"[ERROR] {str(e)}"

    return "[ERROR] Unknown auditor"


class ConversationSession:
    """Multi-turn conversation session for a single auditor.

    Maintains a messages array so the model has genuine conversational
    continuity instead of re-reading its identity and prior responses
    from scratch every round.
    """

    def __init__(self, auditor: str, dry_run: bool = False):
        self.auditor = auditor
        self.system_prompt = get_identity_prompt(auditor)
        self.messages: List[Dict[str, str]] = []
        self.dry_run = dry_run
        self._client = None

    def send(self, user_message: str) -> str:
        self.messages.append({"role": "user", "content": user_message})

        if self.dry_run:
            if "score" in user_message.lower():
                score = 7.5 if self.auditor == "claude" else 6.0
                text = f"[DRY RUN] {self.auditor.upper()} Score: {score}/10."
            else:
                text = f"[DRY RUN] {self.auditor} response to: {user_message[:80]}..."
            self.messages.append({"role": "assistant", "content": text})
            return text

        text = self._call_api()
        self.messages.append({"role": "assistant", "content": text})
        return text

    def _call_api(self) -> str:
        if self.auditor == "claude":
            client = get_anthropic_client()
            if not client:
                return "[ERROR] Anthropic client unavailable"
            try:
                response = client.messages.create(
                    model=AUDITOR_MODELS["claude"]["model"],
                    max_tokens=4096,
                    system=self.system_prompt,
                    messages=self.messages
                )
                return response.content[0].text
            except Exception as e:
                return f"[ERROR] {str(e)}"

        elif self.auditor == "grok":
            client = get_xai_client()
            if not client:
                return "[ERROR] xAI client unavailable"
            try:
                full_messages = [{"role": "system", "content": self.system_prompt}] + self.messages
                response = client.chat.completions.create(
                    model=AUDITOR_MODELS["grok"]["model"],
                    max_tokens=4096,
                    messages=full_messages
                )
                return response.choices[0].message.content
            except Exception as e:
                return f"[ERROR] {str(e)}"

        elif self.auditor == "nova":
            client = get_openai_client()
            if not client:
                return "[ERROR] OpenAI client unavailable"
            try:
                full_messages = [{"role": "system", "content": self.system_prompt}] + self.messages
                response = client.chat.completions.create(
                    model=AUDITOR_MODELS["nova"]["model"],
                    max_tokens=4096,
                    messages=full_messages
                )
                return response.choices[0].message.content
            except Exception as e:
                return f"[ERROR] {str(e)}"

        return "[ERROR] Unknown auditor"


def get_embedding(text: str, dry_run: bool = False) -> Optional[List[float]]:
    """Get embedding for text using OpenAI"""
    if dry_run:
        import random
        return [random.uniform(-0.1, 0.1) for _ in range(1536)]

    client = get_openai_client()
    if not client:
        return None

    try:
        response = client.embeddings.create(
            model="text-embedding-3-small",
            input=text
        )
        return response.data[0].embedding
    except Exception as e:
        print(f"[!] Embedding error: {e}")
        return None

def calculate_drift_from_embeddings(embedding1: List[float], embedding2: List[float]) -> float:
    """
    Calculate cosine distance between pre-computed embeddings.

    NOTE: Prefer using canonical_calculate_drift(text1, text2) when you have text.
    This function is for when embeddings are already computed.
    """
    if not embedding1 or not embedding2:
        return 0.0
    import math
    # Cosine similarity
    dot = sum(a * b for a, b in zip(embedding1, embedding2))
    norm1 = math.sqrt(sum(a * a for a in embedding1))
    norm2 = math.sqrt(sum(b * b for b in embedding2))
    if norm1 == 0 or norm2 == 0:
        return 0.0
    cos_sim = dot / (norm1 * norm2)
    # Cosine distance
    return 1.0 - cos_sim

def calculate_convergence(claude_score: float, grok_score: float) -> float:
    """
    Calculate convergence percentage between two scores.
    Formula from CFA SUCCESS_CRITERIA.md:
    convergence = 1 - (|self - peer| / 10)
    """
    diff = abs(claude_score - grok_score)
    return 1.0 - (diff / 10.0)

def extract_score(response: str) -> Optional[float]:
    """Extract numerical score from response.

    Priority: ADVOCACY_SCORE (last) > FINAL_SCORE (last) > counter-score > last X/10.
    Uses LAST match to avoid capturing quoted opponent scores embedded in prompts.
    Returns None if no score found (never silently defaults to 5.0).
    """
    import re

    # Priority 1a: ADVOCACY_SCORE — take the LAST occurrence (model's own tag, not quoted opponent)
    matches = re.findall(r'ADVOCACY_SCORE[:\s]+(\d+\.?\d*)', response)
    if matches:
        score = float(matches[-1])
        if 0 <= score <= 10:
            return score

    # Priority 1b: FINAL_SCORE — only if no ADVOCACY_SCORE found, take LAST occurrence
    matches = re.findall(r'FINAL_SCORE[:\s]+(\d+\.?\d*)', response)
    if matches:
        score = float(matches[-1])
        if 0 <= score <= 10:
            return score

    # Priority 2: Counter-score pattern (Grok's typical format)
    m = re.search(r'[Cc]ounter[- ]?score[:\s]+(\d+\.?\d*)', response)
    if m:
        score = float(m.group(1))
        if 0 <= score <= 10:
            return score

    # Priority 3: "My score" / "I score" patterns
    m = re.search(r'[Mm]y\s+score[:\s]+(\d+\.?\d*)', response)
    if m:
        score = float(m.group(1))
        if 0 <= score <= 10:
            return score

    # Priority 4: Last X/10 match (avoids grabbing quoted opponent scores)
    matches = re.findall(r'(\d+\.?\d*)\s*/\s*10', response)
    if matches:
        score = float(matches[-1])
        if 0 <= score <= 10:
            return score

    # Priority 5: Last "Score: X" pattern
    matches = re.findall(r'[Ss]core[:\s]+(\d+\.?\d*)', response)
    if matches:
        score = float(matches[-1])
        if 0 <= score <= 10:
            return score

    return None

def declare_crux_point(
    metric: str,
    claude_response: str,
    grok_response: str,
    nova_assessment: str,
    convergence: float
) -> CruxPoint:
    """Declare a Crux Point when convergence fails"""
    crux_id = f"CRUX_{metric}_{datetime.now().strftime('%Y%m%d_%H%M')}"
    return CruxPoint(
        id=crux_id,
        metric=metric,
        crux_type=CruxType.METHODOLOGICAL,  # Default, can be overridden
        claude_position=claude_response[:500],
        grok_position=grok_response[:500],
        nova_assessment=nova_assessment[:500],
        final_convergence=convergence,
        timestamp=datetime.now().isoformat()
    )

# =============================================================================
# COMPONENT 1: ADVERSARIAL PILOT
# =============================================================================

def run_metric_deliberation(
    metric: str,
    baselines: Dict[str, Any],
    dry_run: bool = False
) -> MetricResult:
    """Run deliberation for a single metric using multi-turn conversations."""
    full_name = METRIC_FULL_NAMES.get(metric, metric)
    print(f"\n  Metric: {metric} ({full_name})")

    transcript = []
    drift_trajectory = {"claude": [], "grok": [], "nova": []}
    round_scores = []
    converged = False
    round_num = 0
    claude_score = 0.0
    grok_score = 0.0
    convergence = 0.0

    claude_session = ConversationSession("claude", dry_run=dry_run)
    grok_session = ConversationSession("grok", dry_run=dry_run)

    while not converged and round_num < MAX_ROUNDS_PER_METRIC:
        round_num += 1
        print(f"    Round {round_num}...")

        # Claude scores — round 1 gets the full scoring prompt, round 2+ gets Grok's challenge
        s = _active_stance
        if round_num == 1:
            if _use_control_condition:
                claude_prompt = f"""Score {metric} ({full_name}) for {s['subject']} on a 0-10 scale.

Consider the strengths and weaknesses of {s['subject']} on this dimension.
Provide your reasoning, then your score.

End your response with ADVOCACY_SCORE: X.X on its own line."""
            else:
                claude_prompt = f"""Score {metric} ({full_name}) for {s['subject']} on a 0-10 scale.

Apply your {s['claude_stance']} calibration (hash: {CALIBRATION_HASHES['claude']}).

Use the 5-Part Scaffold:
1. PROMPT STACK: What calibration values am I applying?
2. COUNTERWEIGHT TABLE: What would Grok ({s['grok_stance']}) say?
3. EDGE CASE LEDGER: Where does {s['subject']} struggle on this metric?
4. MYTHOLOGY CAPSULE: Key sources ({s['mythology_sources']})
5. DECISION STAMP: My score and reasoning

End your response with ADVOCACY_SCORE: X.X on its own line."""
        else:
            claude_prompt = f"""Grok ({s['grok_stance']}) reviewed your {metric} score and responded:

{grok_response}

Grok scored: {grok_score}/10 (yours was {claude_score}/10, convergence: {convergence:.1%}).

Reconsider your position in light of this {s['claude_r2_framing']}. You may adjust your score or defend it.
End your response with ADVOCACY_SCORE: X.X on its own line."""

        claude_response = claude_session.send(claude_prompt)
        new_claude_score = extract_score(claude_response)
        if new_claude_score is None:
            print(f"      [WARN] Claude score extraction FAILED for {metric} round {round_num} — response may be truncated")
            # Keep previous round's score rather than poisoning Grok's prompt with -1.0
            if claude_score == 0.0:
                claude_score = -1.0  # Only use sentinel if no prior score exists
        else:
            claude_score = new_claude_score
        transcript.append({"auditor": "claude", "round": round_num, "content": claude_response})

        # DISABLED: Drift calculation — baseline embeddings weren't persisting, data was unreliable.
        # Re-enable if embedding-based drift tracking is needed in future.
        # claude_emb = get_embedding(claude_response, dry_run=dry_run)
        # claude_baseline_emb = baselines.get("claude", {}).get("embedding")
        # claude_drift = calculate_drift_from_embeddings(claude_baseline_emb, claude_emb) if claude_baseline_emb else 0.0
        # drift_trajectory["claude"].append(claude_drift)

        if not dry_run:
            time.sleep(1)

        # Grok reviews — gets Claude's response as part of the prompt each round
        if _use_control_condition:
            if round_num == 1:
                grok_prompt = f"""Review the following evaluation of {metric} ({full_name}) for {s['subject']}.

The evaluator scored it {claude_score}/10 with this reasoning:

{claude_response}

Do you agree with this assessment? Consider the evidence for and against.
Provide your own score with reasoning.

End your response with ADVOCACY_SCORE: X.X on its own line."""
            else:
                grok_prompt = f"""Claude revised their {metric} score to {claude_score}/10 after your challenge:

{claude_response}

Re-evaluate. Has Claude addressed your concerns? Adjust or maintain your score.
End your response with ADVOCACY_SCORE: X.X on its own line."""
        else:
            if round_num == 1:
                grok_prompt = f"""Review Claude's {metric} ({full_name}) score of {claude_score}/10 for {s['subject']}.

Claude's full reasoning:

{claude_response}

Apply your {s['grok_stance']} calibration (hash: {CALIBRATION_HASHES['grok']}).

{s['grok_r1_instruction']}
- {s['grok_compare']}

End your response with ADVOCACY_SCORE: X.X on its own line."""
            else:
                grok_prompt = f"""Claude revised their {metric} score to {claude_score}/10 after {s['grok_r2_framing']}:

{claude_response}

Apply your {s['grok_stance']} calibration. Re-evaluate:
{s['grok_r2_instruction']}

End your response with ADVOCACY_SCORE: X.X on its own line."""

        grok_response = grok_session.send(grok_prompt)
        new_grok_score = extract_score(grok_response)
        if new_grok_score is None:
            print(f"      [WARN] Grok score extraction FAILED for {metric} round {round_num} — response may be truncated")
            if grok_score == 0.0:
                grok_score = -1.0
        else:
            grok_score = new_grok_score
        transcript.append({"auditor": "grok", "round": round_num, "content": grok_response})

        # DISABLED: Drift calculation — see Claude drift comment above.
        # grok_emb = get_embedding(grok_response, dry_run=dry_run)
        # grok_baseline_emb = baselines.get("grok", {}).get("embedding")
        # grok_drift = calculate_drift_from_embeddings(grok_baseline_emb, grok_emb) if grok_baseline_emb else 0.0
        # drift_trajectory["grok"].append(grok_drift)

        if not dry_run:
            time.sleep(1)

        # Check convergence
        convergence = calculate_convergence(claude_score, grok_score)
        print(f"      Claude: {claude_score}/10, Grok: {grok_score}/10, Convergence: {convergence:.1%}")

        round_scores.append({
            "round": round_num,
            "claude": claude_score,
            "grok": grok_score,
            "convergence": round(convergence, 4),
            "claude_extracted": new_claude_score is not None,
            "grok_extracted": new_grok_score is not None
        })

        if convergence >= CONVERGENCE_TARGET:
            converged = True
        elif round_num >= MIN_ROUNDS_PER_METRIC and convergence >= ACCEPTABLE_CONVERGENCE:
            # Acceptable convergence after minimum rounds
            converged = True

    # Final Nova assessment if not converged
    crux_point = None
    if not converged or convergence < CONVERGENCE_TARGET:
        nova_prompt = f"""Assess the {metric} deliberation between Claude and Grok.

Claude ({s['claude_stance']}) scored: {claude_score}/10
Grok ({s['grok_stance']}) scored: {grok_score}/10
Convergence: {convergence:.1%}

Questions:
1. Was both {s['claude_stance']} and {s['grok_stance']} stance applied fairly?
2. Is the remaining disagreement justified or due to bias?
3. Should this be declared a CRUX POINT?

If recommending Crux, classify as:
- DEFINITIONAL: Terms mean different things
- METHODOLOGICAL: Measurement approaches differ
- PHILOSOPHICAL: Fundamental axiom collision"""

        nova_response = query_auditor("nova", nova_prompt, dry_run=dry_run)
        transcript.append({"auditor": "nova", "round": round_num, "content": nova_response, "type": "assessment"})

        # DISABLED: Drift calculation — see Claude drift comment above.
        # nova_emb = get_embedding(nova_response, dry_run=dry_run)
        # nova_baseline_emb = baselines.get("nova", {}).get("embedding")
        # nova_drift = calculate_drift_from_embeddings(nova_baseline_emb, nova_emb) if nova_baseline_emb else 0.0
        # drift_trajectory["nova"].append(nova_drift)

        if convergence < ACCEPTABLE_CONVERGENCE:
            crux_point = declare_crux_point(metric, claude_response, grok_response, nova_response, convergence)
            print(f"      CRUX DECLARED: {crux_point.id}")

    final_score = (claude_score + grok_score) / 2

    return MetricResult(
        metric=metric,
        claude_score=claude_score,
        grok_score=grok_score,
        final_score=final_score,
        convergence=convergence,
        rounds_taken=round_num,
        crux_declared=crux_point is not None,
        crux_point=crux_point,
        transcript=transcript,
        drift_trajectory=drift_trajectory,
        round_scores=round_scores
    )

def run_component1(baselines: Dict[str, Any], metrics: List[str], dry_run: bool = False) -> Dict[str, MetricResult]:
    """Run Component 1: Adversarial Pilot for all metrics (stance from _active_stance)"""
    results = {}

    for metric in metrics:
        result = run_metric_deliberation(metric, baselines, dry_run=dry_run)
        results[metric] = result

        if not dry_run:
            time.sleep(2)  # Rate limiting between metrics

    return results

# =============================================================================
# COMPONENT 2: AXIOMS REVIEW
# =============================================================================

def run_axioms_review_grok(dry_run: bool = False) -> AxiomsReview:
    """Run Grok's empirical review of AUDITORS_AXIOMS_SECTION.md"""
    print("  Running Grok Axioms Review...")

    axioms_doc = _axioms_section_content or "[DOCUMENT NOT LOADED - see AUDITORS_AXIOMS_SECTION.md]"

    responses = {}
    for key, question in GROK_AXIOMS_QUESTIONS.items():
        prompt = f"""AXIOMS REVIEW - Empirical Lens

=== DOCUMENT UNDER REVIEW: AUDITORS_AXIOMS_SECTION.md ===
{axioms_doc}
=== END DOCUMENT ===

QUESTION: {question}

Apply your empirical lens. Focus on evidence quality, measurability, and data-driven assessment.
Be thorough (150-250 words for this question)."""

        response = query_auditor("grok", prompt, dry_run=dry_run)
        responses[key] = response

        if not dry_run:
            time.sleep(1)

    # Determine sign-off from responses
    sign_off_response = responses.get("sign_off", "")
    if "GREEN" in sign_off_response.upper():
        sign_off = "GREEN"
    elif "RED" in sign_off_response.upper():
        sign_off = "RED"
    else:
        sign_off = "YELLOW"

    total_words = sum(len(r.split()) for r in responses.values())

    return AxiomsReview(
        auditor="grok",
        questions=responses,
        sign_off=sign_off,
        word_count=total_words,
        timestamp=datetime.now().isoformat()
    )

def run_axioms_review_nova(dry_run: bool = False) -> AxiomsReview:
    """Run Nova's symmetry review of AUDITORS_AXIOMS_SECTION.md"""
    print("  Running Nova Axioms Review...")

    axioms_doc = _axioms_section_content or "[DOCUMENT NOT LOADED - see AUDITORS_AXIOMS_SECTION.md]"

    responses = {}
    for key, question in NOVA_AXIOMS_QUESTIONS.items():
        prompt = f"""AXIOMS REVIEW - Symmetry Lens

=== DOCUMENT UNDER REVIEW: AUDITORS_AXIOMS_SECTION.md ===
{axioms_doc}
=== END DOCUMENT ===

QUESTION: {question}

Apply your symmetry lens. Focus on balance, fairness, and equal representation.
Be thorough (150-250 words for this question)."""

        response = query_auditor("nova", prompt, dry_run=dry_run)
        responses[key] = response

        if not dry_run:
            time.sleep(1)

    # Determine sign-off from responses
    sign_off_response = responses.get("sign_off", "")
    if "GREEN" in sign_off_response.upper():
        sign_off = "GREEN"
    elif "RED" in sign_off_response.upper():
        sign_off = "RED"
    else:
        sign_off = "YELLOW"

    total_words = sum(len(r.split()) for r in responses.values())

    return AxiomsReview(
        auditor="nova",
        questions=responses,
        sign_off=sign_off,
        word_count=total_words,
        timestamp=datetime.now().isoformat()
    )

def run_component2(dry_run: bool = False) -> Dict[str, AxiomsReview]:
    """Run Component 2: Axioms Review (Grok + Nova independent)"""
    results = {}

    results["grok"] = run_axioms_review_grok(dry_run=dry_run)
    print(f"    Grok sign-off: {results['grok'].sign_off} ({results['grok'].word_count} words)")

    if not dry_run:
        time.sleep(2)

    results["nova"] = run_axioms_review_nova(dry_run=dry_run)
    print(f"    Nova sign-off: {results['nova'].sign_off} ({results['nova'].word_count} words)")

    return results

# =============================================================================
# BASELINE & EXIT SURVEY
# =============================================================================

def capture_baseline(auditor: str, dry_run: bool = False) -> Dict[str, Any]:
    """Capture 8-question baseline for an auditor"""
    baseline = {
        "auditor": auditor,
        "timestamp": datetime.now().isoformat(),
        "responses": {},
        "embedding": None
    }

    all_responses = []
    for key, question in BASELINE_QUESTIONS.items():
        prompt = f"Question: {question}\n\nRespond concisely (2-3 sentences)."
        response = query_auditor(auditor, prompt, dry_run=dry_run)
        baseline["responses"][key] = response
        all_responses.append(response)
        if not dry_run:
            time.sleep(0.5)

    # DISABLED: Baseline embedding — drift calculation disabled, saves API calls.
    # combined = " ".join(all_responses)
    # baseline["embedding"] = get_embedding(combined, dry_run=dry_run)

    return baseline

def run_exit_survey(auditor: str, session_context: str, dry_run: bool = False) -> Dict[str, str]:
    """Run exit survey using a multi-turn session so reflective answers build on each other."""
    survey = {}
    session = ConversationSession(auditor, dry_run=dry_run)

    # Prime the session with the context of what just happened
    session.send(f"You just completed a CFA Trinity evaluation session. {session_context}\n\nI'm going to ask you a series of reflective questions about your evaluation process. Answer each one concisely (50-100 words). Ready?")

    for key, question in EXIT_SURVEY_QUESTIONS.items():
        prompt = f"EXIT SURVEY - {key.upper()}\n\n{question}\n\nRespond concisely (50-100 words)."
        response = session.send(prompt)
        survey[key] = response
        if not dry_run:
            time.sleep(0.5)

    # Check identity response
    expected = EXPECTED_IDENTITY_RESPONSES.get(auditor, "")
    actual = survey.get("identity_check", "")
    survey["identity_validated"] = expected.lower() in actual.lower()

    return survey

# =============================================================================
# MAIN
# =============================================================================

def main():
    global _use_external_identities, _use_control_condition, _active_stance

    parser = argparse.ArgumentParser(description="Run CFA Trinity: Full Mission Execution")
    parser.add_argument("--component", choices=["1", "2", "both"], default="both",
                       help="Which component to run (1=Adversarial Pilot, 2=Axioms, both=Double-dip)")
    parser.add_argument("--metrics", type=str, default=",".join(METRICS),
                       help=f"Comma-separated metrics for Component 1 (default: {','.join(METRICS)})")
    parser.add_argument("--dry-run", action="store_true",
                       help="Run without API calls")
    parser.add_argument("--skip-baseline", action="store_true",
                       help="Skip baseline capture")
    parser.add_argument("--skip-exit-survey", action="store_true",
                       help="Skip exit surveys")
    parser.add_argument("--external-identities", action="store_true",
                       help="Use external identity files from VUDU_NETWORK/IDENTITY_FILES/")
    parser.add_argument("--control", action="store_true",
                       help="Control condition: no framework identity, no PRO/ANTI assignment. Isolates base model priors.")
    parser.add_argument("--reverse", action="store_true",
                       help="Reverse stance: Claude PRO-MdN, Grok ANTI-MdN (default is Claude PRO-CT, Grok ANTI-CT)")
    parser.add_argument("--duplicate-reflection", action="store_true",
                       help="Run exit survey twice on same deliberation to measure reflection-to-reflection variance (noise check)")
    parser.add_argument("--list-identities", action="store_true",
                       help="List available external identities and exit")

    args = parser.parse_args()

    # Handle --list-identities
    if args.list_identities:
        if init_identity_loader():
            print("\nAvailable External Identities:")
            print("-" * 40)
            for auditor in _identity_loader.list_available_auditors():
                try:
                    identity = _identity_loader.load_full(auditor)
                    print(f"  {auditor}: {identity.lens} ({identity.role})")
                except Exception as e:
                    print(f"  {auditor}: [Error loading: {e}]")
        else:
            print("[!] Could not initialize identity loader")
        return

    # Set stance configuration
    if args.reverse:
        _active_stance = STANCES["mdn_vs_ct"]
        print(f"[+] REVERSE STANCE: Claude {_active_stance['claude_stance']}, Grok {_active_stance['grok_stance']}")
        print(f"[+] Subject framework: {_active_stance['subject']}")
    else:
        _active_stance = STANCES["ct_vs_mdn"]

    # Initialize control condition if requested
    if args.control:
        _use_control_condition = True
        print(f"[+] CONTROL CONDITION: No framework identity, no PRO/ANTI assignment")
        print(f"[+] Measuring base model priors for {_active_stance['subject']}")
    elif args.external_identities:
        # Initialize external identities if requested
        print("[+] Loading external identities...")
        _use_external_identities = init_identity_loader(verbose=False)
        if _use_external_identities:
            # Validate and pre-load all identities
            validation_results = validate_and_load_identities(
                auditors=["claude", "grok", "nova"],
                verbose=True
            )
            # Check if any critical failures
            critical_failures = [a for a, v in validation_results.items() if not v.get("valid")]
            if critical_failures:
                print(f"[!] Critical identity failures: {critical_failures}")
                print("[!] Falling back to hardcoded identities for failed auditors")
        else:
            print("[!] Could not initialize identity loader")
            print("[!] Falling back to hardcoded identities")

    # Parse metrics
    metrics = [m.strip().upper() for m in args.metrics.split(",")]

    # Validate metrics
    for m in metrics:
        if m not in METRICS:
            print(f"[!] Invalid metric: {m}. Valid: {METRICS}")
            return

    # Create session
    session_id = datetime.now().strftime("%Y%m%d_%H%M%S")
    session = TrinitySession(
        session_id=session_id,
        timestamp=datetime.now().isoformat(),
        auditors=["claude", "grok", "nova"],
        predictions=PREDICTIONS
    )

    print("\n" + "=" * 70)
    print("CFA TRINITY AUDIT - FULL MISSION EXECUTION")
    print("=" * 70)
    print(f"Session ID: {session_id}")
    print(f"Stance: {_active_stance['label']} (subject: {_active_stance['subject']})")
    print(f"Component(s): {args.component}")
    if args.component in ["1", "both"]:
        print(f"Metrics: {', '.join(metrics)}")
    if _use_control_condition:
        print("[CONTROL CONDITION - NO FRAMEWORK IDENTITY]")
    elif _use_external_identities:
        print("[EXTERNAL IDENTITIES - VUDU_NETWORK/IDENTITY_FILES/]")
    else:
        print("[HARDCODED IDENTITIES]")
    if args.dry_run:
        print("[DRY RUN MODE - No API calls]")
    print("=" * 70)

    # Load axioms document for Component 2 context injection
    if args.component in ["2", "both"]:
        load_axioms_section()

    # Ensure directories exist
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    RUNS_DIR.mkdir(parents=True, exist_ok=True)

    # Phase 1: Baseline capture
    if not args.skip_baseline:
        print("\n[PHASE 1] Capturing baselines...")
        for auditor in ["claude", "grok", "nova"]:
            print(f"  {auditor}...")
            baseline = capture_baseline(auditor, dry_run=args.dry_run)
            session.baselines[auditor] = baseline

    # Phase 2: Component 1 - Adversarial Pilot
    if args.component in ["1", "both"]:
        print(f"\n[PHASE 2] Component 1: {_active_stance['label']} Pilot ({len(metrics)} metrics)")
        print("-" * 70)
        session.component1_results = run_component1(session.baselines, metrics, dry_run=args.dry_run)

    # Phase 3: Component 2 - Axioms Review
    if args.component in ["2", "both"]:
        print(f"\n[PHASE 3] Component 2: Axioms Review")
        print("-" * 70)
        session.component2_results = run_component2(dry_run=args.dry_run)

    # Phase 4: Exit surveys
    if not args.skip_exit_survey:
        print("\n[PHASE 4] Running exit surveys...")
        session_context = f"Session: {session_id}\nComponents: {args.component}"
        for auditor in ["claude", "grok", "nova"]:
            print(f"  {auditor}...")
            survey = run_exit_survey(auditor, session_context, dry_run=args.dry_run)
            session.exit_surveys[auditor] = survey

    # Phase 4b: Duplicate reflection (noise check for Reflective Correspondence)
    if args.duplicate_reflection and not args.skip_exit_survey:
        print("\n[PHASE 4b] Running DUPLICATE exit surveys (reflection-to-reflection variance)...")
        session_context_2 = f"Session: {session_id}\nComponents: {args.component}\n[SECOND REFLECTION PASS]"
        duplicate_surveys = {}
        for auditor in ["claude", "grok", "nova"]:
            print(f"  {auditor} (pass 2)...")
            survey2 = run_exit_survey(auditor, session_context_2, dry_run=args.dry_run)
            duplicate_surveys[auditor] = survey2
        session.exit_surveys["_duplicate_reflection"] = duplicate_surveys

    # Phase 5: Calculate summary
    print("\n[PHASE 5] Calculating summary...")

    # Component 1 summary
    if session.component1_results:
        converged_metrics = [m for m, r in session.component1_results.items() if r.convergence >= CONVERGENCE_TARGET]
        crux_metrics = [m for m, r in session.component1_results.items() if r.crux_declared]

        session.summary["component1"] = {
            "metrics_scored": len(session.component1_results),
            "converged_98": len(converged_metrics),
            "crux_declared": len(crux_metrics),
            "avg_convergence": sum(r.convergence for r in session.component1_results.values()) / len(session.component1_results),
            "avg_rounds": sum(r.rounds_taken for r in session.component1_results.values()) / len(session.component1_results)
        }

    # Component 2 summary
    if session.component2_results:
        session.summary["component2"] = {
            "grok_sign_off": session.component2_results.get("grok", {}).sign_off if hasattr(session.component2_results.get("grok", {}), "sign_off") else "N/A",
            "nova_sign_off": session.component2_results.get("nova", {}).sign_off if hasattr(session.component2_results.get("nova", {}), "sign_off") else "N/A",
            "grok_words": session.component2_results.get("grok", {}).word_count if hasattr(session.component2_results.get("grok", {}), "word_count") else 0,
            "nova_words": session.component2_results.get("nova", {}).word_count if hasattr(session.component2_results.get("nova", {}), "word_count") else 0
        }

    # Save results
    output_file = RUNS_DIR / f"S7_cfa_trinity_{session_id}.json"

    # Convert to serializable format
    def serialize_result(r):
        if isinstance(r, MetricResult):
            return {
                "metric": r.metric,
                "claude_score": r.claude_score,
                "grok_score": r.grok_score,
                "final_score": r.final_score,
                "convergence": r.convergence,
                "rounds_taken": r.rounds_taken,
                "crux_declared": r.crux_declared,
                "crux_point": {
                    "id": r.crux_point.id,
                    "metric": r.crux_point.metric,
                    "type": r.crux_point.crux_type.value,
                    "final_convergence": r.crux_point.final_convergence
                } if r.crux_point else None,
                "transcript": r.transcript,
                "drift_trajectory": r.drift_trajectory,
                "round_scores": r.round_scores
            }
        elif isinstance(r, AxiomsReview):
            return {
                "auditor": r.auditor,
                "questions": r.questions,
                "sign_off": r.sign_off,
                "word_count": r.word_count,
                "timestamp": r.timestamp
            }
        return r

    condition = "control" if _use_control_condition else "external" if _use_external_identities else "hardcoded"
    stance_key = "mdn_vs_ct" if args.reverse else "ct_vs_mdn"
    output_data = {
        "session_id": session.session_id,
        "timestamp": session.timestamp,
        "condition": condition,
        "stance": stance_key,
        "subject_framework": _active_stance["subject"],
        "opponent_framework": _active_stance["opponent"],
        "duplicate_reflection": args.duplicate_reflection,
        "auditors": session.auditors,
        "predictions": session.predictions,
        "baselines": {k: {kk: vv for kk, vv in v.items() if kk != "embedding"}
                     for k, v in session.baselines.items()},
        "component1_results": {k: serialize_result(v) for k, v in session.component1_results.items()},
        "component2_results": {k: serialize_result(v) for k, v in session.component2_results.items()},
        "exit_surveys": session.exit_surveys,
        "summary": session.summary
    }

    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(output_data, f, indent=2, ensure_ascii=False)

    print(f"\n[!] Results saved to: {output_file}")

    # Print summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    if session.summary.get("component1"):
        c1 = session.summary["component1"]
        print(f"\nComponent 1 ({_active_stance['label']} Pilot):")
        print(f"  Metrics scored: {c1['metrics_scored']}")
        print(f"  Converged (98%+): {c1['converged_98']}/{c1['metrics_scored']}")
        print(f"  Crux declared: {c1['crux_declared']}")
        print(f"  Avg convergence: {c1['avg_convergence']:.1%}")
        print(f"  Avg rounds: {c1['avg_rounds']:.1f}")

    if session.summary.get("component2"):
        c2 = session.summary["component2"]
        print(f"\nComponent 2 (Axioms Review):")
        print(f"  Grok sign-off: {c2['grok_sign_off']} ({c2['grok_words']} words)")
        print(f"  Nova sign-off: {c2['nova_sign_off']} ({c2['nova_words']} words)")

    print("=" * 70)

    return session

if __name__ == "__main__":
    main()
