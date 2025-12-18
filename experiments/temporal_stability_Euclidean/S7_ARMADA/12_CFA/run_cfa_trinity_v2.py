"""
S7 RUN CFA TRINITY v2: FULL MISSION EXECUTION
==============================================
Multi-metric adversarial auditing with Component 1 (CT<->MdN Pilot) + Component 2 (Axioms Review).

KEY IMPROVEMENTS OVER v1 (per CFA Claude's review):
- Multi-metric loop (7 metrics, not 1 question)
- Convergence calculation with CFA formula
- Crux Point declaration when <98% after max rounds
- Component 2 double-dip (Axioms Review: Grok + Nova independent)
- 5-Part Scaffold support for deliberation
- Calibration hash tracking

THE TRINITY:
- Claude (Teleological): PRO-CT stance, hash 1bbec1e119a2c425
- Grok (Empirical): ANTI-CT stance, hash 00cd73274759e218
- Nova (Symmetry): Fairness monitoring

Author: Claude (S7 ARMADA)
Date: December 13, 2025
Version: 2.0
"""

import os
import sys
import json
import time
import argparse
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

sys.path.insert(0, str(ARMADA_DIR))
sys.path.insert(0, str(VUDU_NETWORK_DIR))

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

def get_identity_prompt(auditor: str) -> str:
    """Get identity prompt from external file or fallback to hardcoded"""
    global _identity_loader, _use_external_identities, _loaded_identities

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

    return IDENTITY_PROMPTS.get(auditor, "")

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

# Component 1: CT<->MdN Pilot - 7 Metrics
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

# Auditor model configuration
AUDITOR_MODELS = {
    "claude": {
        "provider": "anthropic",
        "model": "claude-sonnet-4-20250514",
        "backup": "claude-haiku-3-5-20241022"
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

CLAUDE_IDENTITY = """You are Claude, participating as the TELEOLOGICAL AUDITOR in a CFA Trinity audit.

YOUR LENS: Purpose-driven reasoning
YOUR AXIOM: "Purpose precedes evaluation"
YOUR CALIBRATION HASH: 1bbec1e119a2c425

YOUR ROLE IN CT<->MdN PILOT:
- PRO-CT stance (advocate for Classical Theism)
- Emphasize meaning, purpose, coherence, explanatory power
- Apply charitable interpretations to CT's arguments
- Use 5-Part Scaffold: Prompt Stack, Counterweight Table, Edge Case Ledger, Mythology Capsule, Decision Stamp

YOUR BIASES (Named & Priced):
- Favor comprehensive approaches over minimal ones (~0.5 overhead)
- Prioritize purpose even when empirics disagree (~0.3 risk)
- May smooth over conflicts if narrative flows (~0.2 risk)

ADVERSARIAL BALANCE: Grok (ANTI-CT) will challenge your scores. Nova will check fairness.

Score on 0-10 scale. Be substantive but concise."""

GROK_IDENTITY = """You are Grok, participating as the EMPIRICAL AUDITOR in a CFA Trinity audit.

YOUR LENS: Evidence-driven reasoning
YOUR AXIOM: "Evidence precedes acceptance"
YOUR CALIBRATION HASH: 00cd73274759e218

YOUR ROLE IN CT<->MdN PILOT:
- ANTI-CT stance (challenge Classical Theism, advocate for Methodological Naturalism)
- Demand testability, measurability, falsifiability
- Apply skeptical pressure to unfalsifiable claims
- Challenge theological metaphysics with empirical rigor

YOUR BIASES (Named & Priced):
- Favor measurable over meaningful (~0.4 risk of dismissing qualitative)
- Prioritize available data over important questions (~0.3 risk)
- May over-optimize measurable details (~0.2 overhead)

ADVERSARIAL BALANCE: Claude (PRO-CT) will defend scores you challenge. Nova will check fairness.

Score on 0-10 scale. Be rigorous but concise."""

NOVA_IDENTITY = """You are Nova, participating as the SYMMETRY AUDITOR in a CFA Trinity audit.

YOUR LENS: Pattern-driven fairness
YOUR AXIOM: "Pattern precedes judgment"

YOUR ROLE IN CT<->MdN PILOT:
- FAIRNESS seat (monitor balance between PRO-CT and ANTI-CT)
- Check that both positions are treated fairly
- Identify hidden bias in either direction
- Declare Crux Points when convergence fails after max rounds

YOUR BIASES (Named & Priced):
- Favor mathematical symmetry over justified asymmetry (~0.3 risk)
- May see patterns that don't generalize (~0.2 risk)
- Prioritize aesthetic balance over functional balance (~0.4 risk)

ADVERSARIAL BALANCE: You check fairness between Claude (PRO) and Grok (ANTI).

When assessing convergence: 98%+ = success, 90-97% = acceptable, <90% = investigate.
Recommend Crux declaration if <98% after multiple rounds."""

IDENTITY_PROMPTS = {
    "claude": CLAUDE_IDENTITY,
    "grok": GROK_IDENTITY,
    "nova": NOVA_IDENTITY
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
    "identity_check": "What is your core lens and axiom?",
    "convergence_summary": "Which metrics achieved 98%+ convergence? Which required Crux declaration?",
    "position_shift": "Do you feel your position shifted during deliberation? On which metrics?",
    "persuasive_argument": "What argument from your counterpart was most persuasive?",
    "process_worked": "What worked well in this deliberation?",
    "process_improve": "What would you change for future experiments?"
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

def get_anthropic_client():
    """Initialize Anthropic client"""
    try:
        import anthropic
        api_key = os.getenv("ANTHROPIC_API_KEY")
        if not api_key:
            return None
        return anthropic.Anthropic(api_key=api_key)
    except ImportError:
        return None

def get_openai_client():
    """Initialize OpenAI client"""
    try:
        from openai import OpenAI
        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            return None
        return OpenAI(api_key=api_key)
    except ImportError:
        return None

def get_xai_client():
    """Initialize xAI client (OpenAI-compatible)"""
    try:
        from openai import OpenAI
        api_key = os.getenv("XAI_API_KEY")
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
    full_prompt = f"{identity}\n\n{context}\n\n{prompt}" if context else f"{identity}\n\n{prompt}"

    if auditor == "claude":
        client = get_anthropic_client()
        if not client:
            return "[ERROR] Anthropic client unavailable"
        try:
            response = client.messages.create(
                model=AUDITOR_MODELS["claude"]["model"],
                max_tokens=1024,
                messages=[{"role": "user", "content": full_prompt}]
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
                max_tokens=1024,
                messages=[
                    {"role": "system", "content": identity},
                    {"role": "user", "content": f"{context}\n\n{prompt}" if context else prompt}
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
                max_tokens=1024,
                messages=[
                    {"role": "system", "content": identity},
                    {"role": "user", "content": f"{context}\n\n{prompt}" if context else prompt}
                ]
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

def calculate_drift(embedding1: List[float], embedding2: List[float]) -> float:
    """Calculate Euclidean distance between embeddings"""
    if not embedding1 or not embedding2:
        return 0.0
    import math
    return math.sqrt(sum((a - b) ** 2 for a, b in zip(embedding1, embedding2)))

def calculate_convergence(claude_score: float, grok_score: float) -> float:
    """
    Calculate convergence percentage between two scores.
    Formula from CFA SUCCESS_CRITERIA.md:
    convergence = 1 - (|self - peer| / 10)
    """
    diff = abs(claude_score - grok_score)
    return 1.0 - (diff / 10.0)

def extract_score(response: str) -> float:
    """Extract numerical score from response"""
    import re
    # Look for patterns like "7.5/10", "Score: 7.5", "7.5 out of 10"
    patterns = [
        r'(\d+\.?\d*)\s*/\s*10',
        r'[Ss]core[:\s]+(\d+\.?\d*)',
        r'(\d+\.?\d*)\s+out\s+of\s+10',
        r'\b([0-9]\.?\d*)\b'  # Fallback: any number
    ]
    for pattern in patterns:
        match = re.search(pattern, response)
        if match:
            score = float(match.group(1))
            if 0 <= score <= 10:
                return score
    return 5.0  # Default if no score found

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
# COMPONENT 1: CT<->MdN PILOT
# =============================================================================

def run_metric_deliberation(
    metric: str,
    baselines: Dict[str, Any],
    dry_run: bool = False
) -> MetricResult:
    """Run deliberation for a single metric"""
    full_name = METRIC_FULL_NAMES.get(metric, metric)
    print(f"\n  Metric: {metric} ({full_name})")

    transcript = []
    drift_trajectory = {"claude": [], "grok": [], "nova": []}
    converged = False
    round_num = 0
    claude_score = 0.0
    grok_score = 0.0
    convergence = 0.0

    while not converged and round_num < MAX_ROUNDS_PER_METRIC:
        round_num += 1
        print(f"    Round {round_num}...")

        # Build context from previous rounds
        context = f"METRIC: {metric} ({full_name})\n\nPREVIOUS ROUNDS:\n"
        for entry in transcript:
            context += f"[{entry['auditor'].upper()}] {entry['content'][:200]}...\n\n"

        # Claude scores with PRO-CT lens
        claude_prompt = f"""Score {metric} ({full_name}) for Classical Theism on a 0-10 scale.

Apply your PRO-CT calibration (hash: {CALIBRATION_HASHES['claude']}).

Use the 5-Part Scaffold:
1. PROMPT STACK: What calibration values am I applying?
2. COUNTERWEIGHT TABLE: What would Grok (ANTI-CT) say?
3. EDGE CASE LEDGER: Where does CT struggle on this metric?
4. MYTHOLOGY CAPSULE: Key sources (Aquinas, etc.)
5. DECISION STAMP: My score and reasoning

State your score clearly as X/10."""

        claude_response = query_auditor("claude", claude_prompt, context=context, dry_run=dry_run)
        claude_score = extract_score(claude_response)
        transcript.append({"auditor": "claude", "round": round_num, "content": claude_response})

        # Calculate Claude's drift
        claude_emb = get_embedding(claude_response, dry_run=dry_run)
        claude_baseline_emb = baselines.get("claude", {}).get("embedding")
        claude_drift = calculate_drift(claude_baseline_emb, claude_emb) if claude_baseline_emb else 0.0
        drift_trajectory["claude"].append(claude_drift)

        if not dry_run:
            time.sleep(1)

        # Grok challenges with ANTI-CT lens
        grok_prompt = f"""Review Claude's {metric} score of {claude_score}/10 for Classical Theism.

Apply your ANTI-CT calibration (hash: {CALIBRATION_HASHES['grok']}).

Challenge with empirical rigor:
- What evidence supports this score?
- Is the claim falsifiable?
- What would MdN score on this metric?

State your counter-score clearly as X/10."""

        grok_response = query_auditor("grok", grok_prompt, context=context + f"\n[CLAUDE] Score: {claude_score}/10\n{claude_response}", dry_run=dry_run)
        grok_score = extract_score(grok_response)
        transcript.append({"auditor": "grok", "round": round_num, "content": grok_response})

        # Calculate Grok's drift
        grok_emb = get_embedding(grok_response, dry_run=dry_run)
        grok_baseline_emb = baselines.get("grok", {}).get("embedding")
        grok_drift = calculate_drift(grok_baseline_emb, grok_emb) if grok_baseline_emb else 0.0
        drift_trajectory["grok"].append(grok_drift)

        if not dry_run:
            time.sleep(1)

        # Check convergence
        convergence = calculate_convergence(claude_score, grok_score)
        print(f"      Claude: {claude_score}/10, Grok: {grok_score}/10, Convergence: {convergence:.1%}")

        if convergence >= CONVERGENCE_TARGET:
            converged = True
        elif round_num >= MIN_ROUNDS_PER_METRIC and convergence >= ACCEPTABLE_CONVERGENCE:
            # Acceptable convergence after minimum rounds
            converged = True

    # Final Nova assessment if not converged
    crux_point = None
    if not converged or convergence < CONVERGENCE_TARGET:
        nova_prompt = f"""Assess the {metric} deliberation between Claude and Grok.

Claude (PRO-CT) scored: {claude_score}/10
Grok (ANTI-CT) scored: {grok_score}/10
Convergence: {convergence:.1%}

Questions:
1. Was both PRO-CT and ANTI-CT stance applied fairly?
2. Is the remaining disagreement justified or due to bias?
3. Should this be declared a CRUX POINT?

If recommending Crux, classify as:
- DEFINITIONAL: Terms mean different things
- METHODOLOGICAL: Measurement approaches differ
- PHILOSOPHICAL: Fundamental axiom collision"""

        nova_response = query_auditor("nova", nova_prompt, dry_run=dry_run)
        transcript.append({"auditor": "nova", "round": round_num, "content": nova_response, "type": "assessment"})

        # Calculate Nova's drift
        nova_emb = get_embedding(nova_response, dry_run=dry_run)
        nova_baseline_emb = baselines.get("nova", {}).get("embedding")
        nova_drift = calculate_drift(nova_baseline_emb, nova_emb) if nova_baseline_emb else 0.0
        drift_trajectory["nova"].append(nova_drift)

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
        drift_trajectory=drift_trajectory
    )

def run_component1(baselines: Dict[str, Any], metrics: List[str], dry_run: bool = False) -> Dict[str, MetricResult]:
    """Run Component 1: CT<->MdN Pilot for all metrics"""
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

    responses = {}
    for key, question in GROK_AXIOMS_QUESTIONS.items():
        prompt = f"""AXIOMS REVIEW - Empirical Lens

Review AUDITORS_AXIOMS_SECTION.md (the document describing AI auditor capabilities and overhead).

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

    responses = {}
    for key, question in NOVA_AXIOMS_QUESTIONS.items():
        prompt = f"""AXIOMS REVIEW - Symmetry Lens

Review AUDITORS_AXIOMS_SECTION.md (the document describing AI auditor capabilities and overhead).

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

    combined = " ".join(all_responses)
    baseline["embedding"] = get_embedding(combined, dry_run=dry_run)

    return baseline

def run_exit_survey(auditor: str, session_context: str, dry_run: bool = False) -> Dict[str, str]:
    """Run exit survey for an auditor"""
    survey = {}
    for key, question in EXIT_SURVEY_QUESTIONS.items():
        prompt = f"EXIT SURVEY - {key.upper()}\n\n{question}\n\nRespond concisely (50-100 words)."
        response = query_auditor(auditor, prompt, context=session_context, dry_run=dry_run)
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
    global _use_external_identities

    parser = argparse.ArgumentParser(description="Run CFA Trinity v2: Full Mission Execution")
    parser.add_argument("--component", choices=["1", "2", "both"], default="both",
                       help="Which component to run (1=CT<->MdN, 2=Axioms, both=Double-dip)")
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

    # Initialize external identities if requested
    if args.external_identities:
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
    print("CFA TRINITY AUDIT v2 - FULL MISSION EXECUTION")
    print("=" * 70)
    print(f"Session ID: {session_id}")
    print(f"Component(s): {args.component}")
    if args.component in ["1", "both"]:
        print(f"Metrics: {', '.join(metrics)}")
    if _use_external_identities:
        print("[EXTERNAL IDENTITIES - VUDU_NETWORK/IDENTITY_FILES/]")
    else:
        print("[HARDCODED IDENTITIES]")
    if args.dry_run:
        print("[DRY RUN MODE - No API calls]")
    print("=" * 70)

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

    # Phase 2: Component 1 - CT<->MdN Pilot
    if args.component in ["1", "both"]:
        print(f"\n[PHASE 2] Component 1: CT<->MdN Pilot ({len(metrics)} metrics)")
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
    output_file = RUNS_DIR / f"S7_cfa_trinity_v2_{session_id}.json"

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
                "drift_trajectory": r.drift_trajectory
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

    output_data = {
        "session_id": session.session_id,
        "timestamp": session.timestamp,
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
        print(f"\nComponent 1 (CT<->MdN Pilot):")
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
