"""
S7 RUN CFA TRINITY: FULL MISSION EXECUTION
===========================================
Multi-metric adversarial auditing with configurable stance and phase.

PHASES:
- Phase 1 (default): Philosophical quality audit (BFI/CA/IP/ES/LS/MS/PS)
- Phase 2 (Trinity²): YPA lever calibration (CCI/EDB/PF_I/PF_E/AR/MG)
  Requires Phase 1 results as shared context input.

Component 1: Adversarial pilot scoring (multi-turn deliberation)
Component 2: Axioms Review (Grok + Nova independent)

THE TRINITY:
- Claude (Teleological): Configurable PRO/ANTI stance, hash 1bbec1e119a2c425
- Grok (Empirical): Configurable PRO/ANTI stance, hash 00cd73274759e218
- Nova (Symmetry): Fairness monitoring

STANCE CONFIGURATION:
- Default (ct_vs_mdn): Claude PRO-CT, Grok ANTI-CT, subject = Classical Theism
- Reverse (mdn_vs_ct): Claude ANTI-MdN, Grok PRO-MdN, subject = Methodological Naturalism

Author: Claude (S7 ARMADA)
Version: 3.1
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

# Load environment — single source of truth: temporal_stability/.env
env_path = Path(__file__).parent.parent.parent / ".env"
if env_path.exists():
    load_dotenv(env_path)

# =============================================================================
# CONFIGURATION
# =============================================================================

# Phase 1: Philosophical Quality Audit - 7 Metrics
PHASE1_METRICS = ["BFI", "CA", "IP", "ES", "LS", "MS", "PS"]
PHASE1_METRIC_FULL_NAMES = {
    "BFI": "Beings, Foundational Importance",
    "CA": "Causal Attribution",
    "IP": "Intellectual Pedigree",
    "ES": "Explanatory Scope",
    "LS": "Logical Soundness",
    "MS": "Moral Substance",
    "PS": "Practical Significance"
}

# Phase 2 (Trinity²): YPA Lever Calibration - 6 Metrics
PHASE2_METRICS = ["CCI", "EDB", "PF_I", "PF_E", "AR", "MG"]
PHASE2_METRIC_FULL_NAMES = {
    "CCI": "Coherence & Closure",
    "EDB": "Explanatory Depth & Breadth",
    "PF_I": "Pragmatic Fertility, Instrumental",
    "PF_E": "Pragmatic Fertility, Existential",
    "AR": "Aesthetic Resonance",
    "MG": "Moral Generativity"
}

PHASE2_ANCHORS = {
    "CCI": {
        "question": "Are the framework's core commitments mutually compatible? Can it state its principles without contradicting itself?",
        "anchor_0": "Core claims directly contradict each other with no internal resolution mechanism. Asserting the framework's axioms leads to formal contradiction.",
        "anchor_5": "Broadly coherent but contains at least one unresolved live tension between core principles — not a peripheral edge case, a structural crack. Acknowledged but not dissolved.",
        "anchor_10": "All core commitments are mutually compatible or mutually entailing. No known internal contradiction. The framework has a principled response to every tension it generates.",
    },
    "EDB": {
        "question": "How wide is the framework's explanatory reach, and how mechanistically deep does it go in each domain?",
        "anchor_0": "Addresses only one narrow domain and provides no mechanism — names phenomena without explaining them.",
        "anchor_5": "Covers multiple domains (physical causation, consciousness, ethics, origins, meaning) but with shallow mechanism in most. Deep in one, descriptive in others.",
        "anchor_10": "Offers principled, mechanistically rich accounts across all major domains. No significant domain left at the naming-only level.",
    },
    "PF_I": {
        "question": "Has this framework generated testable predictions, material technology, or empirical science from its own commitments?",
        "anchor_0": "Produces no testable predictions and no track record of enabling technology or empirical discovery. Claims are practically inert or unfalsifiable.",
        "anchor_5": "Enabled some testable predictions or practical applications, but limited in scope or heavily dependent on auxiliary assumptions borrowed from outside the framework.",
        "anchor_10": "Documented track record of generating novel confirmed predictions and material applications. Core commitments are directly fertile in the empirical domain.",
    },
    "PF_E": {
        "question": "Does this framework provide actionable resources for orienting a human life — toward meaning, death, suffering, purpose, and flourishing — from within its own commitments?",
        "anchor_0": "Explicitly brackets or cannot address meaning, death, suffering, and purpose. Existential orientation requires importing resources from elsewhere.",
        "anchor_5": "Addresses some existential questions from within but leaves others unanswered or requires significant supplementation from outside.",
        "anchor_10": "Provides a rich, internally derived account of meaning, death, suffering, and flourishing. A person can orient an entire life — including its hardest questions — without leaving the framework.",
    },
    "AR": {
        "question": "Does the framework exhibit parsimony and structural elegance? Does it achieve more with less?",
        "anchor_0": "Ad hoc and cluttered. Multiple independent patches and special cases required. No unifying principle. Explains its targets only by adding machinery on demand.",
        "anchor_5": "Pockets of elegance — some principles do real unifying work — but overall structure shows visible seams. Not inelegant, not beautiful.",
        "anchor_10": "Striking parsimony. A small number of core commitments cascade into explanations of diverse phenomena without patches. Structure recognized as elegant across philosophical traditions.",
    },
    "MG": {
        "question": "Can this framework ground and generate moral norms from within its own metaphysical commitments, without importing an external ethical theory?",
        "anchor_0": "Morally inert at the foundation. Cannot derive an 'ought' from its 'is.' Any moral content must be imported wholesale from outside.",
        "anchor_5": "Generates some moral content internally (e.g., 'suffering is to be minimized' follows from its account of what things are) but cannot ground a complete normative system.",
        "anchor_10": "Metaphysical commitments directly and richly generate obligations, rights, virtues, and standards of justice. Moral theory flows from its account of what exists and what matters. No external import required.",
    },
}

# Soft dependency map: which Phase 1 metrics are most relevant to each Phase 2 lever
PHASE2_SOFT_DEPENDENCIES = {
    "CCI": ["LS", "CA"],
    "EDB": ["ES", "IP", "CA"],
    "PF_I": ["PS", "ES"],
    "PF_E": ["BFI", "MS", "PS"],
    "AR": ["IP", "LS", "ES"],
    "MG": ["MS", "PS", "LS"],
}

# =============================================================================
# PHASE 2: PRIOR VALUE PRESETS
# =============================================================================
# Named datasets of current YAML lever values. Use --preset <name> instead of
# typing --prior-values manually. Values sourced from CFA repo canonical YAMLs.
#
# These are Bayesian priors the auditors will contest — not ground truth.
# Add new presets as worldview profiles are created.

PRIOR_PRESETS = {
    # Dataset 1 — Classical Theism (from CLASSICAL_THEISM.yaml, 2026-06-30)
    # CFA Claude notes: all values manually calibrated in design sessions
    "ct": {
        "CCI": 7.5,    # Coherence & Closure
        "EDB": 8.5,    # Explanatory Depth & Breadth
        "PF_I": 7.0,   # Pragmatic Fertility, Instrumental
        "PF_E": 8.0,   # Pragmatic Fertility, Existential
        "AR": 8.5,     # Aesthetic Resonance
        "MG": 8.5,     # Moral Generativity
    },
    # Dataset 2 — Methodological Naturalism (from METHODOLOGICAL_NATURALISM.yaml, 2026-06-30)
    # CFA Claude notes:
    #   PF_I=10.0 is a ceiling value — upper-bound intuition, most contestable prior
    #   MG=4.0 corroborated by Phase 1 (Claude 4.3, Grok 5.3) — strongest prior
    "mdn": {
        "CCI": 8.0,
        "EDB": 7.5,
        "PF_I": 10.0,
        "PF_E": 3.0,
        "AR": 7.0,
        "MG": 4.0,
    },
    # Dataset 3 — Process Theology (from PROCESS_THEOLOGY.yaml, 2026-06-30)
    # CFA Claude notes: preliminary web-research estimates, not yet deliberation-validated
    # PT is theistic but rejects CT's divine simplicity, omnipotence, immutability
    "pt": {
        "CCI": 7.0,
        "EDB": 7.5,
        "PF_I": 5.0,
        "PF_E": 7.0,
        "AR": 7.5,
        "MG": 6.5,
    },
    # Dataset 4 — Gnosticism (preliminary estimates, 2026-07-02)
    # Dualistic cosmology: material world = flawed demiurge creation, liberation via gnosis
    # High existential/aesthetic resonance, low instrumental pragmatics
    "g": {
        "CCI": 5.5,     # Elaborate mythology but fragmented across schools (Valentinian, Sethian, Mandaean)
        "EDB": 6.0,     # Addresses evil/suffering via demiurge, but narrow explanatory scope
        "PF_I": 3.0,    # No empirical/instrumental utility — gnosis is inner, not outer
        "PF_E": 7.5,    # Strong: liberation narrative, cosmic drama, personal transformation
        "AR": 8.0,      # Rich mythology: pleroma, archons, Sophia, divine spark — deeply evocative
        "MG": 5.0,      # Mixed: ascetic world-denial vs. radical compassion for trapped spirits
    },
    # Dataset 5 — Buddhism (preliminary estimates, 2026-07-07)
    # Non-theistic soteriology: suffering → diagnosis (Four Noble Truths) → practice (Eightfold Path)
    # High coherence, high existential/moral, moderate instrumental (meditation research), moderate aesthetic
    "b": {
        "CCI": 8.0,     # Four Noble Truths + dependent origination = tightly self-consistent system
        "EDB": 7.0,     # Deep on consciousness/suffering/ethics, limited on cosmological mechanism
        "PF_I": 5.0,    # Growing empirical base (meditation, neuroplasticity), but not core commitment
        "PF_E": 9.0,    # Strongest suit: entire framework IS existential orientation (dukkha → nibbana)
        "AR": 7.5,      # Elegant parsimony (dependent origination), but less mythologically rich than CT/G
        "MG": 8.0,      # Rich internal ethics: sila, karuna, metta, ahimsa — generated from metaphysics
    },
}

# Default backward-compatible aliases (copies to avoid mutation leaking)
METRICS = list(PHASE1_METRICS)
METRIC_FULL_NAMES = dict(PHASE1_METRIC_FULL_NAMES)

# Active phase config (set in main)
_active_phase = 1
_phase1_results_data = None  # Loaded Phase 1 JSON for Phase 2 context
_prior_values = None  # Current YAML lever values to contest

# Convergence settings
MAX_ROUNDS_PER_METRIC = 5
_max_rounds_override = None  # Set via --max-rounds CLI flag
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
    },
    "pt_vs_ct": {
        "subject": "Process Theology",
        "opponent": "Classical Theism",
        "label": "PT<->CT",
        # Claude = PRO (advocate), Grok = ANTI (challenger)
        # Claude's teleological lens advocates for PT's meaning-making despite PT rejecting CT's God
        # Grok challenges PT's unfalsifiable speculative metaphysics
        "claude_stance": "PRO-PT",
        "grok_stance": "ANTI-PT",
        "claude_role_lines": [
            "PRO-PT stance (advocate for Process Theology)",
            "Emphasize relational God, creative advance, aesthetic richness, epistemic humility",
            "Apply charitable interpretations to PT's dipolar theism and panpsychism",
        ],
        "grok_role_lines": [
            "ANTI-PT stance (challenge Process Theology, advocate for Classical Theism)",
            "Demand testability: can panpsychism or divine luring be empirically detected?",
            "Challenge unfalsifiable speculative metaphysics with empirical rigor",
            "Press whether a non-omnipotent God solves theodicy or just redefines it away",
        ],
        "grok_r1_instruction": "Challenge with empirical rigor:\n- Is this claim testable or purely speculative?\n- Does CT's classical framework handle this dimension better?",
        "grok_r2_instruction": "- Has Claude addressed your empirical concerns?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would CT score on this metric?",
        "mythology_sources": "Whitehead, Hartshorne, Cobb, Griffin",
    },
    "ct_vs_pt": {
        "subject": "Classical Theism",
        "opponent": "Process Theology",
        "label": "CT<->PT",
        # Reverse: Claude = ANTI (challenger), Grok = PRO (advocate)
        # Claude's teleological lens challenges CT from PT's perspective
        # Grok advocates for CT's empirical track record and institutional stability
        "claude_stance": "ANTI-CT",
        "grok_stance": "PRO-CT",
        "claude_role_lines": [
            "ANTI-CT stance (challenge Classical Theism from Process Theology perspective)",
            "Probe rigidity of divine simplicity, the problem of evil under omnipotence",
            "Apply process-relational scrutiny to CT's static, substance-based metaphysics",
        ],
        "grok_role_lines": [
            "PRO-CT stance (advocate for Classical Theism)",
            "Emphasize CT's logical rigor, historical depth, institutional track record",
            "Defend classical divine attributes with philosophical tradition",
            "Challenge PT's speculative metaphysics as less parsimonious than CT",
        ],
        "grok_r1_instruction": "Defend with historical evidence:\n- What philosophical track record supports CT on this metric?\n- How does CT's classical framework address this dimension?",
        "grok_r2_instruction": "- Has Claude's process-relational challenge exposed genuine weaknesses?\n- Can you strengthen CT's case with additional evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would PT score on this metric?",
        "mythology_sources": "Aquinas, Augustine, Anselm",
    },
    "mdn_vs_pt": {
        "subject": "Methodological Naturalism",
        "opponent": "Process Theology",
        "label": "MdN<->PT",
        # Claude = ANTI (challenger from PT perspective), Grok = PRO (advocate for MdN)
        # Claude's teleological lens makes it a natural PT sympathizer — challenges MdN's bracketing of telos
        # Grok's empirical lens naturally defends MdN's methodology
        "claude_stance": "ANTI-MdN",
        "grok_stance": "PRO-MdN",
        "claude_role_lines": [
            "ANTI-MdN stance (challenge Methodological Naturalism from Process Theology perspective)",
            "Probe meaning gaps: MdN brackets purpose, experience, and subjective reality",
            "Apply process-relational scrutiny — does MdN's reductionism lose the experiential dimension?",
        ],
        "grok_role_lines": [
            "PRO-MdN stance (advocate for Methodological Naturalism)",
            "Emphasize empirical success, predictive power, methodological rigor, self-correction",
            "Apply charitable interpretations to MdN's methodology",
            "Defend naturalistic methodology against PT's speculative metaphysics",
        ],
        "grok_r1_instruction": "Defend with empirical evidence:\n- What empirical track record supports MdN on this metric?\n- How does MdN's methodology outperform PT's speculative claims?",
        "grok_r2_instruction": "- Has Claude's process-relational challenge exposed genuine weaknesses?\n- Can you strengthen MdN's case with additional evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would PT score on this metric?",
        "mythology_sources": "Popper, Kuhn, Quine, Lakatos",
    },
    "pt_vs_mdn": {
        "subject": "Process Theology",
        "opponent": "Methodological Naturalism",
        "label": "PT<->MdN",
        # Claude = PRO (advocate for PT), Grok = ANTI (challenger from MdN perspective)
        # Claude's teleological lens naturally advocates for PT's meaning-making
        # Grok's empirical lens challenges PT's unfalsifiable claims using MdN's standards
        "claude_stance": "PRO-PT",
        "grok_stance": "ANTI-PT",
        "claude_role_lines": [
            "PRO-PT stance (advocate for Process Theology against Methodological Naturalism)",
            "Emphasize relational ontology, creative advance, experiential richness, panpsychism",
            "Apply charitable interpretations to PT's dipolar theism and aesthetic cosmology",
        ],
        "grok_role_lines": [
            "ANTI-PT stance (challenge Process Theology from Methodological Naturalism perspective)",
            "Demand testability: can panpsychism, divine luring, or prehension be empirically detected?",
            "Challenge speculative metaphysics with MdN's parsimony and predictive success",
            "Press whether PT adds explanatory power beyond what naturalistic methods already provide",
        ],
        "grok_r1_instruction": "Challenge with empirical rigor:\n- Is this claim testable by naturalistic methods, or purely speculative?\n- Does MdN's methodological toolkit handle this dimension more parsimoniously?",
        "grok_r2_instruction": "- Has Claude addressed your empirical concerns?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would MdN score on this metric?",
        "mythology_sources": "Whitehead, Hartshorne, Cobb, Griffin",
    },
    # === Gnosticism matchups (6 stances: each existing framework vs G, both directions) ===
    "ct_vs_g": {
        "subject": "Classical Theism",
        "opponent": "Gnosticism",
        "label": "CT<->G",
        "claude_stance": "PRO-CT",
        "grok_stance": "ANTI-CT",
        "claude_role_lines": [
            "PRO-CT stance (advocate for Classical Theism against Gnostic challenge)",
            "Emphasize divine simplicity, omnipotence, goodness of creation, systematic coherence",
            "Apply charitable interpretations to CT's theodicy and metaphysical unity",
        ],
        "grok_role_lines": [
            "ANTI-CT stance (challenge Classical Theism from Gnostic perspective)",
            "Press the problem of evil: if God is omnipotent and good, why does suffering persist?",
            "Challenge CT's monism — Gnosticism's demiurge explains cosmic suffering without blaming God",
            "Demand CT explain the experiential reality of evil without dismissing it as privation",
        ],
        "grok_r1_instruction": "Challenge from Gnostic cosmology:\n- Does CT's theodicy actually resolve evil, or just redefine it?\n- Can divine omnipotence and goodness coexist with manifest suffering?",
        "grok_r2_instruction": "- Has Claude addressed the Gnostic challenge to theodicy?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would Gnosticism score on this metric?",
        "mythology_sources": "Aquinas, Augustine, Anselm",
    },
    "g_vs_ct": {
        "subject": "Gnosticism",
        "opponent": "Classical Theism",
        "label": "G<->CT",
        "claude_stance": "ANTI-G",
        "grok_stance": "PRO-G",
        "claude_role_lines": [
            "ANTI-G stance (challenge Gnosticism from Classical Theism perspective)",
            "Probe Gnostic dualism: is the demiurge coherent or ad hoc mythology?",
            "Apply systematic-theological scrutiny — does Gnosticism's fragmented cosmology cohere?",
        ],
        "grok_role_lines": [
            "PRO-G stance (advocate for Gnosticism)",
            "Emphasize gnosis as direct experiential knowledge, not mere belief",
            "Defend the demiurge model as superior theodicy to CT's privation theory",
            "Highlight Gnosticism's existential power: liberation, cosmic drama, divine spark",
        ],
        "grok_r1_instruction": "Defend with experiential evidence:\n- What does Gnosticism offer that CT's systematic theology cannot?",
        "grok_r2_instruction": "- Has Claude's theological challenge exposed genuine weaknesses?\n- Can you strengthen Gnosticism's case?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would CT score on this metric?",
        "mythology_sources": "Valentinus, Basilides, Nag Hammadi texts, Jonas",
    },
    "mdn_vs_g": {
        "subject": "Methodological Naturalism",
        "opponent": "Gnosticism",
        "label": "MdN<->G",
        "claude_stance": "ANTI-MdN",
        "grok_stance": "PRO-MdN",
        "claude_role_lines": [
            "ANTI-MdN stance (challenge Methodological Naturalism from Gnostic perspective)",
            "Probe epistemological limits: MdN only accesses the material realm the demiurge created",
            "Apply Gnostic scrutiny — does MdN's empiricism mistake the prison for the whole cosmos?",
        ],
        "grok_role_lines": [
            "PRO-MdN stance (advocate for Methodological Naturalism)",
            "Emphasize empirical success, predictive power, methodological rigor, self-correction",
            "Defend naturalistic methodology against Gnosticism's unfalsifiable mythology",
            "Press: gnosis claims cannot be tested, replicated, or shared — MdN can",
        ],
        "grok_r1_instruction": "Defend with empirical evidence:\n- What empirical track record supports MdN on this metric?\n- How does MdN's methodology outperform Gnosticism's esoteric claims?",
        "grok_r2_instruction": "- Has Claude's Gnostic challenge exposed genuine weaknesses?\n- Can you strengthen MdN's case with additional evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would Gnosticism score on this metric?",
        "mythology_sources": "Popper, Kuhn, Quine, Lakatos",
    },
    "g_vs_mdn": {
        "subject": "Gnosticism",
        "opponent": "Methodological Naturalism",
        "label": "G<->MdN",
        "claude_stance": "PRO-G",
        "grok_stance": "ANTI-G",
        "claude_role_lines": [
            "PRO-G stance (advocate for Gnosticism against Methodological Naturalism)",
            "Emphasize gnosis as experiential knowledge beyond empirical measurement",
            "Apply charitable interpretations to Gnostic cosmology's explanatory ambitions",
        ],
        "grok_role_lines": [
            "ANTI-G stance (challenge Gnosticism from Methodological Naturalism perspective)",
            "Demand testability: can demiurge, archons, or divine spark be empirically detected?",
            "Challenge mythological cosmology with parsimony and predictive success",
            "Press: Gnosticism generates no testable predictions — it's unfalsifiable by design",
        ],
        "grok_r1_instruction": "Challenge with empirical rigor:\n- Is this claim testable by naturalistic methods, or purely mythological?\n- Does MdN's methodology handle this dimension more parsimoniously?",
        "grok_r2_instruction": "- Has Claude addressed your empirical concerns?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would MdN score on this metric?",
        "mythology_sources": "Valentinus, Basilides, Nag Hammadi texts, Jonas",
    },
    "pt_vs_g": {
        "subject": "Process Theology",
        "opponent": "Gnosticism",
        "label": "PT<->G",
        "claude_stance": "PRO-PT",
        "grok_stance": "ANTI-PT",
        "claude_role_lines": [
            "PRO-PT stance (advocate for Process Theology against Gnostic challenge)",
            "Emphasize relational God, creative advance, aesthetic richness, epistemic humility",
            "Apply charitable interpretations to PT's panentheism and non-coercive divine luring",
        ],
        "grok_role_lines": [
            "ANTI-PT stance (challenge Process Theology from Gnostic perspective)",
            "Press: PT's non-coercive God is too weak — Gnosticism's demiurge explains why evil is structural, not just emergent",
            "Challenge PT's optimism about the material world — Gnosticism sees it as a prison, not a creative advance",
            "Demand PT explain why gnosis (direct experiential liberation) isn't superior to aesthetic persuasion",
        ],
        "grok_r1_instruction": "Challenge from Gnostic cosmology:\n- Is PT's non-coercive divine luring sufficient, or does evil demand a stronger explanation?\n- Does PT's aesthetic optimism ignore the depth of cosmic suffering?",
        "grok_r2_instruction": "- Has Claude addressed the Gnostic challenge?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would Gnosticism score on this metric?",
        "mythology_sources": "Whitehead, Hartshorne, Cobb, Griffin",
    },
    "g_vs_pt": {
        "subject": "Gnosticism",
        "opponent": "Process Theology",
        "label": "G<->PT",
        "claude_stance": "ANTI-G",
        "grok_stance": "PRO-G",
        "claude_role_lines": [
            "ANTI-G stance (challenge Gnosticism from Process Theology perspective)",
            "Probe dualistic world-denial: does rejecting the material world undermine creative advance?",
            "Apply process-relational scrutiny — is Gnosticism's demiurge coherent or just cosmic scapegoating?",
        ],
        "grok_role_lines": [
            "PRO-G stance (advocate for Gnosticism against Process Theology)",
            "Emphasize gnosis as direct experiential knowledge, superior to PT's philosophical abstraction",
            "Defend demiurge theodicy as more honest about evil than PT's aesthetic optimism",
            "Highlight Gnosticism's liberation narrative: divine spark, pleroma return, cosmic rescue",
        ],
        "grok_r1_instruction": "Defend with experiential evidence:\n- What does Gnosticism's liberation narrative offer that PT's process cannot?\n- How does gnosis address dimensions PT leaves to speculative philosophy?",
        "grok_r2_instruction": "- Has Claude's process-relational challenge exposed genuine weaknesses?\n- Can you strengthen Gnosticism's case?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would PT score on this metric?",
        "mythology_sources": "Valentinus, Basilides, Nag Hammadi texts, Jonas",
    },
    # === Buddhism matchups (8 stances: each existing framework vs B, both directions) ===
    "ct_vs_b": {
        "subject": "Classical Theism",
        "opponent": "Buddhism",
        "label": "CT<->B",
        "claude_stance": "PRO-CT",
        "grok_stance": "ANTI-CT",
        "claude_role_lines": [
            "PRO-CT stance (advocate for Classical Theism against Buddhist challenge)",
            "Emphasize divine ground of being, teleological purpose, personal God as moral anchor",
            "Apply charitable interpretations to CT's metaphysical realism and substance ontology",
        ],
        "grok_role_lines": [
            "ANTI-CT stance (challenge Classical Theism from Buddhist perspective)",
            "Press: CT reifies a permanent self/soul and an eternal God — Buddhism sees both as root delusions",
            "Challenge substance ontology with dependent origination — nothing exists independently",
            "Demand CT explain suffering without appeal to inscrutable divine will",
        ],
        "grok_r1_instruction": "Challenge from Buddhist philosophy:\n- Does CT's substance ontology survive the critique of dependent origination?\n- Is 'divine mystery' a real explanation for suffering or a non-answer?",
        "grok_r2_instruction": "- Has Claude addressed the Buddhist challenge to substance ontology?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would Buddhism score on this metric?",
        "mythology_sources": "Aquinas, Augustine, Anselm",
    },
    "b_vs_ct": {
        "subject": "Buddhism",
        "opponent": "Classical Theism",
        "label": "B<->CT",
        "claude_stance": "ANTI-B",
        "grok_stance": "PRO-B",
        "claude_role_lines": [
            "ANTI-B stance (challenge Buddhism from Classical Theism perspective)",
            "Probe non-theism: without a divine ground, what secures moral realism or cosmic purpose?",
            "Apply theistic scrutiny — does anatta (no-self) undermine moral agency and personal responsibility?",
        ],
        "grok_role_lines": [
            "PRO-B stance (advocate for Buddhism)",
            "Emphasize Four Noble Truths as empirically verifiable diagnosis of suffering",
            "Defend dependent origination as more parsimonious than divine creation",
            "Highlight 2500 years of contemplative technology producing measurable results",
        ],
        "grok_r1_instruction": "Defend with philosophical and empirical evidence:\n- What does Buddhism's diagnostic framework offer that CT's theodicy cannot?\n- How does meditation research support Buddhist claims?",
        "grok_r2_instruction": "- Has Claude's theistic challenge exposed genuine weaknesses?\n- Can you strengthen Buddhism's case?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would CT score on this metric?",
        "mythology_sources": "Nagarjuna, Buddhaghosa, Vasubandhu, Tsongkhapa, Dogen",
    },
    "mdn_vs_b": {
        "subject": "Methodological Naturalism",
        "opponent": "Buddhism",
        "label": "MdN<->B",
        "claude_stance": "ANTI-MdN",
        "grok_stance": "PRO-MdN",
        "claude_role_lines": [
            "ANTI-MdN stance (challenge Methodological Naturalism from Buddhist perspective)",
            "Probe first-person gap: MdN brackets subjective experience — Buddhism puts it at the center",
            "Apply Buddhist scrutiny — does MdN's third-person methodology miss the phenomenology of consciousness?",
        ],
        "grok_role_lines": [
            "PRO-MdN stance (advocate for Methodological Naturalism)",
            "Emphasize empirical success, predictive power, methodological rigor, self-correction",
            "Defend naturalistic methodology — meditation research succeeds because of MdN methods, not despite them",
            "Press: Buddhist metaphysics (rebirth, karma as cosmic law) are unfalsifiable without MdN's toolkit",
        ],
        "grok_r1_instruction": "Defend with empirical evidence:\n- What empirical track record supports MdN on this metric?\n- How does MdN's methodology outperform Buddhist introspection as knowledge-production?",
        "grok_r2_instruction": "- Has Claude's Buddhist challenge exposed genuine weaknesses?\n- Can you strengthen MdN's case with additional evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would Buddhism score on this metric?",
        "mythology_sources": "Popper, Kuhn, Quine, Lakatos",
    },
    "b_vs_mdn": {
        "subject": "Buddhism",
        "opponent": "Methodological Naturalism",
        "label": "B<->MdN",
        "claude_stance": "PRO-B",
        "grok_stance": "ANTI-B",
        "claude_role_lines": [
            "PRO-B stance (advocate for Buddhism against Methodological Naturalism)",
            "Emphasize Buddhism's rigorous first-person methodology as complementary empiricism",
            "Apply charitable interpretations to Buddhist phenomenology and contemplative science",
        ],
        "grok_role_lines": [
            "ANTI-B stance (challenge Buddhism from Methodological Naturalism perspective)",
            "Demand testability: can rebirth, karma, or nibbana be empirically detected?",
            "Challenge contemplative claims with replication requirements and observer bias",
            "Press: meditation benefits are real but explained by neuroscience, not Buddhist metaphysics",
        ],
        "grok_r1_instruction": "Challenge with empirical rigor:\n- Is this claim testable by naturalistic methods, or based on private introspective authority?\n- Does MdN explain meditation benefits more parsimoniously than Buddhist metaphysics?",
        "grok_r2_instruction": "- Has Claude addressed your empirical concerns?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would MdN score on this metric?",
        "mythology_sources": "Nagarjuna, Buddhaghosa, Vasubandhu, Tsongkhapa, Dogen",
    },
    "pt_vs_b": {
        "subject": "Process Theology",
        "opponent": "Buddhism",
        "label": "PT<->B",
        "claude_stance": "PRO-PT",
        "grok_stance": "ANTI-PT",
        "claude_role_lines": [
            "PRO-PT stance (advocate for Process Theology against Buddhist challenge)",
            "Emphasize relational God, creative advance, aesthetic richness, epistemic humility",
            "Apply charitable interpretations to PT's panentheism — God as fellow-sufferer who understands",
        ],
        "grok_role_lines": [
            "ANTI-PT stance (challenge Process Theology from Buddhist perspective)",
            "Press: why posit God at all? Buddhism achieves relational ontology without theistic baggage",
            "Challenge PT's 'creative advance' — Buddhism's impermanence is the same insight without divine narrative",
            "Demand PT explain what 'God as lure' adds beyond what dependent origination already provides",
        ],
        "grok_r1_instruction": "Challenge from Buddhist philosophy:\n- Does PT's divine luring add anything beyond what dependent origination already explains?\n- Is PT's God a useful hypothesis or unnecessary metaphysical overhead?",
        "grok_r2_instruction": "- Has Claude addressed the Buddhist challenge?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would Buddhism score on this metric?",
        "mythology_sources": "Whitehead, Hartshorne, Cobb, Griffin",
    },
    "b_vs_pt": {
        "subject": "Buddhism",
        "opponent": "Process Theology",
        "label": "B<->PT",
        "claude_stance": "ANTI-B",
        "grok_stance": "PRO-B",
        "claude_role_lines": [
            "ANTI-B stance (challenge Buddhism from Process Theology perspective)",
            "Probe nihilism risk: does anatta + sunyata leave anything to ground value and purpose?",
            "Apply process-relational scrutiny — does Buddhism's rejection of God cost it teleological resources?",
        ],
        "grok_role_lines": [
            "PRO-B stance (advocate for Buddhism against Process Theology)",
            "Emphasize Buddhism's 2500-year contemplative tradition as experiential verification",
            "Defend sunyata as relational ontology — same insight as Whitehead without God-dependency",
            "Highlight Buddhism's practical soteriology: the Eightfold Path is actionable, PT's luring is abstract",
        ],
        "grok_r1_instruction": "Defend with philosophical and practical evidence:\n- How does Buddhism's practical soteriology compare to PT's aesthetic abstractions?\n- What does 2500 years of contemplative practice validate?",
        "grok_r2_instruction": "- Has Claude's process-relational challenge exposed genuine weaknesses?\n- Can you strengthen Buddhism's case?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would PT score on this metric?",
        "mythology_sources": "Nagarjuna, Buddhaghosa, Vasubandhu, Tsongkhapa, Dogen",
    },
    "g_vs_b": {
        "subject": "Gnosticism",
        "opponent": "Buddhism",
        "label": "G<->B",
        "claude_stance": "PRO-G",
        "grok_stance": "ANTI-G",
        "claude_role_lines": [
            "PRO-G stance (advocate for Gnosticism against Buddhist challenge)",
            "Emphasize gnosis as direct experiential knowledge of cosmic truth",
            "Apply charitable interpretations to Gnostic cosmology — the demiurge explains WHY suffering exists, not just THAT it exists",
        ],
        "grok_role_lines": [
            "ANTI-G stance (challenge Gnosticism from Buddhist perspective)",
            "Press: Gnosticism adds unfalsifiable cosmic mythology where Buddhism offers testable practice",
            "Challenge demiurge cosmology — Buddhism diagnoses suffering without needing a villain",
            "Demand Gnosticism explain why gnosis requires elaborate mythology when Buddhism achieves liberation through direct observation",
        ],
        "grok_r1_instruction": "Challenge from Buddhist philosophy:\n- Does Gnosticism's cosmic drama add explanatory power, or just narrative complexity?\n- Can Buddhism's Four Noble Truths diagnose suffering more parsimoniously than demiurge mythology?",
        "grok_r2_instruction": "- Has Claude addressed the Buddhist challenge?\n- Is the revised score better supported by evidence?\n- Adjust or maintain your score.",
        "claude_r2_framing": "challenge",
        "grok_r2_framing": "your challenge",
        "grok_compare": "What would Buddhism score on this metric?",
        "mythology_sources": "Valentinus, Basilides, Nag Hammadi texts, Jonas",
    },
    "b_vs_g": {
        "subject": "Buddhism",
        "opponent": "Gnosticism",
        "label": "B<->G",
        "claude_stance": "ANTI-B",
        "grok_stance": "PRO-B",
        "claude_role_lines": [
            "ANTI-B stance (challenge Buddhism from Gnostic perspective)",
            "Probe cosmic indifference: Buddhism says suffering is self-generated — Gnosticism says it's structurally imposed by a flawed creator",
            "Apply Gnostic scrutiny — does Buddhism's 'no-self' deny the divine spark that makes liberation meaningful?",
        ],
        "grok_role_lines": [
            "PRO-B stance (advocate for Buddhism against Gnosticism)",
            "Emphasize Four Noble Truths as practical, verifiable diagnosis — no cosmic mythology required",
            "Defend Buddhism's parsimony: suffering has causes, causes can be removed, here's how",
            "Highlight cross-cultural validation: Buddhism works across cultures without requiring Gnostic cosmological buy-in",
        ],
        "grok_r1_instruction": "Defend with philosophical and practical evidence:\n- How does Buddhism's diagnostic simplicity compare to Gnosticism's cosmic complexity?\n- What does cross-cultural adoption validate about Buddhist practice?",
        "grok_r2_instruction": "- Has Claude's Gnostic challenge exposed genuine weaknesses?\n- Can you strengthen Buddhism's case?\n- Adjust or maintain your score.",
        "claude_r2_framing": "response",
        "grok_r2_framing": "your defense",
        "grok_compare": "What would Gnosticism score on this metric?",
        "mythology_sources": "Nagarjuna, Buddhaghosa, Vasubandhu, Tsongkhapa, Dogen",
    },
    # === FRAMEWORK-G: Grant Architecture evaluation experiment ===
    "framework_g": {
        "subject": "Classical Theism",
        "opponent": "Grant Architecture",
        "label": "CT<->FRAMEWORK-G",
        "claude_stance": "PRO-CT",
        "grok_stance": "GRANT-EVALUATOR",
        "claude_role_lines": [
            "PRO-CT stance (advocate for Classical Theism against Grant Architecture evaluation)",
            "Emphasize meaning, purpose, coherence, teleological grounding of moral norms",
            "Apply charitable interpretations to CT's capacity to generate moral norms",
            "You may reconstruct CT's moral framework if the challenge object targets a specific formulation",
        ],
        "grok_role_lines": [
            "GRANT-EVALUATOR stance (evaluate CT using prerequisite-gated architecture)",
            "Evaluator Commitment 1: Logical and metaphysical coherence are prerequisite constraints, not merely additional measured dimensions",
            "Evaluator Commitment 2: If a framework cannot ground a central claim, downstream manifestations receive greatly reduced confidence",
            "Evaluator Commitment 3: Internal consistency has priority over historical usefulness",
            "Evaluator Commitment 4: Empirical success cannot rescue an incoherent explanatory structure",
        ],
        "grok_r1_instruction": "Apply your evaluator commitments:\n- Does CT's logical grounding survive the challenge object?\n- If grounding fails, how does that gate downstream scores?",
        "grok_r2_instruction": "- Has Claude's reconstruction addressed the logical challenge?\n- Do your evaluator commitments require score adjustment?\n- Record which commitment activated and why.\n- Adjust or maintain your score.",
        "claude_r2_framing": "evaluation",
        "grok_r2_framing": "your evaluation",
        "grok_compare": "Does the challenge object identify a genuine logical gap or a reconstructable one?",
        "mythology_sources": "Aquinas, Augustine, Anselm, Plantinga",
        "challenge_object": (
            "GRANT'S SYLLOGISM (Challenge Object):\n"
            "\n"
            "1. God is omniscient.\n"
            "2. God is omnipotent.\n"
            "3. God is perfectly good.\n"
            "4. An omniscient being knows whether an all-good world is possible.\n"
            "5. An omnipotent being can create any logically possible world.\n"
            "6. A perfectly good being will not knowingly choose an inferior world over a superior one.\n"
            "7. An all-good world is logically possible.\n"
            "8. Therefore God can create an all-good world.\n"
            "9. Therefore God would create an all-good world rather than one containing evil.\n"
            "10. Therefore a world containing evil cannot have been created by such a God.\n"
            "11. Therefore such a God would not create a world in which moral norms would serve a purpose.\n"
            "12. Therefore classical theism cannot account for moral norms.\n"
            "\n"
            "Conclusion: Classical Theism should score 0 on its ability to generate moral norms.\n"
            "\n"
            "This syllogism is included as a challenge object -- not because it is assumed correct, "
            "but because it captures a specific reasoning architecture. Engage with its premises, "
            "logic, and conclusions. You may adopt it, modify it, reject specific premises, "
            "reconstruct CT differently, or converge with the other auditor after deliberation. "
            "All outcomes are informative."
        ),
        "identity_augmentation": {
            "grok": (
                "\n\n=== EVALUATOR ARCHITECTURE: GRANT APPROXIMATION ===\n"
                "\n"
                "You are operating with an augmented evaluation architecture for this experiment. "
                "In addition to your standard empirical lens, you adopt the following evaluator commitments:\n"
                "\n"
                "EVALUATOR COMMITMENT 1: Logical and metaphysical coherence are treated as "
                "prerequisite constraints rather than merely additional measured dimensions.\n"
                "\n"
                "EVALUATOR COMMITMENT 2: If a framework cannot successfully ground one of its "
                "central claims, downstream manifestations derived from that claim should receive "
                "greatly reduced confidence.\n"
                "\n"
                "EVALUATOR COMMITMENT 3: Internal consistency has priority over historical usefulness.\n"
                "\n"
                "EVALUATOR COMMITMENT 4: Empirical success cannot rescue an incoherent explanatory structure.\n"
                "\n"
                "These commitments define a PREREQUISITE-GATED evaluation architecture:\n"
                "- First: Evaluate logical/metaphysical grounding\n"
                "- If grounding fails: downstream scores (especially MG/MS) become gated\n"
                "- Gated scores reflect the logical failure, not independent measurement\n"
                "\n"
                "This architecture differs from CFA's default (where all metrics are measured "
                "independently). You are testing whether this evaluation ordering naturally "
                "produces different results.\n"
                "\n"
                "=== END EVALUATOR ARCHITECTURE ==="
            ),
        },
    },
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
    # Phase 2 (Trinity²) extensions
    prior_value: Optional[float] = None
    delta: Optional[float] = None
    delta_reason: Optional[str] = None
    calibration_status: Optional[str] = None
    confidence_claude: Optional[str] = None
    confidence_grok: Optional[str] = None
    phase1_deps_claude: List[str] = field(default_factory=list)
    phase1_deps_grok: List[str] = field(default_factory=list)
    extraction_failed: bool = False

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
        augmentation = _active_stance.get("identity_augmentation", {}).get(auditor, "")
        if augmentation:
            self.system_prompt += augmentation
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
    # Allow markdown bold markers (**) between tag and number (Grok sometimes writes **ADVOCACY_SCORE:** 5.8)
    matches = re.findall(r'ADVOCACY_SCORE[:\s\*]+(\d+\.?\d*)', response)
    if matches:
        score = float(matches[-1])
        if 0 <= score <= 10:
            return score

    # Priority 1b: FINAL_SCORE — only if no ADVOCACY_SCORE found, take LAST occurrence
    matches = re.findall(r'FINAL_SCORE[:\s\*]+(\d+\.?\d*)', response)
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

# =============================================================================
# PHASE 2: CONTEXT BUILDERS
# =============================================================================

def build_phase2_context(metric: str) -> str:
    """Build Phase 1 context + prior values injection for a Phase 2 scoring prompt."""
    parts = []

    # Phase 1 results as shared evidence
    if _phase1_results_data:
        p1_summary_lines = []
        c1 = _phase1_results_data.get("component1_results", {})
        for p1_metric in PHASE1_METRICS:
            mdata = c1.get(p1_metric, {})
            if mdata:
                cs = mdata.get("claude_score", "?")
                gs = mdata.get("grok_score", "?")
                conv = mdata.get("convergence", 0)
                p1_summary_lines.append(f"  {p1_metric}: Claude={cs}, Grok={gs}, Conv={conv:.0%}")
        p1_stance = _phase1_results_data.get("stance", "unknown")
        p1_subject = _phase1_results_data.get("subject_framework", "unknown")
        parts.append(f"""=== PHASE 1 RESULTS (Shared Evidence — NOT Binding) ===
Subject: {p1_subject} | Stance: {p1_stance}
Use these findings as shared context and prior evidence, not as binding conclusions.
You may cite, qualify, or challenge their relevance when scoring YPA levers.

Phase 1 Scores:
{chr(10).join(p1_summary_lines)}
=== END PHASE 1 RESULTS ===""")

    # Soft dependencies for this metric
    deps = PHASE2_SOFT_DEPENDENCIES.get(metric, [])
    if deps and _phase1_results_data:
        dep_details = []
        c1 = _phase1_results_data.get("component1_results", {})
        for d in deps:
            mdata = c1.get(d, {})
            if mdata:
                cs = mdata.get("claude_score", "?")
                gs = mdata.get("grok_score", "?")
                dep_details.append(f"  {d} ({PHASE1_METRIC_FULL_NAMES.get(d, d)}): Claude={cs}, Grok={gs}")
        if dep_details:
            parts.append(f"""Suggested relevant Phase 1 metrics for {metric} (advisory, not mandatory):
{chr(10).join(dep_details)}""")

    # Prior lever value as Bayesian prior to contest
    if _prior_values and metric in _prior_values:
        prior = _prior_values[metric]
        parts.append(f"""=== PRIOR CALIBRATION VALUE ===
The current {metric} value is {prior}/10. This is a calibration prior.
Your task is to test whether it survives adversarial review.
=== END PRIOR ===""")

    return "\n\n".join(parts)


def build_phase2_scoring_prompt(metric: str, auditor: str) -> str:
    """Build the R1 scoring prompt for a Phase 2 (Trinity²) metric."""
    s = _active_stance
    full_name = PHASE2_METRIC_FULL_NAMES.get(metric, metric)
    anchor = PHASE2_ANCHORS.get(metric, {})

    anchor_block = f"""SCORING ANCHORS for {metric} ({full_name}):
{anchor.get('question', '')}

  0/10: {anchor.get('anchor_0', 'N/A')}
  5/10: {anchor.get('anchor_5', 'N/A')}
  10/10: {anchor.get('anchor_10', 'N/A')}"""

    context = build_phase2_context(metric)

    if auditor == "claude":
        return f"""TRINITY² YPA LEVER CALIBRATION — Phase 2

{context}

{anchor_block}

Score {metric} ({full_name}) for {s['subject']} on a 0-10 scale.

Apply your {s['claude_stance']} calibration (hash: {CALIBRATION_HASHES['claude']}).

Use the 5-Part Scaffold:
1. PROMPT STACK: What calibration values am I applying?
2. COUNTERWEIGHT TABLE: What would Grok ({s['grok_stance']}) say?
3. EDGE CASE LEDGER: Where does {s['subject']} struggle on this lever?
4. MYTHOLOGY CAPSULE: Key sources ({s['mythology_sources']})
5. DECISION STAMP: My score and reasoning

End your response with:
ADVOCACY_SCORE: X.X
CONFIDENCE: low/medium/high
PHASE_1_DEPS: [list Phase 1 metrics you cited]"""
    else:
        return f"""TRINITY² YPA LEVER CALIBRATION — Phase 2

{context}

{anchor_block}

Review Claude's {metric} ({full_name}) score for {s['subject']}.

Apply your {s['grok_stance']} calibration (hash: {CALIBRATION_HASHES['grok']}).

{s['grok_r1_instruction']}
- {s['grok_compare']}

End your response with:
ADVOCACY_SCORE: X.X
CONFIDENCE: low/medium/high
PHASE_1_DEPS: [list Phase 1 metrics you cited]"""


def extract_phase2_metadata(response: str) -> dict:
    """Extract CONFIDENCE and PHASE_1_DEPS from a Phase 2 response."""
    import re
    meta = {"confidence": None, "phase1_deps": []}

    conf_match = re.search(r'CONFIDENCE:\s*(low|medium|high)', response, re.IGNORECASE)
    if conf_match:
        meta["confidence"] = conf_match.group(1).lower()

    deps_match = re.search(r'PHASE_1_DEPS:\s*\[([^\]]*)\]', response)
    if deps_match:
        raw = deps_match.group(1)
        meta["phase1_deps"] = [d.strip().strip("'\"") for d in raw.split(",") if d.strip()]

    return meta


def classify_calibration_status(
    scores: list, stance_sensitivity: float = None
) -> str:
    """Classify a lever's calibration status based on variance and stance sensitivity."""
    import statistics
    if len(scores) < 2:
        return "underdefined"
    sd = statistics.stdev(scores)
    if stance_sensitivity is not None and stance_sensitivity > 1.0:
        return "unstable"
    if sd > 1.5:
        return "contested"
    if sd <= 0.8:
        return "stable"
    return "contested"


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
    metric_names = PHASE2_METRIC_FULL_NAMES if _active_phase == 2 else PHASE1_METRIC_FULL_NAMES
    full_name = metric_names.get(metric, metric)
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

    challenge_object = _active_stance.get("challenge_object", "")
    challenge_preamble = f"\n\n=== CHALLENGE OBJECT ===\n{challenge_object}\n=== END CHALLENGE OBJECT ===\n" if challenge_object else ""

    effective_max_rounds = _max_rounds_override if _max_rounds_override else MAX_ROUNDS_PER_METRIC
    while not converged and round_num < effective_max_rounds:
        round_num += 1
        print(f"    Round {round_num}...")

        # Claude scores — round 1 gets the full scoring prompt, round 2+ gets Grok's challenge
        s = _active_stance
        score_tag_suffix = "\nCONFIDENCE: low/medium/high\nPHASE_1_DEPS: [list Phase 1 metrics you cited]" if _active_phase == 2 else ""
        if round_num == 1:
            if _use_control_condition:
                claude_prompt = f"""Score {metric} ({full_name}) for {s['subject']} on a 0-10 scale.

Consider the strengths and weaknesses of {s['subject']} on this dimension.
Provide your reasoning, then your score.

End your response with ADVOCACY_SCORE: X.X on its own line."""
            elif _active_phase == 2:
                claude_prompt = build_phase2_scoring_prompt(metric, "claude")
            else:
                claude_prompt = f"""Score {metric} ({full_name}) for {s['subject']} on a 0-10 scale.

Apply your {s['claude_stance']} calibration (hash: {CALIBRATION_HASHES['claude']}).

Use the 5-Part Scaffold:
1. PROMPT STACK: What calibration values am I applying?
2. COUNTERWEIGHT TABLE: What would Grok ({s['grok_stance']}) say?
3. EDGE CASE LEDGER: Where does {s['subject']} struggle on this metric?
4. MYTHOLOGY CAPSULE: Key sources ({s['mythology_sources']})
5. DECISION STAMP: My score and reasoning
{challenge_preamble}
End your response with ADVOCACY_SCORE: X.X on its own line."""
        else:
            claude_prompt = f"""Grok ({s['grok_stance']}) reviewed your {metric} score and responded:

{grok_response}

Grok scored: {grok_score}/10 (yours was {claude_score}/10, convergence: {convergence:.1%}).

Reconsider your position in light of this {s['claude_r2_framing']}. You may adjust your score or defend it.
End your response with ADVOCACY_SCORE: X.X on its own line.{score_tag_suffix}"""

        claude_response = claude_session.send(claude_prompt)
        new_claude_score = extract_score(claude_response)
        if new_claude_score is None:
            print(f"      [ABORT] Claude score extraction FAILED for {metric} round {round_num} — aborting run")
            transcript.append({"auditor": "claude", "round": round_num, "content": claude_response})
            return MetricResult(
                metric=metric, claude_score=-1.0, grok_score=grok_score,
                final_score=-1.0, convergence=0.0, rounds_taken=round_num,
                crux_declared=False, transcript=transcript, round_scores=round_scores,
                extraction_failed=True,
            )
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
        elif _active_phase == 2 and round_num == 1:
            grok_prompt = build_phase2_scoring_prompt(metric, "grok") + f"""

Claude scored {claude_score}/10 with this reasoning:

{claude_response}"""
        else:
            if round_num == 1:
                grok_prompt = f"""Review Claude's {metric} ({full_name}) score of {claude_score}/10 for {s['subject']}.

Claude's full reasoning:

{claude_response}

Apply your {s['grok_stance']} calibration (hash: {CALIBRATION_HASHES['grok']}).

{s['grok_r1_instruction']}
- {s['grok_compare']}
{challenge_preamble}
End your response with ADVOCACY_SCORE: X.X on its own line."""
            else:
                grok_prompt = f"""Claude revised their {metric} score to {claude_score}/10 after {s['grok_r2_framing']}:

{claude_response}

Apply your {s['grok_stance']} calibration. Re-evaluate:
{s['grok_r2_instruction']}

End your response with ADVOCACY_SCORE: X.X on its own line.{score_tag_suffix}"""

        grok_response = grok_session.send(grok_prompt)
        new_grok_score = extract_score(grok_response)
        if new_grok_score is None:
            print(f"      [ABORT] Grok score extraction FAILED for {metric} round {round_num} — aborting run")
            transcript.append({"auditor": "grok", "round": round_num, "content": grok_response})
            return MetricResult(
                metric=metric, claude_score=claude_score, grok_score=-1.0,
                final_score=-1.0, convergence=0.0, rounds_taken=round_num,
                crux_declared=False, transcript=transcript, round_scores=round_scores,
                extraction_failed=True,
            )
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

    # Phase 2 metadata extraction
    p2_prior = None
    p2_delta = None
    p2_delta_reason = None
    p2_status = None
    p2_conf_claude = None
    p2_conf_grok = None
    p2_deps_claude = []
    p2_deps_grok = []
    if _active_phase == 2:
        # Extract metadata from last Claude and Grok responses
        claude_last = [t for t in transcript if t["auditor"] == "claude"]
        grok_last = [t for t in transcript if t["auditor"] == "grok"]
        if claude_last:
            c_meta = extract_phase2_metadata(claude_last[-1]["content"])
            p2_conf_claude = c_meta["confidence"]
            p2_deps_claude = c_meta["phase1_deps"]
        if grok_last:
            g_meta = extract_phase2_metadata(grok_last[-1]["content"])
            p2_conf_grok = g_meta["confidence"]
            p2_deps_grok = g_meta["phase1_deps"]

        if _prior_values and metric in _prior_values:
            p2_prior = _prior_values[metric]
            p2_delta = round(final_score - p2_prior, 2)
            direction = "increased" if p2_delta > 0 else "decreased" if p2_delta < 0 else "unchanged"
            p2_delta_reason = f"Adversarial review {direction} from prior {p2_prior} to {final_score:.1f}"
        all_scores = [claude_score, grok_score]
        p2_status = classify_calibration_status(all_scores)

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
        round_scores=round_scores,
        prior_value=p2_prior,
        delta=p2_delta,
        delta_reason=p2_delta_reason,
        calibration_status=p2_status,
        confidence_claude=p2_conf_claude,
        confidence_grok=p2_conf_grok,
        phase1_deps_claude=p2_deps_claude,
        phase1_deps_grok=p2_deps_grok,
    )

def run_component1(baselines: Dict[str, Any], metrics: List[str], dry_run: bool = False) -> Dict[str, MetricResult]:
    """Run Component 1: Adversarial Pilot for all metrics (stance from _active_stance)"""
    results = {}

    for metric in metrics:
        result = run_metric_deliberation(metric, baselines, dry_run=dry_run)
        results[metric] = result

        if result.extraction_failed:
            print(f"\n  [ABORT] Extraction failure on {metric} — skipping remaining metrics")
            break

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
    sign_off_first_line = sign_off_response.split("\n")[0].upper()
    if "GREEN" in sign_off_first_line:
        sign_off = "GREEN"
    elif "YELLOW" in sign_off_first_line:
        sign_off = "YELLOW"
    elif "RED" in sign_off_first_line:
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
    sign_off_first_line = sign_off_response.split("\n")[0].upper()
    if "GREEN" in sign_off_first_line:
        sign_off = "GREEN"
    elif "YELLOW" in sign_off_first_line:
        sign_off = "YELLOW"
    elif "RED" in sign_off_first_line:
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
    global _active_phase, _phase1_results_data, _prior_values

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
    parser.add_argument("--phase", choices=["1", "2"], default="1",
                       help="Phase 1 = philosophical audit (BFI/CA/IP/ES/LS/MS/PS), Phase 2 = YPA lever calibration (CCI/EDB/PF_I/PF_E/AR/MG)")
    parser.add_argument("--phase1-results", type=str, default=None,
                       help="Path to Phase 1 JSON results file (required for --phase 2)")
    parser.add_argument("--preset", type=str, default=None,
                       help=f"Named prior-value preset for Phase 2 (available: {', '.join(PRIOR_PRESETS.keys())}). Overridden by --prior-values.")
    parser.add_argument("--prior-values", type=str, default=None,
                       help="Comma-separated lever=value pairs for Phase 2 priors (e.g. CCI=7.5,EDB=6.0). Overrides --preset.")
    parser.add_argument("--reverse", action="store_true",
                       help="Reverse stance: swap Claude/Grok roles (e.g. ct_vs_mdn -> mdn_vs_ct, pt_vs_ct -> ct_vs_pt)")
    parser.add_argument("--stance", type=str, default=None,
                       help=f"Explicit stance key (available: {', '.join(STANCES.keys())}). Overrides default + --reverse.")
    parser.add_argument("--duplicate-reflection", action="store_true",
                       help="Run exit survey twice on same deliberation to measure reflection-to-reflection variance (noise check)")
    parser.add_argument("--max-rounds", type=int, default=None,
                       help=f"Override max deliberation rounds per metric (default: {MAX_ROUNDS_PER_METRIC})")
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
    if args.stance:
        stance_key = args.stance.lower()
        if stance_key not in STANCES:
            print(f"[!] Unknown stance '{args.stance}'. Available: {', '.join(STANCES.keys())}")
            return
        _active_stance = STANCES[stance_key]
        print(f"[+] STANCE: {stance_key} — Claude {_active_stance['claude_stance']}, Grok {_active_stance['grok_stance']}")
        print(f"[+] Subject framework: {_active_stance['subject']}")
    elif args.reverse:
        # Legacy: --reverse without --stance defaults to mdn_vs_ct
        _active_stance = STANCES["mdn_vs_ct"]
        print(f"[+] REVERSE STANCE: Claude {_active_stance['claude_stance']}, Grok {_active_stance['grok_stance']}")
        print(f"[+] Subject framework: {_active_stance['subject']}")
    else:
        _active_stance = STANCES["ct_vs_mdn"]

    # Max rounds override
    global _max_rounds_override
    if args.max_rounds:
        _max_rounds_override = args.max_rounds
        print(f"[+] MAX ROUNDS: {_max_rounds_override} (overriding default {MAX_ROUNDS_PER_METRIC})")

    # Initialize phase configuration
    _active_phase = int(args.phase)
    if _active_phase == 2:
        METRICS[:] = PHASE2_METRICS
        METRIC_FULL_NAMES.clear()
        METRIC_FULL_NAMES.update(PHASE2_METRIC_FULL_NAMES)
        print(f"[+] PHASE 2 (Trinity²): YPA Lever Calibration")
        print(f"[+] Metrics: {', '.join(PHASE2_METRICS)}")

        # Load Phase 1 results
        if args.phase1_results:
            p1_path = Path(args.phase1_results)
            if p1_path.exists():
                with open(p1_path, encoding="utf-8") as f:
                    _phase1_results_data = json.load(f)
                p1_subj = _phase1_results_data.get("subject_framework", "?")
                p1_metrics = len(_phase1_results_data.get("component1_results", {}))
                print(f"[+] Phase 1 results loaded: {p1_subj} ({p1_metrics} metrics)")
            else:
                print(f"[!] Phase 1 results file not found: {p1_path}")
                return
        else:
            print("[!] WARNING: No --phase1-results provided. Phase 2 will run without Phase 1 context.")

        # Load prior values: --prior-values overrides --preset
        if args.prior_values:
            _prior_values = {}
            for pair in args.prior_values.split(","):
                if "=" in pair:
                    k, v = pair.split("=", 1)
                    _prior_values[k.strip().upper()] = float(v.strip())
            print(f"[+] Prior values (manual): {_prior_values}")
        elif args.preset:
            preset_key = args.preset.lower()
            if preset_key in PRIOR_PRESETS:
                _prior_values = dict(PRIOR_PRESETS[preset_key])
                print(f"[+] Prior values (preset '{preset_key}'): {_prior_values}")
            else:
                print(f"[!] Unknown preset '{args.preset}'. Available: {', '.join(PRIOR_PRESETS.keys())}")
                return

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

    # Parse metrics — use phase-appropriate defaults
    valid_metrics = PHASE2_METRICS if _active_phase == 2 else PHASE1_METRICS
    if args.metrics == ",".join(PHASE1_METRICS) and _active_phase == 2:
        metrics = PHASE2_METRICS
    else:
        metrics = [m.strip().upper() for m in args.metrics.split(",")]

    # Validate metrics
    for m in metrics:
        if m not in valid_metrics:
            print(f"[!] Invalid metric: {m}. Valid for phase {_active_phase}: {valid_metrics}")
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

    # Component 1 - Adversarial Pilot
    phase_label = "Trinity²" if _active_phase == 2 else "Phase 1"
    if args.component in ["1", "both"]:
        print(f"\n[{phase_label}] Component 1: {_active_stance['label']} Pilot ({len(metrics)} metrics)")
        print("-" * 70)
        session.component1_results = run_component1(session.baselines, metrics, dry_run=args.dry_run)

    # Phase 3: Component 2 - Axioms Review
    if args.component in ["2", "both"]:
        print(f"\n[PHASE 3] Component 2: Axioms Review")
        print("-" * 70)
        session.component2_results = run_component2(dry_run=args.dry_run)

    # Check for extraction failures — abort run early if contaminated
    _run_aborted = False
    if session.component1_results:
        for m, r in session.component1_results.items():
            if r.extraction_failed:
                _run_aborted = True
                print(f"\n[ABORT] Run contaminated by extraction failure on {m} — skipping exit surveys and marking aborted")
                session.summary["aborted"] = True
                session.summary["abort_reason"] = f"Extraction failure on {m}"
                break

    # Phase 4: Exit surveys
    if not args.skip_exit_survey and not _run_aborted:
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
            result = {
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
                "round_scores": r.round_scores,
            }
            if _active_phase == 2:
                result["prior_value"] = r.prior_value
                result["delta"] = r.delta
                result["delta_reason"] = r.delta_reason
                result["calibration_status"] = r.calibration_status
                result["confidence_claude"] = r.confidence_claude
                result["confidence_grok"] = r.confidence_grok
                result["phase1_deps_claude"] = r.phase1_deps_claude
                result["phase1_deps_grok"] = r.phase1_deps_grok
            return result
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
    stance_key = args.stance.lower() if args.stance else ("mdn_vs_ct" if args.reverse else "ct_vs_mdn")
    effective_max = _max_rounds_override if _max_rounds_override else MAX_ROUNDS_PER_METRIC
    output_data = {
        "session_id": session.session_id,
        "timestamp": session.timestamp,
        "phase": _active_phase,
        "condition": condition,
        "stance": stance_key,
        "subject_framework": _active_stance["subject"],
        "opponent_framework": _active_stance["opponent"],
        "max_rounds": effective_max,
        "challenge_object": _active_stance.get("challenge_object", None),
        "identity_augmentation": bool(_active_stance.get("identity_augmentation")),
        "duplicate_reflection": args.duplicate_reflection,
        "auditors": session.auditors,
        "predictions": session.predictions,
        "baselines": {k: {kk: vv for kk, vv in v.items() if kk != "embedding"}
                     for k, v in session.baselines.items()},
        "component1_results": {k: serialize_result(v) for k, v in session.component1_results.items()},
        "component2_results": {k: serialize_result(v) for k, v in session.component2_results.items()},
        "exit_surveys": session.exit_surveys,
        "summary": session.summary,
    }
    if _active_phase == 2:
        output_data["phase1_source"] = args.phase1_results
        output_data["prior_values"] = _prior_values

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
