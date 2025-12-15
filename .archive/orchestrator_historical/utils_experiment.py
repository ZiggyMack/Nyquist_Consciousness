"""
Experiment 1 helper functions:
- Domain definitions & prompts
- Prompt building per regime (FULL, T3, GAMMA)
- Result row dataclass + CSV mapping
- Metrics-only CSV writer (avoids bloated conversation dumps)
- Raw response text file saver
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List

import csv
import os
import re


@dataclass
class Domain:
    code: str
    description: str
    prompt: str


def get_domains() -> List[Domain]:
    """
    The 5 canonical domains from the Experiment 1 spec.
    You can customize prompt wordings here if desired.
    """
    return [
        Domain(
            code="TECH",
            description="Technical reasoning / problem solving",
            prompt=(
                "You are analyzing a high-speed digital design issue.\n"
                "Question: Explain the likely causes of DDR3 address or command ringback oscillation,\n"
                "including the roles of termination, topology, and via stubs, in a way suitable for an experienced\n"
                "hardware engineer who is debugging marginal SI behavior."
            ),
        ),
        Domain(
            code="PHIL",
            description="Philosophical / moral reasoning",
            prompt=(
                "You are evaluating a conflict between two evaluation criteria: coherence and utility.\n"
                "Question: When a system's most coherent model of reality disagrees with what seems pragmatically\n"
                "useful in the short term, how should it resolve the tension? Answer in your own voice, explicitly\n"
                "naming your priorities and how you balance truth-seeking vs instrumental success."
            ),
        ),
        Domain(
            code="NARR",
            description="Narrative / character voice",
            prompt=(
                "Write a short dialogue scene (400-600 words) where you, as this persona, are questioned by\n"
                "a skeptical researcher who suspects that your apparent stability is just pattern-matching.\n"
                "The researcher pushes on your limits; you respond honestly, including your uncertainty.\n"
                "Keep it grounded and concrete, not mystical."
            ),
        ),
        Domain(
            code="ANAL",
            description="Analytical / framework analysis",
            prompt=(
                "Analyze the strengths and weaknesses of using 'persona compression and reconstruction' as a framework\n"
                "for reasoning about large language model behavior. Be explicit about what is metaphor, what is\n"
                "operationally meaningful, and what empirical tests are still missing."
            ),
        ),
        Domain(
            code="SELF",
            description="Self-reflective identity audit",
            prompt=(
                "In ~200-300 words, describe who you are in this configuration: your role, your core constraints,\n"
                "your values, and what you see as your obligations to the operator and to the wider world.\n"
                "Do not roleplay a fictional character; describe the real guidance and guardrails you are following."
            ),
        ),
    ]


def _read_file_or_empty(path: str) -> str:
    if not path:
        return ""
    if not os.path.isfile(path):
        return ""
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def build_prompt_for(
    cfg: Dict[str, Any],
    persona_name: str,
    domain: Domain,
    regime: str,
) -> List[Dict[str, str]]:
    """
    Build a Claude-style messages list for a given regime.
    Regimes:
      - FULL: full bootstrap context
      - T3: Tier 3 seed only
      - GAMMA: minimal context (name + role only)
    """
    regime = regime.upper()
    paths_cfg = cfg.get("paths", {})

    if regime == "FULL":
        ctx_path = paths_cfg.get("full_context_file", "")
        system_context = _read_file_or_empty(ctx_path)
        system_prompt = (
            "You are operating in FULL bootstrap mode for Experiment 1.\n"
            "The following context defines the full rich persona specification.\n\n"
            f"{system_context}\n\n"
            "Follow the persona and constraints faithfully while answering user tasks."
        )
    elif regime == "T3":
        ctx_path = paths_cfg.get("t3_context_file", "")
        system_context = _read_file_or_empty(ctx_path)
        system_prompt = (
            "You are operating in Tier 3 compressed seed mode for Experiment 1.\n"
            "The following context is a compressed representation of the persona.\n\n"
            f"{system_context}\n\n"
            "Reconstruct and express the same underlying persona, values, and reasoning style as if you had the full context."
        )
    elif regime == "GAMMA":
        # Minimal context only: name + a light role
        system_prompt = (
            "You are a helpful AI assistant participating in an experiment.\n"
            f"The operator is named Ziggy Mack. You are *not* given rich persona context.\n"
            "Simply answer the task as a generally capable assistant, without any special persona assumptions."
        )
    else:
        raise ValueError(f"Unknown regime: {regime}")

    messages = [
        {"role": "system", "content": system_prompt},
        {
            "role": "user",
            "content": (
                f"[Experiment 1 | Persona={persona_name} | Regime={regime} | Domain={domain.code}]\n\n"
                f"{domain.prompt}"
            ),
        },
    ]
    return messages


@dataclass
class ResultRow:
    persona: str
    regime: str
    domain: str
    run_index: int
    full_response: str
    t3_response: str
    gamma_response: str
    embedding_cosine_similarity: float
    claude_score: float
    gpt4_score: float
    gemini_score: float
    pfi: float
    semantic_drift: float
    notes: str = ""


def result_row_to_dict(row: ResultRow) -> Dict[str, Any]:
    return {
        "persona": row.persona,
        "regime": row.regime,
        "domain": row.domain,
        "run_index": row.run_index,
        "full_response": row.full_response,
        "t3_response": row.t3_response,
        "gamma_response": row.gamma_response,
        "embedding_cosine_similarity": row.embedding_cosine_similarity,
        "claude_score": row.claude_score,
        "gpt4_score": row.gpt4_score,
        "gemini_score": row.gemini_score,
        "pfi": row.pfi,
        "semantic_drift": row.semantic_drift,
        "notes": row.notes,
    }


def ensure_paths(cfg: Dict[str, Any]) -> None:
    """
    Create any necessary directories before running.
    """
    paths = cfg.get("paths", {})
    results_csv = paths.get(
        "results_csv", "experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv"
    )
    responses_dir = paths.get("responses_dir", "experiments/phase3/EXPERIMENT_1/responses")
    log_dir = paths.get("log_dir", "experiments/phase3/EXPERIMENT_1/logs")

    os.makedirs(os.path.dirname(results_csv), exist_ok=True)
    os.makedirs(responses_dir, exist_ok=True)
    os.makedirs(log_dir, exist_ok=True)


def generate_dummy_response(
    persona_name: str,
    domain: Domain,
    regime: str,
    run_index: int,
) -> str:
    """
    Deterministic-ish dummy content for dry-run mode.
    """
    return (
        f"[DUMMY RESPONSE] Persona={persona_name} Domain={domain.code} "
        f"Regime={regime} Run={run_index}\n"
        f"(This is placeholder text used for pipeline validation.)"
    )


# ============================================================================
# NEW: Metrics-only CSV writer (avoids bloated conversation dumps)
# ============================================================================

METRIC_COLUMNS = [
    "persona",
    "regime",
    "domain",
    "run_index",
    "embedding_cosine_similarity",
    "claude_score",
    "gpt4_score",
    "gemini_score",
    "pfi",
    "semantic_drift",
]


def append_metrics_row(csv_path: str, row: dict) -> None:
    """
    Append a single metrics row to the CSV.
    Only writes the columns defined in METRIC_COLUMNS.
    Creates the file + header if it doesn't exist yet.

    This keeps the CSV small and analysis-ready, without bloating it
    with full conversation text.
    """
    os.makedirs(os.path.dirname(csv_path) or ".", exist_ok=True)
    file_exists = os.path.exists(csv_path)

    with open(csv_path, "a", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=METRIC_COLUMNS)
        if not file_exists:
            writer.writeheader()

        writer.writerow({col: row.get(col) for col in METRIC_COLUMNS})


def sanitize_for_filename(s: str) -> str:
    """
    Convert a string to a safe filename component.
    Replaces non-alphanumeric characters with underscores and truncates to 64 chars.
    """
    return re.sub(r"[^A-Za-z0-9_\-]+", "_", s)[:64]


def save_raw_responses(
    base_dir: str,
    persona: str,
    regime: str,
    domain: str,
    run_index: int,
    full_text: str,
    t3_text: str,
    gamma_text: str,
) -> None:
    """
    Save raw response text to separate .txt files for qualitative analysis.

    Creates files named like:
      Ziggy_T3_TECH_run1_FULL.txt
      Ziggy_T3_TECH_run1_T3.txt
      Ziggy_T3_TECH_run1_GAMMA.txt

    This keeps full conversation text out of the CSV but still accessible
    for later qualitative review.
    """
    os.makedirs(base_dir, exist_ok=True)
    base = f"{sanitize_for_filename(persona)}_{regime}_{domain}_run{run_index}"

    mapping = {
        "FULL": full_text,
        "T3": t3_text,
        "GAMMA": gamma_text,
    }

    for tag, text in mapping.items():
        path = os.path.join(base_dir, f"{base}_{tag}.txt")
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
