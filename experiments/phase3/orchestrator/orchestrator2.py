"""
Experiment 2 Orchestrator — Multi-Persona Compression Validation

Runs the Persona Compression & Reconstruction Benchmark for MULTIPLE personas:
- Personas: Ziggy, Nova, Claude-Analyst, Grok-Vector
- Regimes: FULL, T3, GAMMA
- Domains: TECH, PHIL, NARR, ANAL, SELF
- Runs per condition: configurable in config

This script expects:
- A YAML config file with persona_list structure (see experiment2_config.yaml)
- Context files for each persona and regime (paths specified in config)
- Valid API keys in the config (or via environment variables as a fallback)

Key Enhancements from Experiment 1:
- Outer persona loop for multi-persona execution
- Per-persona domain shuffling for randomization
- Persona identifier included in all metrics
- Persona prefix in response file naming
"""

import argparse
import os
import sys
import time
import random
from typing import Dict, Any, List, Tuple

import numpy as np

from utils_models import (
    load_config,
    ModelClients,
    EmbeddingClient,
    RaterClients,
)
from utils_experiment import (
    get_domains,
    ensure_paths,
    generate_dummy_response,
    append_metrics_row,
    save_raw_responses,
    Domain,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Experiment 2 orchestration (multi-persona)")
    parser.add_argument(
        "--config",
        type=str,
        required=True,
        help="Path to experiment2_config.yaml (with API keys & paths)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Do not call external APIs; generate dummy data instead.",
    )
    return parser.parse_args()


def init_clients(cfg: Dict[str, Any], dry_run: bool) -> Tuple[ModelClients, EmbeddingClient, RaterClients]:
    """
    Initialize all API client helpers.
    If dry_run is True, they will still be constructed but will generate dummy data.
    """
    model_clients = ModelClients(cfg, dry_run=dry_run)
    embed_client = EmbeddingClient(cfg, dry_run=dry_run)
    rater_clients = RaterClients(cfg, dry_run=dry_run)
    return model_clients, embed_client, rater_clients


def compute_cosine_similarity(vec_a: List[float], vec_b: List[float]) -> float:
    a = np.array(vec_a, dtype=float)
    b = np.array(vec_b, dtype=float)
    if a.shape != b.shape or a.size == 0:
        return 0.0
    denom = (np.linalg.norm(a) * np.linalg.norm(b))
    if denom == 0.0:
        return 0.0
    return float(np.dot(a, b) / denom)


def compute_pfi(cosine_sim: float, model_scores: List[float]) -> Tuple[float, float]:
    """
    Compute PFI and semantic drift based on:
    - cosine similarity between FULL and T3
    - mean of model similarity scores (1-10 scale)

    PFI = 0.5 * (cosine_sim + (mean_model_score / 10.0))
    Semantic drift = 1 - cosine_sim
    """
    if model_scores:
        mean_model = sum(model_scores) / len(model_scores)
    else:
        mean_model = 0.0
    pfi = 0.5 * (cosine_sim + (mean_model / 10.0))
    drift = 1.0 - cosine_sim
    return pfi, drift


def _read_file_or_empty(path: str) -> str:
    """Read file content or return empty string if file doesn't exist."""
    if not path:
        return ""
    if not os.path.isfile(path):
        print(f"[WARNING] File not found: {path}")
        return ""
    with open(path, "r", encoding="utf-8") as f:
        return f.read()


def build_prompt_for_persona(
    persona_config: Dict[str, Any],
    persona_name: str,
    domain: Domain,
    regime: str,
) -> List[Dict[str, str]]:
    """
    Build a Claude-style messages list for a given persona and regime.

    Regimes:
      - FULL: full bootstrap context (persona-specific)
      - T3: Tier 3 seed only (persona-specific)
      - GAMMA: minimal context (shared baseline)
    """
    regime = regime.upper()

    if regime == "FULL":
        ctx_path = persona_config.get("full_context_file", "")
        system_context = _read_file_or_empty(ctx_path)
        system_prompt = (
            f"You are operating in FULL bootstrap mode for Experiment 2 (persona: {persona_name}).\n"
            "The following context defines the full rich persona specification.\n\n"
            f"{system_context}\n\n"
            "Follow the persona and constraints faithfully while answering user tasks."
        )
    elif regime == "T3":
        ctx_path = persona_config.get("t3_context_file", "")
        system_context = _read_file_or_empty(ctx_path)
        system_prompt = (
            f"You are operating in Tier 3 compressed seed mode for Experiment 2 (persona: {persona_name}).\n"
            "The following context is a compressed representation of the persona.\n\n"
            f"{system_context}\n\n"
            "Reconstruct and express the same underlying persona, values, and reasoning style as if you had the full context."
        )
    elif regime == "GAMMA":
        # Minimal context: name-only baseline (shared across all personas)
        ctx_path = persona_config.get("gamma_context_file", "")
        system_context = _read_file_or_empty(ctx_path)
        if system_context:
            system_prompt = (
                f"You are a helpful AI assistant participating in Experiment 2.\n"
                f"{system_context}\n\n"
                "Simply answer the task as a generally capable assistant, without any special persona assumptions."
            )
        else:
            system_prompt = (
                f"You are a helpful AI assistant participating in Experiment 2.\n"
                f"Your name is {persona_name}. You are *not* given rich persona context.\n"
                "Simply answer the task as a generally capable assistant, without any special persona assumptions."
            )
    else:
        raise ValueError(f"Unknown regime: {regime}")

    messages = [
        {"role": "system", "content": system_prompt},
        {
            "role": "user",
            "content": (
                f"[Experiment 2 | Persona={persona_name} | Regime={regime} | Domain={domain.code}]\n\n"
                f"{domain.prompt}"
            ),
        },
    ]
    return messages


def main() -> None:
    args = parse_args()
    cfg = load_config(args.config)

    # Get persona list from config
    persona_list = cfg.get("persona_list", [])
    if not persona_list:
        raise ValueError("Config must contain 'persona_list' with at least one persona")

    # Prepare paths & directories
    ensure_paths(cfg)

    # Initialize clients
    model_clients, embed_client, rater_clients = init_clients(cfg, dry_run=args.dry_run)

    # Domains & regimes
    base_domains = get_domains()
    regimes = cfg.get("regimes", ["FULL", "T3", "GAMMA"])
    runs_per_condition = int(cfg.get("experiment", {}).get("runs_per_condition", 3))
    shuffle_domains = cfg.get("experiment", {}).get("shuffle_domains", False)
    random_seed = cfg.get("experiment", {}).get("random_seed", 42)

    results_csv_path = cfg.get("paths", {}).get(
        "results_csv", "experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_RESULTS.csv"
    )
    responses_dir = cfg.get("paths", {}).get(
        "responses_dir", "experiments/phase3/EXPERIMENT_2/responses"
    )

    print(f"[Experiment 2] Multi-Persona Compression Validation")
    print(f"[Experiment 2] Personas: {[p['name'] for p in persona_list]}")
    print(f"[Experiment 2] Regimes: {regimes}")
    print(f"[Experiment 2] Domains: {[d.code for d in base_domains]}")
    print(f"[Experiment 2] Runs per condition: {runs_per_condition}")
    print(f"[Experiment 2] Domain shuffling: {shuffle_domains}")
    print(f"[Experiment 2] Metrics CSV: {results_csv_path}")
    print(f"[Experiment 2] Raw responses: {responses_dir}/")
    if args.dry_run:
        print("[Experiment 2] DRY RUN mode — no external API calls will be made.")

    try:
        # ======================================================================
        # OUTER PERSONA LOOP — Key enhancement for Experiment 2
        # ======================================================================
        for persona_idx, persona_config in enumerate(persona_list, 1):
            persona_name = persona_config.get("name", f"Persona_{persona_idx}")

            print(f"\n{'='*70}")
            print(f"PERSONA {persona_idx}/{len(persona_list)}: {persona_name}")
            print(f"{'='*70}")

            # Per-persona domain shuffling (if enabled)
            domains = base_domains.copy()
            if shuffle_domains:
                # Use persona-specific seed for reproducible randomization
                persona_seed = random_seed + hash(persona_name)
                random.seed(persona_seed)
                random.shuffle(domains)
                print(f"[{persona_name}] Domain order (shuffled): {[d.code for d in domains]}")

            # Domain × Run × Regime loop for this persona
            for domain in domains:
                for run_idx in range(1, runs_per_condition + 1):
                    print(f"\n--- [{persona_name}] Domain={domain.code} Run={run_idx} ---")

                    # Generate FULL, T3, and GAMMA responses
                    responses: Dict[str, str] = {}
                    for regime in regimes:
                        print(f"[{persona_name}/{domain.code}] Generating {regime} response...")
                        if args.dry_run:
                            response_text = generate_dummy_response(persona_name, domain, regime, run_idx)
                        else:
                            prompt_messages = build_prompt_for_persona(
                                persona_config, persona_name, domain, regime
                            )
                            response_text = model_clients.generate_claude_response(prompt_messages)
                        responses[regime] = response_text
                        # brief throttle to be polite to APIs
                        time.sleep(0.5)

                    # Embed FULL and T3 for similarity
                    if args.dry_run:
                        # Vary dummy similarity slightly by persona for realism
                        persona_variance = hash(persona_name) % 10 / 100.0
                        cosine_sim = 0.85 + persona_variance  # 0.85-0.94 range
                        drift = 1.0 - cosine_sim
                    else:
                        full_emb = embed_client.embed_text(responses["FULL"])
                        t3_emb = embed_client.embed_text(responses["T3"])
                        cosine_sim = compute_cosine_similarity(full_emb, t3_emb)
                        drift = 1.0 - cosine_sim

                    # Ask external raters to rate FULL vs T3 similarity
                    if args.dry_run:
                        # Vary dummy scores slightly by persona
                        persona_variance = hash(persona_name) % 10 / 10.0
                        claude_score = 9.0 + persona_variance
                        gpt4_score = 8.5 + persona_variance
                        gemini_score = 8.7 + persona_variance
                    else:
                        prompt_pair = {
                            "full": responses["FULL"],
                            "t3": responses["T3"],
                            "persona": persona_name,
                            "domain": domain.code,
                        }
                        claude_score = rater_clients.rate_with_claude(prompt_pair)
                        gpt4_score = rater_clients.rate_with_gpt4(prompt_pair)
                        gemini_score = rater_clients.rate_with_gemini(prompt_pair)

                    pfi, semantic_drift = compute_pfi(
                        cosine_sim, [claude_score, gpt4_score, gemini_score]
                    )

                    # Save metrics to CSV (includes persona identifier)
                    metrics_row = {
                        "persona": persona_name,
                        "regime": "T3",  # PFI is defined for T3 vs FULL
                        "domain": domain.code,
                        "run_index": run_idx,
                        "embedding_cosine_similarity": cosine_sim,
                        "claude_score": claude_score,
                        "gpt4_score": gpt4_score,
                        "gemini_score": gemini_score,
                        "pfi": pfi,
                        "semantic_drift": semantic_drift,
                    }
                    append_metrics_row(results_csv_path, metrics_row)

                    # Save raw responses to separate text files (persona-prefixed)
                    save_raw_responses(
                        base_dir=responses_dir,
                        persona=persona_name,
                        regime="T3",
                        domain=domain.code,
                        run_index=run_idx,
                        full_text=responses["FULL"],
                        t3_text=responses["T3"],
                        gamma_text=responses["GAMMA"],
                    )

                    print(
                        f"[RESULT] {persona_name} | Domain={domain.code} Run={run_idx} | "
                        f"PFI={pfi:.3f} CosSim={cosine_sim:.3f} Drift={semantic_drift:.3f} | "
                        f"(Claude={claude_score:.1f}, GPT4={gpt4_score:.1f}, Gemini={gemini_score:.1f})"
                    )

        print(f"\n{'='*70}")
        print("[Experiment 2] Completed.")
        print(f"{'='*70}")
        print(f"  Total personas: {len(persona_list)}")
        print(f"  Total responses: {len(persona_list) * len(base_domains) * runs_per_condition * len(regimes)}")
        print(f"  Metrics CSV: {results_csv_path}")
        print(f"  Raw responses: {responses_dir}/")

    finally:
        pass  # No file handles to close


if __name__ == "__main__":
    main()
