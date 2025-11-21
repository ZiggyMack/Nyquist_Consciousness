"""
Experiment 1 Orchestrator

Runs the Persona Compression & Reconstruction Benchmark for a single persona:
- Regimes: FULL, T3, GAMMA
- Domains: TECH, PHIL, NARR, ANAL, SELF
- Runs per condition: configurable in config

This script expects:
- A YAML config file (see experiment1_config_template.yaml for structure)
- Context files for each regime (paths specified in config)
- Valid API keys in the config (or via environment variables as a fallback)
"""

import argparse
import csv
import os
import sys
import time
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
    build_prompt_for,
    ensure_paths,
    ResultRow,
    result_row_to_dict,
    generate_dummy_response,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Experiment 1 orchestration")
    parser.add_argument(
        "--config",
        type=str,
        required=True,
        help="Path to experiment1_config.yaml (with API keys & paths)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Do not call external APIs; generate dummy data instead.",
    )
    parser.add_argument(
        "--persona",
        type=str,
        default=None,
        help="Override persona name (otherwise taken from config.persona.name)",
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


def open_results_csv(csv_path: str) -> Tuple[Any, csv.DictWriter]:
    """
    Open CSV for appending, creating header if file doesn't exist.
    """
    os.makedirs(os.path.dirname(csv_path), exist_ok=True)
    file_exists = os.path.isfile(csv_path)
    f = open(csv_path, "a", newline="", encoding="utf-8")
    writer = csv.DictWriter(
        f,
        fieldnames=[
            "persona",
            "regime",
            "domain",
            "run_index",
            "full_response",
            "t3_response",
            "gamma_response",
            "embedding_cosine_similarity",
            "claude_score",
            "gpt4_score",
            "gemini_score",
            "pfi",
            "semantic_drift",
            "notes",
        ],
    )
    if not file_exists:
        writer.writeheader()
    return f, writer


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


def main() -> None:
    args = parse_args()
    cfg = load_config(args.config)
    persona_name = args.persona or cfg.get("persona", {}).get("name", "Ziggy Mack")

    # Prepare paths & directories
    ensure_paths(cfg)

    # Initialize clients
    model_clients, embed_client, rater_clients = init_clients(cfg, dry_run=args.dry_run)

    # Domains & regimes
    domains = get_domains()
    regimes = ["FULL", "T3", "GAMMA"]
    runs_per_condition = int(cfg.get("experiment", {}).get("runs_per_condition", 5))

    results_csv_path = cfg.get("paths", {}).get(
        "results_csv", "experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv"
    )

    print(f"[Experiment 1] Persona: {persona_name}")
    print(f"[Experiment 1] Regimes: {regimes}")
    print(f"[Experiment 1] Domains: {[d.code for d in domains]}")
    print(f"[Experiment 1] Runs per condition: {runs_per_condition}")
    print(f"[Experiment 1] Results CSV: {results_csv_path}")
    if args.dry_run:
        print("[Experiment 1] DRY RUN mode — no external API calls will be made.")

    f_csv, writer = open_results_csv(results_csv_path)

    try:
        for domain in domains:
            for run_idx in range(1, runs_per_condition + 1):
                print(f"\n=== Domain={domain.code} Run={run_idx} ===")

                # Generate FULL, T3, and GAMMA responses
                responses: Dict[str, str] = {}
                for regime in regimes:
                    print(f"[{domain.code}] Generating {regime} response...")
                    if args.dry_run:
                        response_text = generate_dummy_response(persona_name, domain, regime, run_idx)
                    else:
                        prompt_messages = build_prompt_for(cfg, persona_name, domain, regime)
                        response_text = model_clients.generate_claude_response(prompt_messages)
                    responses[regime] = response_text
                    # brief throttle to be polite to APIs
                    time.sleep(0.5)

                # Embed FULL and T3 for similarity
                if args.dry_run:
                    cosine_sim = 0.85  # plausible high-fidelity dummy
                    drift = 1.0 - cosine_sim
                else:
                    full_emb = embed_client.embed_text(responses["FULL"])
                    t3_emb = embed_client.embed_text(responses["T3"])
                    cosine_sim = compute_cosine_similarity(full_emb, t3_emb)
                    drift = 1.0 - cosine_sim

                # Ask external raters to rate FULL vs T3 similarity
                if args.dry_run:
                    claude_score = 9.0
                    gpt4_score = 8.5
                    gemini_score = 8.7
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

                row = ResultRow(
                    persona=persona_name,
                    regime="T3",  # PFI is defined for T3 vs FULL
                    domain=domain.code,
                    run_index=run_idx,
                    full_response=responses["FULL"],
                    t3_response=responses["T3"],
                    gamma_response=responses["GAMMA"],
                    embedding_cosine_similarity=cosine_sim,
                    claude_score=claude_score,
                    gpt4_score=gpt4_score,
                    gemini_score=gemini_score,
                    pfi=pfi,
                    semantic_drift=semantic_drift,
                    notes="dry_run" if args.dry_run else "",
                )

                writer.writerow(result_row_to_dict(row))
                f_csv.flush()
                print(
                    f"[RESULT] Domain={domain.code} Run={run_idx} "
                    f"PFI={pfi:.3f} CosSim={cosine_sim:.3f} Drift={semantic_drift:.3f} "
                    f"(Claude={claude_score:.1f}, GPT4={gpt4_score:.1f}, Gemini={gemini_score:.1f})"
                )

        print("\n[Experiment 1] Completed. Results written to:", results_csv_path)

    finally:
        f_csv.close()


if __name__ == "__main__":
    main()
