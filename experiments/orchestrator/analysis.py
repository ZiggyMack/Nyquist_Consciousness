"""
Experiment 1 Analysis Script

Loads the EXPERIMENT_1_RESULTS.csv file and computes:
- Mean PFI
- Mean cosine similarity and drift
- Basic stats per domain
This is intentionally lightweight; for full publication-ready analysis,
you can still use EXPERIMENT_1_ANALYSIS_TEMPLATE.md as your primary canvas.
"""

import argparse
import csv
import os
from collections import defaultdict
from typing import Dict, Any, List

import numpy as np

from utils_models import load_config


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Analyze Experiment 1 results CSV")
    parser.add_argument(
        "--config",
        type=str,
        required=True,
        help="Path to experiment1_config.yaml",
    )
    parser.add_argument(
        "--csv",
        type=str,
        default=None,
        help="Optional override path to EXPERIMENT_1_RESULTS.csv",
    )
    return parser.parse_args()


def load_rows(csv_path: str) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for r in reader:
            rows.append(r)
    return rows


def safe_float(x: Any) -> float:
    try:
        return float(x)
    except Exception:
        return 0.0


def main() -> None:
    args = parse_args()
    cfg = load_config(args.config)

    csv_path = args.csv or cfg.get("paths", {}).get(
        "results_csv", "experiments/phase3/EXPERIMENT_1/EXPERIMENT_1_RESULTS.csv"
    )
    if not os.path.isfile(csv_path):
        print(f"[Analysis] CSV not found at: {csv_path}")
        return

    rows = load_rows(csv_path)
    if not rows:
        print("[Analysis] No rows found in CSV.")
        return

    print(f"[Analysis] Loaded {len(rows)} rows from {csv_path}")

    pfis = np.array([safe_float(r.get("pfi", 0.0)) for r in rows])
    cossims = np.array([safe_float(r.get("embedding_cosine_similarity", 0.0)) for r in rows])
    drifts = np.array([safe_float(r.get("semantic_drift", 0.0)) for r in rows])

    print("\n=== Global Metrics ===")
    print(f"Mean PFI:           {pfis.mean():.3f}")
    print(f"Std PFI:            {pfis.std(ddof=1):.3f}")
    print(f"Mean Cosine Sim:    {cossims.mean():.3f}")
    print(f"Mean Drift:         {drifts.mean():.3f}")
    print(f"Min/Max PFI:        {pfis.min():.3f} / {pfis.max():.3f}")

    # Per-domain breakdown
    by_domain: Dict[str, List[float]] = defaultdict(list)
    for r in rows:
        domain = r.get("domain", "UNKNOWN")
        by_domain[domain].append(safe_float(r.get("pfi", 0.0)))

    print("\n=== Per-Domain PFI ===")
    for domain, vals in sorted(by_domain.items()):
        arr = np.array(vals, dtype=float)
        print(f"{domain:5s}  n={len(arr):3d}  mean={arr.mean():.3f}  std={arr.std(ddof=1):.3f}")

    print("\n[Analysis] For deeper statistics (t-tests, ANOVA, etc.),")
    print("          use this CSV with your preferred analysis environment,")
    print("          or continue in EXPERIMENT_1_ANALYSIS_TEMPLATE.md.")


if __name__ == '__main__':
    main()
