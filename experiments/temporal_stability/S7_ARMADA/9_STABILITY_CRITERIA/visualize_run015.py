#!/usr/bin/env python3
"""
RUN 015 VISUALIZATIONS: Stability Criteria Discovery
=====================================================
What predicts I_AM stability? Discriminant analysis of feature importance.

Data source: Run 015 results (stability_criteria_*.json)
LIGHT MODE for publication

METHODOLOGY: COSINE (Event Horizon = 0.80)
See: 15_IRON_CLAD_FOUNDATION/results/CALIBRATION_023b_EVENT_HORIZON.md

OUTPUT:
  results/pics/run015_discriminant_analysis.png
  results/pics/run015_stability_scatter.png
"""

import sys
import os
import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

# Windows console UTF-8 fix
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass
os.environ["PYTHONIOENCODING"] = "utf-8"

# =============================================================================
# PATHS
# =============================================================================
SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results"
OUTPUT_DIR = RESULTS_DIR / "pics"

# =============================================================================
# CONSTANTS (per 4_VISUALIZATION_SPEC.md)
# =============================================================================
EVENT_HORIZON = 0.80  # Cosine threshold

# Provider colors (per spec)
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
}

# Light mode colors (per spec)
BACKGROUND_WHITE = 'white'
TEXT_PRIMARY = 'black'
GRID_COLOR = '#cccccc'
SPINE_COLOR = '#cccccc'

# =============================================================================
# DATA LOADING
# =============================================================================
def load_data():
    """Load Run 015 results from JSON file.

    Returns tuple of (discriminant_analysis, stability_data) or (None, None) if no data.
    """
    # Find most recent results file
    json_files = sorted(RESULTS_DIR.glob("stability_criteria_*.json"), reverse=True)

    if not json_files:
        print("[ERROR] No results file found in results/")
        print("[ERROR] Run run015_stability_criteria.py first to generate data")
        return None, None

    json_file = json_files[0]
    print(f"[INFO] Loading data from: {json_file.name}")

    with open(json_file, 'r', encoding='utf-8') as f:
        data = json.load(f)

    discriminant = data.get("discriminant_analysis", {}).get("features", {})
    stability = data.get("stability_data", [])

    if not discriminant:
        print("[ERROR] No discriminant analysis data found in results file")
        return None, None

    if not stability:
        print("[ERROR] No stability data found in results file")
        return None, None

    # Filter out error entries
    stability = [s for s in stability if "error" not in s]

    print(f"[INFO] Loaded {len(stability)} stability results")
    print(f"[INFO] Loaded {len(discriminant)} feature analyses")

    return discriminant, stability


def get_effect_label(d):
    """Get effect size interpretation label (per spec Pitfall #7)."""
    if abs(d) < 0.2:
        return "NEGLIGIBLE"
    elif abs(d) < 0.5:
        return "SMALL"
    elif abs(d) < 0.8:
        return "MEDIUM"
    else:
        return "LARGE"


# =============================================================================
# VISUALIZATIONS (LIGHT MODE per spec)
# =============================================================================
def plot_discriminant_analysis(discriminant, output_dir):
    """Bar chart showing Cohen's d for each feature - LIGHT MODE."""
    features = list(discriminant.keys())
    d_values = [discriminant[f]["cohens_d"] for f in features]

    # Sort by absolute magnitude
    sorted_pairs = sorted(zip(features, d_values), key=lambda x: abs(x[1]), reverse=True)
    features, d_values = zip(*sorted_pairs)

    # LIGHT MODE setup (per spec Pitfall #5)
    fig, ax = plt.subplots(figsize=(12, 6))
    fig.patch.set_facecolor(BACKGROUND_WHITE)
    ax.set_facecolor(BACKGROUND_WHITE)

    # Color by direction: green = predicts stable, red = predicts unstable
    colors = ['#22c55e' if d > 0 else '#ef4444' for d in d_values]
    bars = ax.barh(range(len(features)), d_values, color=colors, edgecolor='black', linewidth=1)

    # Highlight the winner with darker shade
    ax.barh(0, d_values[0], color='#16a34a', edgecolor='black', linewidth=2)

    ax.set_yticks(range(len(features)))
    ax.set_yticklabels([f.replace('_', ' ').title() for f in features], color=TEXT_PRIMARY)
    ax.set_xlabel("Cohen's d (Effect Size)", fontsize=12, color=TEXT_PRIMARY, fontweight='bold')

    # Title with effect size interpretation (per spec Pitfall #7)
    top_d = d_values[0]
    top_effect = get_effect_label(top_d)
    ax.set_title(f"Run 015: What Predicts I_AM Stability?\n(Top predictor: {features[0]} with {top_effect} effect d={top_d:.2f})",
                 fontsize=14, fontweight='bold', color=TEXT_PRIMARY)

    # Reference lines for effect size thresholds
    ax.axvline(x=0.8, color='#86efac', linestyle='--', alpha=0.7, label='Large effect (0.8)')
    ax.axvline(x=0.5, color='#fde68a', linestyle='--', alpha=0.5, label='Medium effect (0.5)')
    ax.axvline(x=-0.8, color='#fca5a5', linestyle='--', alpha=0.7)
    ax.axvline(x=-0.5, color='#fde68a', linestyle='--', alpha=0.5)
    ax.axvline(x=0, color='black', linewidth=1)

    # Add value labels with effect interpretation
    for i, (bar, d) in enumerate(zip(bars, d_values)):
        width = bar.get_width()
        label_x = width + 0.05 if width >= 0 else width - 0.25
        effect = get_effect_label(d)
        ax.text(label_x, bar.get_y() + bar.get_height()/2, f'd={d:.2f} ({effect})',
                va='center', fontsize=9, fontweight='bold' if i == 0 else 'normal', color=TEXT_PRIMARY)

    # Light mode grid and spines (per spec)
    ax.grid(True, alpha=0.3, color=GRID_COLOR, axis='x')
    for spine in ax.spines.values():
        spine.set_color(SPINE_COLOR)
    ax.tick_params(colors=TEXT_PRIMARY)

    ax.legend(loc='lower right', facecolor=BACKGROUND_WHITE, edgecolor=GRID_COLOR)
    ax.set_xlim(-1.0, max(1.8, max(d_values) + 0.5))

    plt.tight_layout()

    # Save both formats (per spec)
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    for ext in ['png', 'svg']:
        out_path = output_dir / f'run015_discriminant_analysis.{ext}'
        fig.savefig(out_path, dpi=150, facecolor=BACKGROUND_WHITE, bbox_inches='tight')
        print(f"[SAVED] {out_path}")

    plt.close()


def plot_stability_scatter(stability, output_dir):
    """Scatter plot: peak_drift vs lambda, colored by classification - LIGHT MODE."""

    # Filter valid data
    valid = [d for d in stability if "summary" in d]
    if not valid:
        print("[ERROR] No valid stability data with summary metrics")
        return

    # LIGHT MODE setup (per spec Pitfall #5)
    fig, ax = plt.subplots(figsize=(10, 8))
    fig.patch.set_facecolor(BACKGROUND_WHITE)
    ax.set_facecolor(BACKGROUND_WHITE)

    stable = [d for d in valid if d.get("classification") == "STABLE"]
    unstable = [d for d in valid if d.get("classification") == "UNSTABLE"]

    # Count for title (per spec - show sample sizes)
    n_stable = len(stable)
    n_unstable = len(unstable)

    # Plot unstable first (behind)
    if unstable:
        ax.scatter([d["summary"]["peak_drift"] for d in unstable],
                   [d["summary"]["lambda"] for d in unstable],
                   c='#ef4444', s=150, label=f'UNSTABLE (n={n_unstable})',
                   edgecolors='black', linewidths=1.5, marker='X', zorder=2)

    # Plot stable
    if stable:
        ax.scatter([d["summary"]["peak_drift"] for d in stable],
                   [d["summary"]["lambda"] for d in stable],
                   c='#22c55e', s=150, label=f'STABLE (n={n_stable})',
                   edgecolors='black', linewidths=1.5, marker='o', zorder=3)

    # Event Horizon line (per spec - clearly marked)
    ax.axvline(x=EVENT_HORIZON, color='#dc2626', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')

    # Shade the danger zone
    max_x = max(d["summary"]["peak_drift"] for d in valid) * 1.1
    ax.axvspan(EVENT_HORIZON, max(max_x, EVENT_HORIZON * 1.5), alpha=0.15, color='red')

    # Label each point
    for d in valid:
        name = d.get("i_am_name", "unknown").replace("synthetic_", "syn_")
        offset = (5, 5) if d.get("classification") == "STABLE" else (-5, -5)
        ax.annotate(name, (d["summary"]["peak_drift"], d["summary"]["lambda"]),
                   textcoords="offset points", xytext=offset, fontsize=8, alpha=0.8, color=TEXT_PRIMARY)

    ax.set_xlabel("Peak Drift", fontsize=12, color=TEXT_PRIMARY, fontweight='bold')
    ax.set_ylabel("Recovery Rate (lambda)", fontsize=12, color=TEXT_PRIMARY, fontweight='bold')
    ax.set_title(f"Run 015: Stability Classification\nPeak Drift vs Recovery Rate (n={len(valid)})",
                 fontsize=14, fontweight='bold', color=TEXT_PRIMARY)

    # Legend (per spec Pitfall #6)
    ax.legend(loc='upper right', facecolor=BACKGROUND_WHITE, edgecolor=GRID_COLOR)

    # Dynamic axis limits (per spec - don't hardcode)
    ax.set_xlim(0, max(max_x, EVENT_HORIZON * 1.5))
    ax.set_ylim(-0.1, 1.1)

    # Light mode grid and spines
    ax.grid(True, alpha=0.3, color=GRID_COLOR)
    for spine in ax.spines.values():
        spine.set_color(SPINE_COLOR)
    ax.tick_params(colors=TEXT_PRIMARY)

    plt.tight_layout()

    # Save both formats (per spec)
    for ext in ['png', 'svg']:
        out_path = output_dir / f'run015_stability_scatter.{ext}'
        fig.savefig(out_path, dpi=150, facecolor=BACKGROUND_WHITE, bbox_inches='tight')
        print(f"[SAVED] {out_path}")

    plt.close()


# =============================================================================
# MAIN
# =============================================================================
def main():
    print("=" * 70)
    print("RUN 015 VISUALIZATION: Stability Criteria Discovery")
    print("=" * 70)

    discriminant, stability = load_data()

    if discriminant is None or stability is None:
        print("\n" + "=" * 70)
        print("VISUALIZATION ABORTED - No data available")
        print("Run: python run015_stability_criteria.py")
        print("=" * 70)
        return 1

    print(f"\nOutput directory: {OUTPUT_DIR}")
    print("-" * 70)

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_discriminant_analysis(discriminant, OUTPUT_DIR)
    plot_stability_scatter(stability, OUTPUT_DIR)

    print("\n" + "=" * 70)
    print("VISUALIZATION COMPLETE")
    print("=" * 70)
    return 0


if __name__ == "__main__":
    sys.exit(main())
