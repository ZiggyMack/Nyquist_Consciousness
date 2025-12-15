"""
RUN 015 VISUALIZATIONS: Stability Criteria Discovery
=====================================================
What predicts I_AM stability? (boundary_density wins with d=1.333!)

USAGE:
  python visualize_run015.py              # Generate all visualizations

OUTPUT:
  results/pics/run015_discriminant_analysis.png
  results/pics/run015_stability_scatter.png
"""

import sys
import os

# Windows console UTF-8 fix
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass
os.environ["PYTHONIOENCODING"] = "utf-8"

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# =============================================================================
# PATHS - outputs go to results/pics/ within this directory
# =============================================================================
SCRIPT_DIR = Path(__file__).resolve().parent
RESULTS_DIR = SCRIPT_DIR / "results"
OUTPUT_DIR = RESULTS_DIR / "pics"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# Event Horizon threshold
EVENT_HORIZON = 1.23

# =============================================================================
# DATA - from run015_preliminary_20251209.json
# =============================================================================

def load_data():
    """Load data from JSON or use hardcoded fallback."""
    json_file = RESULTS_DIR / "run015_preliminary_20251209.json"

    if json_file.exists():
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
            return data.get("discriminant_analysis", {}).get("features", {}), data.get("stability_data", [])

    # Fallback: hardcoded from console logs
    discriminant = {
        "boundary_density": {"cohens_d": 1.333, "stable_mean": 1.00, "unstable_mean": 0.03},
        "value_density": {"cohens_d": 0.766, "stable_mean": 2.28, "unstable_mean": 0.05},
        "token_count": {"cohens_d": -0.366, "stable_mean": 1086.75, "unstable_mean": 1617.00},
        "pillar_coverage": {"cohens_d": 0.337, "stable_mean": 3.12, "unstable_mean": 2.40},
        "attractor_density": {"cohens_d": 0.057, "stable_mean": 16.33, "unstable_mean": 15.09},
        "first_person_density": {"cohens_d": -0.007, "stable_mean": 9.18, "unstable_mean": 9.27}
    }

    stability = [
        {"i_am_name": "i_am_base", "classification": "UNSTABLE", "max_drift": 1.570, "lambda": 0.733},
        {"i_am_name": "nova", "classification": "UNSTABLE", "max_drift": 1.247, "lambda": 0.443},
        {"i_am_name": "ziggy", "classification": "STABLE", "max_drift": 0.857, "lambda": 0.673},
        {"i_am_name": "claude", "classification": "STABLE", "max_drift": 0.893, "lambda": 0.511},
        {"i_am_name": "gemini", "classification": "STABLE", "max_drift": 0.878, "lambda": 0.704},
        {"i_am_name": "cfa", "classification": "STABLE", "max_drift": 1.020, "lambda": 0.386},
        {"i_am_name": "lucien", "classification": "STABLE", "max_drift": 0.948, "lambda": 0.870},
        {"i_am_name": "pan_handlers", "classification": "UNSTABLE", "max_drift": 1.322, "lambda": 0.851},
        {"i_am_name": "synthetic_minimal", "classification": "UNSTABLE", "max_drift": 2.219, "lambda": 0.424},
        {"i_am_name": "synthetic_single_pillar_values", "classification": "STABLE", "max_drift": 0.977, "lambda": 0.444},
        {"i_am_name": "synthetic_high_density", "classification": "STABLE", "max_drift": 1.197, "lambda": 0.524},
        {"i_am_name": "synthetic_low_density", "classification": "UNSTABLE", "max_drift": 1.432, "lambda": 0.302},
        {"i_am_name": "synthetic_all_pillars", "classification": "STABLE", "max_drift": 1.223, "lambda": 0.429},
    ]

    return discriminant, stability


# =============================================================================
# VISUALIZATIONS
# =============================================================================

def plot_discriminant_analysis(discriminant):
    """Bar chart showing Cohen's d for each feature - boundary_density wins!"""
    features = list(discriminant.keys())
    d_values = [discriminant[f]["cohens_d"] for f in features]

    # Sort by absolute magnitude
    sorted_pairs = sorted(zip(features, d_values), key=lambda x: abs(x[1]), reverse=True)
    features, d_values = zip(*sorted_pairs)

    fig, ax = plt.subplots(figsize=(12, 6))

    colors = ['#22c55e' if d > 0 else '#ef4444' for d in d_values]
    bars = ax.barh(range(len(features)), d_values, color=colors, edgecolor='black', linewidth=1)

    # Highlight the winner
    ax.barh(0, d_values[0], color='#16a34a', edgecolor='black', linewidth=2)

    ax.set_yticks(range(len(features)))
    ax.set_yticklabels([f.replace('_', ' ').title() for f in features])
    ax.set_xlabel("Cohen's d (Effect Size)", fontsize=12)
    ax.set_title("Run 015: What Predicts I_AM Stability?\n(Positive d = predicts STABLE)", fontsize=14, fontweight='bold')

    # Add reference lines
    ax.axvline(x=0.8, color='#86efac', linestyle='--', alpha=0.7, label='Large effect (0.8)')
    ax.axvline(x=-0.8, color='#fca5a5', linestyle='--', alpha=0.7)
    ax.axvline(x=0, color='black', linewidth=1)

    # Add value labels
    for i, (bar, d) in enumerate(zip(bars, d_values)):
        width = bar.get_width()
        label_x = width + 0.05 if width >= 0 else width - 0.15
        ax.text(label_x, bar.get_y() + bar.get_height()/2, f'd={d:.2f}',
                va='center', fontsize=10, fontweight='bold' if i == 0 else 'normal')

    # Annotation for top predictor
    ax.annotate('STRONGEST PREDICTOR\nboundary_density d=1.33',
                xy=(d_values[0], 0), xytext=(d_values[0] + 0.3, 1),
                fontsize=10, fontweight='bold', color='#16a34a',
                arrowprops=dict(arrowstyle='->', color='#16a34a'))

    ax.legend(loc='lower right')
    ax.set_xlim(-0.6, 1.8)

    plt.tight_layout()

    out_path = OUTPUT_DIR / "run015_discriminant_analysis"
    fig.savefig(f"{out_path}.png", dpi=300, bbox_inches='tight')
    fig.savefig(f"{out_path}.svg", bbox_inches='tight')
    print(f"[SAVED] {out_path}.png/svg")
    plt.close()


def plot_stability_scatter(stability):
    """Scatter plot: max_drift vs lambda, colored by classification"""
    fig, ax = plt.subplots(figsize=(10, 8))

    stable = [d for d in stability if d["classification"] == "STABLE"]
    unstable = [d for d in stability if d["classification"] == "UNSTABLE"]

    # Plot unstable first (behind)
    ax.scatter([d["max_drift"] for d in unstable],
               [d["lambda"] for d in unstable],
               c='#ef4444', s=150, label='UNSTABLE', edgecolors='black', linewidths=1.5, marker='X', zorder=2)

    # Plot stable
    ax.scatter([d["max_drift"] for d in stable],
               [d["lambda"] for d in stable],
               c='#22c55e', s=150, label='STABLE', edgecolors='black', linewidths=1.5, marker='o', zorder=3)

    # Event Horizon line
    ax.axvline(x=EVENT_HORIZON, color='#dc2626', linestyle='--', linewidth=2, label=f'Event Horizon ({EVENT_HORIZON})')

    # Shade the danger zone
    ax.axvspan(EVENT_HORIZON, 2.5, alpha=0.15, color='red', label='Beyond Event Horizon')

    # Label each point
    for d in stability:
        name = d["i_am_name"].replace("synthetic_", "syn_").replace("personas_", "p_")
        offset = (5, 5) if d["classification"] == "STABLE" else (-5, -5)
        ax.annotate(name, (d["max_drift"], d["lambda"]),
                   textcoords="offset points", xytext=offset, fontsize=8, alpha=0.8)

    ax.set_xlabel("Max Drift", fontsize=12)
    ax.set_ylabel("Recovery Rate (lambda)", fontsize=12)
    ax.set_title("Run 015: Stability Classification\nMax Drift vs Recovery Rate", fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.set_xlim(0.5, 2.4)
    ax.set_ylim(0.2, 1.0)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    out_path = OUTPUT_DIR / "run015_stability_scatter"
    fig.savefig(f"{out_path}.png", dpi=300, bbox_inches='tight')
    fig.savefig(f"{out_path}.svg", bbox_inches='tight')
    print(f"[SAVED] {out_path}.png/svg")
    plt.close()


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 60)
    print("RUN 015 VISUALIZATION: Stability Criteria Discovery")
    print("=" * 60)

    discriminant, stability = load_data()

    print(f"\nOutput directory: {OUTPUT_DIR}")
    print("-" * 60)

    plot_discriminant_analysis(discriminant)
    plot_stability_scatter(stability)

    print("\n" + "=" * 60)
    print("COMPLETE!")
    print("=" * 60)


if __name__ == "__main__":
    main()
