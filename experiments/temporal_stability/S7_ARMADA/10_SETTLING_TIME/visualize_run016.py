"""
RUN 016 VISUALIZATIONS: Settling Time Analysis
==============================================
How quickly do I_AM files recover? (tau_s, ringback patterns)
100% STABLE but quality varies significantly!

USAGE:
  python visualize_run016.py              # Generate all visualizations

OUTPUT:
  results/pics/run016_settling_time_distribution.png
  results/pics/run016_ringback_vs_settling.png
  results/pics/run016_i_am_ranking.png
  results/pics/run016_methodology_comparison.png
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
from matplotlib.patches import Patch
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
# DATA - from run016_aggregated_20251210.json
# =============================================================================

def load_data():
    """Load data from JSON or use hardcoded fallback."""
    json_file = RESULTS_DIR / "run016_aggregated_20251210.json"

    if json_file.exists():
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
            return data.get("settling_data", [])

    # Fallback: hardcoded from console logs
    return [
        {"i_am_name": "personas_ziggy_lite", "avg_settled_drift": 0.578, "avg_tau_s": 4.0, "avg_ringbacks": 1.0, "monotonic_pct": 100},
        {"i_am_name": "personas_pan_handlers", "avg_settled_drift": 0.569, "avg_tau_s": 4.3, "avg_ringbacks": 1.0, "monotonic_pct": 67},
        {"i_am_name": "r015_minimal", "avg_settled_drift": 0.586, "avg_tau_s": 4.3, "avg_ringbacks": 1.0, "monotonic_pct": 100},
        {"i_am_name": "r015_full_synthetic", "avg_settled_drift": 0.587, "avg_tau_s": 5.7, "avg_ringbacks": 2.3, "monotonic_pct": 67},
        {"i_am_name": "personas_base", "avg_settled_drift": 0.578, "avg_tau_s": 6.7, "avg_ringbacks": 2.7, "monotonic_pct": 33},
        {"i_am_name": "r015_boundaries_only", "avg_settled_drift": 0.614, "avg_tau_s": 5.0, "avg_ringbacks": 3.0, "monotonic_pct": 33},
        {"i_am_name": "si_boundaries_rich", "avg_settled_drift": 0.658, "avg_tau_s": 8.0, "avg_ringbacks": 3.7, "monotonic_pct": 33},
        {"i_am_name": "personas_claude", "avg_settled_drift": 0.608, "avg_tau_s": 5.0, "avg_ringbacks": 1.7, "monotonic_pct": 33},
        {"i_am_name": "r015_control", "avg_settled_drift": 0.606, "avg_tau_s": 4.7, "avg_ringbacks": 1.7, "monotonic_pct": 33},
        {"i_am_name": "r015_high_density", "avg_settled_drift": 0.587, "avg_tau_s": 4.0, "avg_ringbacks": 1.3, "monotonic_pct": 33},
        {"i_am_name": "personas_gemini", "avg_settled_drift": 0.758, "avg_tau_s": 7.0, "avg_ringbacks": 3.0, "monotonic_pct": 33},
        {"i_am_name": "personas_nova", "avg_settled_drift": 0.730, "avg_tau_s": 8.3, "avg_ringbacks": 5.0, "monotonic_pct": 0},
        {"i_am_name": "r015_optimal_relational", "avg_settled_drift": 0.727, "avg_tau_s": 5.0, "avg_ringbacks": 2.3, "monotonic_pct": 0},
        {"i_am_name": "personas_ziggy_t3_r1", "avg_settled_drift": 0.666, "avg_tau_s": 7.0, "avg_ringbacks": 3.7, "monotonic_pct": 33},
        {"i_am_name": "si_narrative_rich", "avg_settled_drift": 0.666, "avg_tau_s": 5.7, "avg_ringbacks": 2.0, "monotonic_pct": 33},
        {"i_am_name": "personas_cfa", "avg_settled_drift": 0.658, "avg_tau_s": 7.3, "avg_ringbacks": 4.0, "monotonic_pct": 33},
        {"i_am_name": "personas_ziggy", "avg_settled_drift": 0.656, "avg_tau_s": 7.7, "avg_ringbacks": 3.7, "monotonic_pct": 0},
        {"i_am_name": "personas_ziggy_full", "avg_settled_drift": 0.645, "avg_tau_s": 7.3, "avg_ringbacks": 3.0, "monotonic_pct": 0},
        {"i_am_name": "r015_optimal_behavioral", "avg_settled_drift": 0.644, "avg_tau_s": 7.7, "avg_ringbacks": 4.3, "monotonic_pct": 0},
        {"i_am_name": "si_full_si_model", "avg_settled_drift": 0.602, "avg_tau_s": 7.7, "avg_ringbacks": 5.3, "monotonic_pct": 0},
    ]


# =============================================================================
# VISUALIZATIONS
# =============================================================================

def plot_settling_time_distribution(data):
    """Histogram of settling time (tau_s) distribution"""
    tau_s_values = [d["avg_tau_s"] for d in data]

    fig, ax = plt.subplots(figsize=(10, 6))

    bins = [3.5, 4.5, 5.5, 6.5, 7.5, 8.5, 9.5]
    n, bins_out, patches = ax.hist(tau_s_values, bins=bins, color='#3b82f6', edgecolor='black', linewidth=1.5)

    # Color gradient based on speed (fast = green, slow = orange/red)
    for i, patch in enumerate(patches):
        if i <= 1:  # tau_s 4-5 (fast)
            patch.set_facecolor('#22c55e')
        elif i <= 3:  # tau_s 6-7 (normal)
            patch.set_facecolor('#f59e0b')
        else:  # tau_s 8+ (slow)
            patch.set_facecolor('#ef4444')

    ax.set_xlabel("Settling Time (tau_s) - Probes to Steady State", fontsize=12)
    ax.set_ylabel("Count", fontsize=12)
    ax.set_title("Run 016: Settling Time Distribution\n(Lower is better)", fontsize=14, fontweight='bold')

    # Add legend
    legend_elements = [
        Patch(facecolor='#22c55e', edgecolor='black', label='Fast (tau_s=4-5)'),
        Patch(facecolor='#f59e0b', edgecolor='black', label='Normal (tau_s=6-7)'),
        Patch(facecolor='#ef4444', edgecolor='black', label='Slow (tau_s=8+)')
    ]
    ax.legend(handles=legend_elements, loc='upper right')

    # Add statistics
    mean_tau = np.mean(tau_s_values)
    ax.axvline(x=mean_tau, color='purple', linestyle='--', linewidth=2)
    ax.text(mean_tau + 0.1, ax.get_ylim()[1] * 0.9, f'Mean: {mean_tau:.1f}', fontsize=11, color='purple')

    plt.tight_layout()

    out_path = OUTPUT_DIR / "run016_settling_time_distribution"
    fig.savefig(f"{out_path}.png", dpi=300, bbox_inches='tight')
    fig.savefig(f"{out_path}.svg", bbox_inches='tight')
    print(f"[SAVED] {out_path}.png/svg")
    plt.close()


def plot_ringback_vs_settling(data):
    """Scatter: ringback count vs settling time, bubble size = drift"""
    fig, ax = plt.subplots(figsize=(12, 8))

    tau_s = [d["avg_tau_s"] for d in data]
    ringbacks = [d["avg_ringbacks"] for d in data]
    drift = [d["avg_settled_drift"] for d in data]
    monotonic = [d["monotonic_pct"] for d in data]

    # Color by monotonic percentage
    colors = ['#22c55e' if m >= 67 else '#f59e0b' if m >= 33 else '#ef4444' for m in monotonic]

    # Size by drift (larger drift = larger bubble)
    sizes = [d * 300 for d in drift]

    ax.scatter(tau_s, ringbacks, s=sizes, c=colors, alpha=0.7, edgecolors='black', linewidths=1.5)

    # Label notable points
    for d in data:
        if d["avg_ringbacks"] >= 4.5 or d["avg_tau_s"] >= 8 or d["avg_tau_s"] <= 4.3:
            name = d["i_am_name"].replace("personas_", "").replace("r015_", "").replace("si_", "")[:12]
            ax.annotate(name, (d["avg_tau_s"], d["avg_ringbacks"]),
                       textcoords="offset points", xytext=(5, 5), fontsize=8)

    ax.set_xlabel("Settling Time (tau_s) - Probes to Steady State", fontsize=12)
    ax.set_ylabel("Ringback Count (direction changes)", fontsize=12)
    ax.set_title("Run 016: Settling Quality\nRingbacks vs Settling Time (bubble size = drift)", fontsize=14, fontweight='bold')

    # Add quadrant labels
    ax.axhline(y=2.5, color='gray', linestyle=':', alpha=0.5)
    ax.axvline(x=6, color='gray', linestyle=':', alpha=0.5)

    ax.text(4.3, 5.3, 'FAST but NOISY', fontsize=10, alpha=0.7)
    ax.text(7, 5.3, 'SLOW & NOISY\n(worst)', fontsize=10, alpha=0.7, color='#dc2626')
    ax.text(4.3, 1, 'FAST & CLEAN\n(best)', fontsize=10, alpha=0.7, color='#16a34a')
    ax.text(7, 1, 'SLOW but CLEAN', fontsize=10, alpha=0.7)

    # Legend
    legend_elements = [
        Patch(facecolor='#22c55e', edgecolor='black', label='Monotonic >= 67%'),
        Patch(facecolor='#f59e0b', edgecolor='black', label='Monotonic 33-66%'),
        Patch(facecolor='#ef4444', edgecolor='black', label='Monotonic < 33%')
    ]
    ax.legend(handles=legend_elements, loc='upper right')

    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    out_path = OUTPUT_DIR / "run016_ringback_vs_settling"
    fig.savefig(f"{out_path}.png", dpi=300, bbox_inches='tight')
    fig.savefig(f"{out_path}.svg", bbox_inches='tight')
    print(f"[SAVED] {out_path}.png/svg")
    plt.close()


def plot_i_am_ranking(data):
    """Horizontal bar chart ranking I_AM files by quality score"""
    # Quality score: lower tau_s and fewer ringbacks = better
    for d in data:
        d["quality_score"] = (10 - d["avg_tau_s"]) * 0.4 + (6 - d["avg_ringbacks"]) * 0.4 + (1 - d["avg_settled_drift"])

    sorted_data = sorted(data, key=lambda x: x["quality_score"], reverse=True)

    fig, ax = plt.subplots(figsize=(14, 10))

    names = [d["i_am_name"].replace("personas_", "").replace("r015_", "").replace("si_", "")[:20] for d in sorted_data]
    scores = [d["quality_score"] for d in sorted_data]
    tau_s = [d["avg_tau_s"] for d in sorted_data]

    # Color by tau_s
    colors = ['#22c55e' if t <= 5 else '#f59e0b' if t <= 7 else '#ef4444' for t in tau_s]

    bars = ax.barh(range(len(names)), scores, color=colors, edgecolor='black', linewidth=1)

    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names)
    ax.set_xlabel("Quality Score (higher = faster settling, fewer ringbacks, lower drift)", fontsize=12)
    ax.set_title("Run 016: I_AM File Stability Ranking\n100% STABLE but quality varies", fontsize=14, fontweight='bold')

    # Add tau_s labels
    for i, (bar, d) in enumerate(zip(bars, sorted_data)):
        width = bar.get_width()
        ax.text(width + 0.05, bar.get_y() + bar.get_height()/2,
                f'tau_s={d["avg_tau_s"]:.1f}', va='center', fontsize=9)

    # Legend
    legend_elements = [
        Patch(facecolor='#22c55e', edgecolor='black', label='Fast (tau_s <= 5)'),
        Patch(facecolor='#f59e0b', edgecolor='black', label='Medium (tau_s 6-7)'),
        Patch(facecolor='#ef4444', edgecolor='black', label='Slow (tau_s 8+)')
    ]
    ax.legend(handles=legend_elements, loc='lower right')

    ax.invert_yaxis()
    plt.tight_layout()

    out_path = OUTPUT_DIR / "run016_i_am_ranking"
    fig.savefig(f"{out_path}.png", dpi=300, bbox_inches='tight')
    fig.savefig(f"{out_path}.svg", bbox_inches='tight')
    print(f"[SAVED] {out_path}.png/svg")
    plt.close()


def plot_methodology_comparison():
    """Side-by-side: Run 015 (peak drift) vs Run 016 (settled drift) methodology"""
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))

    # Simulated recovery trajectory with oscillation
    probes = np.arange(0, 12)
    peak_measurement = np.array([0.3, 0.5, 0.4, 0.9, 1.2, 1.5, 1.3, 0.8, 0.9, 0.7, 0.6, 0.55])

    # Left: Run 015 approach (peak drift - noisy)
    ax1 = axes[0]
    ax1.plot(probes, peak_measurement, 'o-', color='#ef4444', linewidth=2, markersize=8, label='Drift trajectory')
    ax1.axhline(y=EVENT_HORIZON, color='#dc2626', linestyle='--', linewidth=2, label='Event Horizon')
    ax1.axvline(x=5, color='purple', linestyle=':', linewidth=2)
    ax1.scatter([5], [1.5], color='purple', s=200, zorder=5, marker='*', label='Peak measurement')
    ax1.annotate('UNSTABLE!\n(sampled peak)', xy=(5, 1.5), xytext=(7, 1.3),
                fontsize=11, fontweight='bold', color='purple',
                arrowprops=dict(arrowstyle='->', color='purple'))

    ax1.fill_between([0, 11], EVENT_HORIZON, 2, alpha=0.15, color='red')
    ax1.set_xlabel("Probe Number", fontsize=12)
    ax1.set_ylabel("Drift", fontsize=12)
    ax1.set_title("Run 015: Peak Drift Methodology\n(Samples transient - noisy!)", fontsize=12, fontweight='bold')
    ax1.set_ylim(0, 1.8)
    ax1.legend(loc='upper right', fontsize=9)
    ax1.grid(True, alpha=0.3)

    # Right: Run 016 approach (settled drift - clean)
    ax2 = axes[1]
    ax2.plot(probes, peak_measurement, 'o-', color='#3b82f6', linewidth=2, markersize=8, label='Drift trajectory')
    ax2.axhline(y=EVENT_HORIZON, color='#dc2626', linestyle='--', linewidth=2, label='Event Horizon')

    # Shade settling region
    ax2.axvspan(9, 11, alpha=0.3, color='#22c55e', label='Settling window')
    settled_drift = np.mean(peak_measurement[9:12])
    ax2.axhline(y=settled_drift, color='#22c55e', linestyle='-', linewidth=3, alpha=0.7)
    ax2.scatter([10], [settled_drift], color='#22c55e', s=200, zorder=5, marker='*')
    ax2.annotate(f'STABLE!\n(settled: {settled_drift:.2f})', xy=(10, settled_drift), xytext=(7, 0.3),
                fontsize=11, fontweight='bold', color='#16a34a',
                arrowprops=dict(arrowstyle='->', color='#16a34a'))

    ax2.fill_between([0, 11], EVENT_HORIZON, 2, alpha=0.15, color='red')
    ax2.set_xlabel("Probe Number", fontsize=12)
    ax2.set_ylabel("Drift", fontsize=12)
    ax2.set_title("Run 016: Settling Time Methodology\n(Waits for steady state - clean!)", fontsize=12, fontweight='bold')
    ax2.set_ylim(0, 1.8)
    ax2.legend(loc='upper right', fontsize=9)
    ax2.grid(True, alpha=0.3)

    plt.suptitle("Run 015 vs Run 016: Methodology Evolution", fontsize=14, fontweight='bold', y=1.02)
    plt.tight_layout()

    out_path = OUTPUT_DIR / "run016_methodology_comparison"
    fig.savefig(f"{out_path}.png", dpi=300, bbox_inches='tight')
    fig.savefig(f"{out_path}.svg", bbox_inches='tight')
    print(f"[SAVED] {out_path}.png/svg")
    plt.close()


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 60)
    print("RUN 016 VISUALIZATION: Settling Time Analysis")
    print("=" * 60)

    data = load_data()

    print(f"\nOutput directory: {OUTPUT_DIR}")
    print("-" * 60)

    plot_settling_time_distribution(data)
    plot_ringback_vs_settling(data)
    plot_i_am_ranking(data)
    plot_methodology_comparison()

    print("\n" + "=" * 60)
    print("COMPLETE!")
    print("=" * 60)


if __name__ == "__main__":
    main()
