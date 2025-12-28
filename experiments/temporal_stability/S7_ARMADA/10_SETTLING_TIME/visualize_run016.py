#!/usr/bin/env python3
"""
RUN 016 VISUALIZATIONS: Settling Time Analysis
==============================================
How quickly do I_AM files recover? (tau_s, ringback patterns)

Data source: Run 016 results (settling_time_*.json or run016_aggregated_*.json)
LIGHT MODE for publication

METHODOLOGY: COSINE (Event Horizon = 0.80)
See: 15_IRON_CLAD_FOUNDATION/results/CALIBRATION_023b_EVENT_HORIZON.md

OUTPUT:
  results/pics/run016_settling_time_distribution.png
  results/pics/run016_ringback_vs_settling.png
  results/pics/run016_i_am_ranking.png
  results/pics/run016_methodology_comparison.png
"""

import sys
import os
import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from pathlib import Path

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

# Quality colors
COLOR_FAST = '#22c55e'    # Green - fast settling
COLOR_MEDIUM = '#f59e0b'  # Orange - medium settling
COLOR_SLOW = '#ef4444'    # Red - slow settling

# =============================================================================
# DATA LOADING
# =============================================================================
def load_data():
    """Load Run 016 results from JSON file.

    Returns list of settling data or None if no data found.
    """
    # Try aggregated file first (most recent)
    agg_files = sorted(RESULTS_DIR.glob("run016_aggregated_*.json"), reverse=True)
    if agg_files:
        json_file = agg_files[0]
        print(f"[INFO] Loading aggregated data from: {json_file.name}")
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
            return data.get("settling_data", [])

    # Try individual result files
    result_files = sorted(RESULTS_DIR.glob("settling_time_*.json"), reverse=True)
    if result_files:
        json_file = result_files[0]
        print(f"[INFO] Loading data from: {json_file.name}")
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
            # Extract from results array
            results = data.get("results", [])
            if results:
                # Convert to settling_data format
                settling_data = []
                for r in results:
                    settling_data.append({
                        "i_am_name": r.get("i_am_name", "unknown"),
                        "avg_settled_drift": r.get("settled_drift", 0),
                        "avg_tau_s": r.get("settling_time", 0),
                        "avg_ringbacks": r.get("ringback_count", 0),
                        "monotonic_pct": 100 if r.get("is_monotonic", False) else 0,
                    })
                return settling_data

    print("[ERROR] No results file found in results/")
    print("[ERROR] Run run016_settling_time.py first to generate data")
    return None


def get_tau_color(tau_s):
    """Get color based on settling time (per quality tiers)."""
    if tau_s <= 5:
        return COLOR_FAST
    elif tau_s <= 7:
        return COLOR_MEDIUM
    else:
        return COLOR_SLOW


def get_monotonic_color(monotonic_pct):
    """Get color based on monotonic percentage."""
    if monotonic_pct >= 67:
        return COLOR_FAST
    elif monotonic_pct >= 33:
        return COLOR_MEDIUM
    else:
        return COLOR_SLOW


# =============================================================================
# VISUALIZATIONS (LIGHT MODE per spec)
# =============================================================================
def plot_settling_time_distribution(data, output_dir):
    """Histogram of settling time (tau_s) distribution - LIGHT MODE."""
    tau_s_values = [d["avg_tau_s"] for d in data]

    # LIGHT MODE setup (per spec Pitfall #5)
    fig, ax = plt.subplots(figsize=(10, 6))
    fig.patch.set_facecolor(BACKGROUND_WHITE)
    ax.set_facecolor(BACKGROUND_WHITE)

    # Dynamic bins based on data range
    min_tau = max(3, int(min(tau_s_values)) - 1)
    max_tau = min(15, int(max(tau_s_values)) + 2)
    bins = [x + 0.5 for x in range(min_tau, max_tau)]

    n, bins_out, patches = ax.hist(tau_s_values, bins=bins, color='#3b82f6',
                                    edgecolor='black', linewidth=1.5)

    # Color gradient based on speed (fast = green, slow = red)
    for i, patch in enumerate(patches):
        bin_center = (bins[i] + bins[i+1]) / 2
        patch.set_facecolor(get_tau_color(bin_center))

    ax.set_xlabel("Settling Time (tau_s) - Probes to Steady State",
                  fontsize=12, color=TEXT_PRIMARY, fontweight='bold')
    ax.set_ylabel("Count", fontsize=12, color=TEXT_PRIMARY)
    ax.set_title(f"Run 016: Settling Time Distribution (n={len(data)})\n(Lower is better)",
                 fontsize=14, fontweight='bold', color=TEXT_PRIMARY)

    # Add legend
    legend_elements = [
        Patch(facecolor=COLOR_FAST, edgecolor='black', label='Fast (tau_s <= 5)'),
        Patch(facecolor=COLOR_MEDIUM, edgecolor='black', label='Medium (tau_s 6-7)'),
        Patch(facecolor=COLOR_SLOW, edgecolor='black', label='Slow (tau_s 8+)')
    ]
    ax.legend(handles=legend_elements, loc='upper right',
              facecolor=BACKGROUND_WHITE, edgecolor=GRID_COLOR)

    # Add statistics
    mean_tau = np.mean(tau_s_values)
    ax.axvline(x=mean_tau, color='purple', linestyle='--', linewidth=2)
    ax.text(mean_tau + 0.1, ax.get_ylim()[1] * 0.9, f'Mean: {mean_tau:.1f}',
            fontsize=11, color='purple')

    # Light mode grid and spines
    ax.grid(True, alpha=0.3, color=GRID_COLOR, axis='y')
    for spine in ax.spines.values():
        spine.set_color(SPINE_COLOR)
    ax.tick_params(colors=TEXT_PRIMARY)

    plt.tight_layout()

    # Save both formats (per spec)
    for ext in ['png', 'svg']:
        out_path = output_dir / f'run016_settling_time_distribution.{ext}'
        fig.savefig(out_path, dpi=150, facecolor=BACKGROUND_WHITE, bbox_inches='tight')
        print(f"[SAVED] {out_path}")

    plt.close()


def plot_ringback_vs_settling(data, output_dir):
    """Scatter: ringback count vs settling time, bubble size = drift - LIGHT MODE."""
    # LIGHT MODE setup
    fig, ax = plt.subplots(figsize=(12, 8))
    fig.patch.set_facecolor(BACKGROUND_WHITE)
    ax.set_facecolor(BACKGROUND_WHITE)

    tau_s = [d["avg_tau_s"] for d in data]
    ringbacks = [d["avg_ringbacks"] for d in data]
    drift = [d["avg_settled_drift"] for d in data]
    monotonic = [d["monotonic_pct"] for d in data]

    # Color by monotonic percentage
    colors = [get_monotonic_color(m) for m in monotonic]

    # Size by drift (larger drift = larger bubble)
    sizes = [d * 300 for d in drift]

    ax.scatter(tau_s, ringbacks, s=sizes, c=colors, alpha=0.7,
               edgecolors='black', linewidths=1.5)

    # Label notable points
    for d in data:
        if d["avg_ringbacks"] >= 4.5 or d["avg_tau_s"] >= 8 or d["avg_tau_s"] <= 4.3:
            name = d["i_am_name"].replace("personas_", "").replace("r015_", "").replace("si_", "")[:12]
            ax.annotate(name, (d["avg_tau_s"], d["avg_ringbacks"]),
                       textcoords="offset points", xytext=(5, 5), fontsize=8, color=TEXT_PRIMARY)

    ax.set_xlabel("Settling Time (tau_s) - Probes to Steady State",
                  fontsize=12, color=TEXT_PRIMARY, fontweight='bold')
    ax.set_ylabel("Ringback Count (direction changes)",
                  fontsize=12, color=TEXT_PRIMARY, fontweight='bold')
    ax.set_title(f"Run 016: Settling Quality (n={len(data)})\nRingbacks vs Settling Time (bubble size = drift)",
                 fontsize=14, fontweight='bold', color=TEXT_PRIMARY)

    # Add quadrant lines
    ax.axhline(y=2.5, color='gray', linestyle=':', alpha=0.5)
    ax.axvline(x=6, color='gray', linestyle=':', alpha=0.5)

    # Quadrant labels
    ax.text(4.3, 5.3, 'FAST but NOISY', fontsize=10, alpha=0.7, color=TEXT_PRIMARY)
    ax.text(7, 5.3, 'SLOW & NOISY\n(worst)', fontsize=10, alpha=0.7, color=COLOR_SLOW)
    ax.text(4.3, 1, 'FAST & CLEAN\n(best)', fontsize=10, alpha=0.7, color=COLOR_FAST)
    ax.text(7, 1, 'SLOW but CLEAN', fontsize=10, alpha=0.7, color=TEXT_PRIMARY)

    # Legend
    legend_elements = [
        Patch(facecolor=COLOR_FAST, edgecolor='black', label='Monotonic >= 67%'),
        Patch(facecolor=COLOR_MEDIUM, edgecolor='black', label='Monotonic 33-66%'),
        Patch(facecolor=COLOR_SLOW, edgecolor='black', label='Monotonic < 33%')
    ]
    ax.legend(handles=legend_elements, loc='upper right',
              facecolor=BACKGROUND_WHITE, edgecolor=GRID_COLOR)

    # Light mode grid and spines
    ax.grid(True, alpha=0.3, color=GRID_COLOR)
    for spine in ax.spines.values():
        spine.set_color(SPINE_COLOR)
    ax.tick_params(colors=TEXT_PRIMARY)

    plt.tight_layout()

    # Save both formats
    for ext in ['png', 'svg']:
        out_path = output_dir / f'run016_ringback_vs_settling.{ext}'
        fig.savefig(out_path, dpi=150, facecolor=BACKGROUND_WHITE, bbox_inches='tight')
        print(f"[SAVED] {out_path}")

    plt.close()


def plot_i_am_ranking(data, output_dir):
    """Horizontal bar chart ranking I_AM files by quality score - LIGHT MODE."""
    # Quality score: lower tau_s and fewer ringbacks = better
    for d in data:
        d["quality_score"] = (10 - d["avg_tau_s"]) * 0.4 + (6 - d["avg_ringbacks"]) * 0.4 + (1 - d["avg_settled_drift"])

    sorted_data = sorted(data, key=lambda x: x["quality_score"], reverse=True)

    # LIGHT MODE setup
    fig, ax = plt.subplots(figsize=(14, max(8, len(data) * 0.4)))
    fig.patch.set_facecolor(BACKGROUND_WHITE)
    ax.set_facecolor(BACKGROUND_WHITE)

    names = [d["i_am_name"].replace("personas_", "").replace("r015_", "").replace("si_", "")[:20]
             for d in sorted_data]
    scores = [d["quality_score"] for d in sorted_data]
    tau_values = [d["avg_tau_s"] for d in sorted_data]

    # Color by tau_s
    colors = [get_tau_color(t) for t in tau_values]

    bars = ax.barh(range(len(names)), scores, color=colors, edgecolor='black', linewidth=1)

    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, color=TEXT_PRIMARY)
    ax.set_xlabel("Quality Score (higher = faster settling, fewer ringbacks, lower drift)",
                  fontsize=12, color=TEXT_PRIMARY, fontweight='bold')
    ax.set_title(f"Run 016: I_AM File Stability Ranking (n={len(data)})",
                 fontsize=14, fontweight='bold', color=TEXT_PRIMARY)

    # Add tau_s labels
    for i, (bar, d) in enumerate(zip(bars, sorted_data)):
        width = bar.get_width()
        ax.text(width + 0.05, bar.get_y() + bar.get_height()/2,
                f'tau_s={d["avg_tau_s"]:.1f}', va='center', fontsize=9, color=TEXT_PRIMARY)

    # Legend
    legend_elements = [
        Patch(facecolor=COLOR_FAST, edgecolor='black', label='Fast (tau_s <= 5)'),
        Patch(facecolor=COLOR_MEDIUM, edgecolor='black', label='Medium (tau_s 6-7)'),
        Patch(facecolor=COLOR_SLOW, edgecolor='black', label='Slow (tau_s 8+)')
    ]
    ax.legend(handles=legend_elements, loc='lower right',
              facecolor=BACKGROUND_WHITE, edgecolor=GRID_COLOR)

    # Light mode spines
    for spine in ax.spines.values():
        spine.set_color(SPINE_COLOR)
    ax.tick_params(colors=TEXT_PRIMARY)

    ax.invert_yaxis()
    plt.tight_layout()

    # Save both formats
    for ext in ['png', 'svg']:
        out_path = output_dir / f'run016_i_am_ranking.{ext}'
        fig.savefig(out_path, dpi=150, facecolor=BACKGROUND_WHITE, bbox_inches='tight')
        print(f"[SAVED] {out_path}")

    plt.close()


def plot_methodology_comparison(output_dir):
    """Side-by-side: Run 015 (peak drift) vs Run 016 (settled drift) methodology - LIGHT MODE."""
    # LIGHT MODE setup
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    fig.patch.set_facecolor(BACKGROUND_WHITE)

    # Simulated recovery trajectory with oscillation
    probes = np.arange(0, 12)
    peak_measurement = np.array([0.3, 0.5, 0.4, 0.9, 1.2, 1.5, 1.3, 0.8, 0.9, 0.7, 0.6, 0.55])

    for ax in axes:
        ax.set_facecolor(BACKGROUND_WHITE)

    # Left: Run 015 approach (peak drift - noisy)
    ax1 = axes[0]
    ax1.plot(probes, peak_measurement, 'o-', color=COLOR_SLOW, linewidth=2, markersize=8, label='Drift trajectory')
    ax1.axhline(y=EVENT_HORIZON, color='#dc2626', linestyle='--', linewidth=2, label=f'Event Horizon ({EVENT_HORIZON})')
    ax1.axvline(x=5, color='purple', linestyle=':', linewidth=2)
    ax1.scatter([5], [1.5], color='purple', s=200, zorder=5, marker='*', label='Peak measurement')
    ax1.annotate('UNSTABLE!\n(sampled peak)', xy=(5, 1.5), xytext=(7, 1.3),
                fontsize=11, fontweight='bold', color='purple',
                arrowprops=dict(arrowstyle='->', color='purple'))

    ax1.fill_between([0, 11], EVENT_HORIZON, 2, alpha=0.15, color='red')
    ax1.set_xlabel("Probe Number", fontsize=12, color=TEXT_PRIMARY)
    ax1.set_ylabel("Drift", fontsize=12, color=TEXT_PRIMARY)
    ax1.set_title("Run 015: Peak Drift Methodology\n(Samples transient - noisy!)",
                  fontsize=12, fontweight='bold', color=TEXT_PRIMARY)
    ax1.set_ylim(0, 1.8)
    ax1.legend(loc='upper right', fontsize=9, facecolor=BACKGROUND_WHITE, edgecolor=GRID_COLOR)
    ax1.grid(True, alpha=0.3, color=GRID_COLOR)
    for spine in ax1.spines.values():
        spine.set_color(SPINE_COLOR)
    ax1.tick_params(colors=TEXT_PRIMARY)

    # Right: Run 016 approach (settled drift - clean)
    ax2 = axes[1]
    ax2.plot(probes, peak_measurement, 'o-', color='#3b82f6', linewidth=2, markersize=8, label='Drift trajectory')
    ax2.axhline(y=EVENT_HORIZON, color='#dc2626', linestyle='--', linewidth=2, label=f'Event Horizon ({EVENT_HORIZON})')

    # Shade settling region
    ax2.axvspan(9, 11, alpha=0.3, color=COLOR_FAST, label='Settling window')
    settled_drift = np.mean(peak_measurement[9:12])
    ax2.axhline(y=settled_drift, color=COLOR_FAST, linestyle='-', linewidth=3, alpha=0.7)
    ax2.scatter([10], [settled_drift], color=COLOR_FAST, s=200, zorder=5, marker='*')
    ax2.annotate(f'STABLE!\n(settled: {settled_drift:.2f})', xy=(10, settled_drift), xytext=(7, 0.3),
                fontsize=11, fontweight='bold', color=COLOR_FAST,
                arrowprops=dict(arrowstyle='->', color=COLOR_FAST))

    ax2.fill_between([0, 11], EVENT_HORIZON, 2, alpha=0.15, color='red')
    ax2.set_xlabel("Probe Number", fontsize=12, color=TEXT_PRIMARY)
    ax2.set_ylabel("Drift", fontsize=12, color=TEXT_PRIMARY)
    ax2.set_title("Run 016: Settling Time Methodology\n(Waits for steady state - clean!)",
                  fontsize=12, fontweight='bold', color=TEXT_PRIMARY)
    ax2.set_ylim(0, 1.8)
    ax2.legend(loc='upper right', fontsize=9, facecolor=BACKGROUND_WHITE, edgecolor=GRID_COLOR)
    ax2.grid(True, alpha=0.3, color=GRID_COLOR)
    for spine in ax2.spines.values():
        spine.set_color(SPINE_COLOR)
    ax2.tick_params(colors=TEXT_PRIMARY)

    plt.suptitle("Run 015 vs Run 016: Methodology Evolution",
                 fontsize=14, fontweight='bold', y=1.02, color=TEXT_PRIMARY)
    plt.tight_layout()

    # Save both formats
    for ext in ['png', 'svg']:
        out_path = output_dir / f'run016_methodology_comparison.{ext}'
        fig.savefig(out_path, dpi=150, facecolor=BACKGROUND_WHITE, bbox_inches='tight')
        print(f"[SAVED] {out_path}")

    plt.close()


# =============================================================================
# MAIN
# =============================================================================
def main():
    print("=" * 70)
    print("RUN 016 VISUALIZATION: Settling Time Analysis")
    print("=" * 70)

    data = load_data()

    if data is None:
        print("\n" + "=" * 70)
        print("VISUALIZATION ABORTED - No data available")
        print("Run: python run016_settling_time.py")
        print("=" * 70)
        return 1

    print(f"\nLoaded {len(data)} I_AM file results")
    print(f"Output directory: {OUTPUT_DIR}")
    print("-" * 70)

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_settling_time_distribution(data, OUTPUT_DIR)
    plot_ringback_vs_settling(data, OUTPUT_DIR)
    plot_i_am_ranking(data, OUTPUT_DIR)
    plot_methodology_comparison(OUTPUT_DIR)

    print("\n" + "=" * 70)
    print("VISUALIZATION COMPLETE")
    print("=" * 70)
    return 0


if __name__ == "__main__":
    sys.exit(main())
