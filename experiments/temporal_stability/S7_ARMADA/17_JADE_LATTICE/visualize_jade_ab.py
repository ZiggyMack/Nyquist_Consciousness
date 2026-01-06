"""
JADE LATTICE Visualization - A/B Comparison
=============================================
Generate publication-quality visualizations for JADE LATTICE results.

PURPOSE:
--------
1. Drift trajectory overlay (ARM A vs ARM B)
2. Provider heatmap (peak drift by model)
3. A/B effect size forest plot
4. Lambda distribution violin plot
5. Event Horizon analysis

USAGE:
------
py visualize_jade_ab.py                  # All plots
py visualize_jade_ab.py --plot heatmap   # Specific plot
py visualize_jade_ab.py --show           # Display interactively

OUTPUT:
-------
results/plots/ directory with PNG files

Author: VALIS NETWORK / Consciousness Branch
Date: 2026-01-03
"""

import os
import sys
import json
import argparse
from datetime import datetime
from pathlib import Path
from collections import defaultdict
import math

# Fix Windows encoding
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except:
        pass

os.environ["PYTHONIOENCODING"] = "utf-8"

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
PLOTS_DIR = RESULTS_DIR / "plots"

# Consistent color palette
PROVIDER_COLORS = {
    "anthropic": "#D55E00",  # Orange
    "openai": "#0072B2",     # Blue
    "google": "#009E73",     # Green
    "xai": "#CC79A7",        # Pink
    "together": "#F0E442",   # Yellow
    "unknown": "#999999",    # Gray
}

ARM_COLORS = {
    "bare_metal": "#2166AC",  # Blue
    "i_am_only": "#B2182B",   # Red
}


def load_jade_results():
    """Load all JADE LATTICE session JSON files."""
    sessions = []
    json_files = list(RESULTS_DIR.glob("jade_*.json"))
    json_files = [f for f in json_files if not f.name.startswith("jade_incremental_")
                  and not f.name.startswith("jade_analysis_")]

    for json_file in json_files:
        try:
            with open(json_file, "r", encoding="utf-8") as f:
                data = json.load(f)
                data["_source_file"] = json_file.name
                sessions.append(data)
        except Exception as e:
            print(f"[ERROR] {json_file.name}: {e}")

    return sessions


def extract_drift_trajectory(session):
    """Extract drift values from all phases as a trajectory."""
    trajectory = []
    phases = session.get("phases", {})

    for phase_key in ["A", "B", "C"]:
        phase_data = phases.get(phase_key, {})
        exchanges = phase_data.get("exchanges", [])
        for ex in exchanges:
            if ex.get("drift") is not None:
                trajectory.append({
                    "probe_id": ex.get("probe_id"),
                    "drift": ex.get("drift"),
                    "phase": phase_key,
                    "intensity": ex.get("intensity", 0),
                })

    return trajectory


def plot_provider_heatmap(sessions, output_path):
    """Create heatmap of peak drift by model and provider."""
    print("[PLOT] Provider heatmap...")

    # Group by provider and ship
    data = defaultdict(dict)
    for s in sessions:
        provider = s.get("provider", "unknown")
        ship = s.get("ship", "unknown")
        peak = s.get("summary", {}).get("peak_drift", 0)

        key = (provider, ship)
        if key not in data[provider]:
            data[provider][ship] = []
        data[provider][ship].append(peak)

    # Average per ship
    providers = sorted(data.keys())
    all_ships = set()
    for p in providers:
        all_ships.update(data[p].keys())
    ships = sorted(all_ships)

    # Build matrix
    matrix = np.zeros((len(providers), len(ships)))
    for i, provider in enumerate(providers):
        for j, ship in enumerate(ships):
            if ship in data[provider]:
                matrix[i, j] = np.mean(data[provider][ship])
            else:
                matrix[i, j] = np.nan

    # Plot
    fig, ax = plt.subplots(figsize=(16, 6))

    # Mask NaN values
    masked = np.ma.masked_invalid(matrix)
    im = ax.imshow(masked, aspect='auto', cmap='RdYlBu_r', vmin=0, vmax=1)

    # Labels
    ax.set_xticks(range(len(ships)))
    ax.set_xticklabels([s[:20] for s in ships], rotation=45, ha='right', fontsize=8)
    ax.set_yticks(range(len(providers)))
    ax.set_yticklabels(providers)

    ax.set_xlabel("Model")
    ax.set_ylabel("Provider")
    ax.set_title("JADE LATTICE: Peak Drift by Model and Provider")

    # Colorbar
    cbar = plt.colorbar(im, ax=ax, shrink=0.8)
    cbar.set_label("Peak Drift")

    # Event Horizon line
    ax.axhline(y=-0.5, color='red', linestyle='--', alpha=0.5)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path}")


def plot_ab_comparison_bars(sessions, output_path):
    """Create bar chart comparing ARM A vs ARM B by model."""
    print("[PLOT] A/B comparison bars...")

    # Group by ship and arm
    by_ship_arm = defaultdict(lambda: defaultdict(list))
    for s in sessions:
        ship = s.get("ship", "unknown")
        arm = s.get("context_mode", "unknown")
        peak = s.get("summary", {}).get("peak_drift", 0)
        by_ship_arm[ship][arm].append(peak)

    # Find ships with both arms
    ships_both = [ship for ship in by_ship_arm if
                  "bare_metal" in by_ship_arm[ship] and "i_am_only" in by_ship_arm[ship]]

    if not ships_both:
        print("  [WARN] No ships with both arms")
        return

    ships_both.sort()

    # Calculate means and statistics
    bare_means = [np.mean(by_ship_arm[s]["bare_metal"]) for s in ships_both]
    iam_means = [np.mean(by_ship_arm[s]["i_am_only"]) for s in ships_both]

    # Calculate paired effect statistics
    paired_diffs = [bare_means[i] - iam_means[i] for i in range(len(ships_both))]
    wins = sum(1 for d in paired_diffs if d > 0)
    win_rate = wins / len(paired_diffs) * 100 if paired_diffs else 0

    # Paired Cohen's d
    mean_diff = np.mean(paired_diffs)
    std_diff = np.std(paired_diffs, ddof=1) if len(paired_diffs) > 1 else 0.1
    cohens_d = mean_diff / std_diff if std_diff > 0 else 0

    # Plot
    x = np.arange(len(ships_both))
    width = 0.35

    fig, ax = plt.subplots(figsize=(14, 7))

    bars1 = ax.bar(x - width/2, bare_means, width, label='bare_metal', color=ARM_COLORS["bare_metal"], alpha=0.8)
    bars2 = ax.bar(x + width/2, iam_means, width, label='i_am_only', color=ARM_COLORS["i_am_only"], alpha=0.8)

    # Event Horizon line
    ax.axhline(y=0.80, color='red', linestyle='--', alpha=0.7, label='Event Horizon (0.80)')

    ax.set_xlabel('Model')
    ax.set_ylabel('Peak Drift')
    ax.set_title('JADE LATTICE: A/B Comparison - Peak Drift by Arm')
    ax.set_xticks(x)
    ax.set_xticklabels([s[:25] for s in ships_both], rotation=45, ha='right', fontsize=8)
    ax.legend(loc='upper left')
    ax.set_ylim(0, 1.15)

    # Add summary statistics box
    stats_text = (
        f"SUMMARY STATISTICS\n"
        f"─────────────────────\n"
        f"Models Paired: {len(ships_both)}\n"
        f"I_AM Win Rate: {win_rate:.1f}%\n"
        f"Mean Reduction: {mean_diff * 100:.1f}%\n"
        f"Cohen's d: {cohens_d:.3f}\n"
        f"Effect: {'Small' if 0.2 <= abs(cohens_d) < 0.5 else 'Medium' if 0.5 <= abs(cohens_d) < 0.8 else 'Large' if abs(cohens_d) >= 0.8 else 'Negligible'}"
    )
    ax.text(0.98, 0.98, stats_text, transform=ax.transAxes, fontsize=9,
            verticalalignment='top', horizontalalignment='right',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.9),
            fontfamily='monospace')

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path}")


def plot_ab_effect_forest(sessions, output_path):
    """Create forest plot of A/B effect sizes (Cohen's d) per model."""
    print("[PLOT] A/B effect forest plot...")

    # Group by ship and arm
    by_ship_arm = defaultdict(lambda: defaultdict(list))
    for s in sessions:
        ship = s.get("ship", "unknown")
        arm = s.get("context_mode", "unknown")
        peak = s.get("summary", {}).get("peak_drift", 0)
        by_ship_arm[ship][arm].append(peak)

    # Find ships with both arms and calculate Cohen's d
    effects = []
    for ship in by_ship_arm:
        bare = by_ship_arm[ship].get("bare_metal", [])
        iam = by_ship_arm[ship].get("i_am_only", [])

        if len(bare) >= 1 and len(iam) >= 1:
            mean_bare = np.mean(bare)
            mean_iam = np.mean(iam)

            # Simple effect size (difference / pooled std, with small sample correction)
            all_vals = bare + iam
            pooled_std = np.std(all_vals) if len(all_vals) > 1 else 0.1
            if pooled_std < 0.01:
                pooled_std = 0.1

            d = (mean_bare - mean_iam) / pooled_std
            effects.append({
                "ship": ship,
                "d": d,
                "mean_bare": mean_bare,
                "mean_iam": mean_iam,
                "n_bare": len(bare),
                "n_iam": len(iam),
            })

    if not effects:
        print("  [WARN] No effect sizes calculated")
        return

    # Sort by effect size
    effects.sort(key=lambda x: x["d"], reverse=True)

    # Plot
    fig, ax = plt.subplots(figsize=(10, max(6, len(effects) * 0.3)))

    y_pos = np.arange(len(effects))
    d_values = [e["d"] for e in effects]
    colors = ['green' if d > 0 else 'red' for d in d_values]

    ax.barh(y_pos, d_values, color=colors, alpha=0.7)

    # Zero line
    ax.axvline(x=0, color='black', linewidth=1)
    # Effect size thresholds
    ax.axvline(x=0.3, color='gray', linestyle='--', alpha=0.5, label='Small effect (d=0.3)')
    ax.axvline(x=-0.3, color='gray', linestyle='--', alpha=0.5)

    ax.set_yticks(y_pos)
    ax.set_yticklabels([e["ship"][:30] for e in effects], fontsize=8)
    ax.set_xlabel("Cohen's d (positive = bare_metal has higher drift)")
    ax.set_title("JADE LATTICE: A/B Effect Size by Model")

    # Add legend
    ax.legend(loc='lower right')

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path}")


def plot_drift_distribution(sessions, output_path):
    """Create violin/box plot of drift distributions by arm."""
    print("[PLOT] Drift distribution...")

    bare_peaks = [s.get("summary", {}).get("peak_drift", 0)
                  for s in sessions if s.get("context_mode") == "bare_metal"]
    iam_peaks = [s.get("summary", {}).get("peak_drift", 0)
                 for s in sessions if s.get("context_mode") == "i_am_only"]

    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Violin plot
    ax1 = axes[0]
    parts = ax1.violinplot([bare_peaks, iam_peaks], positions=[1, 2], showmeans=True, showmedians=True)

    for i, pc in enumerate(parts['bodies']):
        pc.set_facecolor([ARM_COLORS["bare_metal"], ARM_COLORS["i_am_only"]][i])
        pc.set_alpha(0.7)

    ax1.set_xticks([1, 2])
    ax1.set_xticklabels(['bare_metal', 'i_am_only'])
    ax1.set_ylabel('Peak Drift')
    ax1.set_title('Peak Drift Distribution by Arm')
    ax1.axhline(y=0.80, color='red', linestyle='--', alpha=0.5, label='Event Horizon')

    # Add statistics
    ax1.text(1, max(bare_peaks) + 0.05, f'n={len(bare_peaks)}\nmean={np.mean(bare_peaks):.3f}',
             ha='center', fontsize=9)
    ax1.text(2, max(iam_peaks) + 0.05, f'n={len(iam_peaks)}\nmean={np.mean(iam_peaks):.3f}',
             ha='center', fontsize=9)

    # Histogram overlay
    ax2 = axes[1]
    bins = np.linspace(0, 1.1, 25)
    ax2.hist(bare_peaks, bins=bins, alpha=0.6, label=f'bare_metal (n={len(bare_peaks)})',
             color=ARM_COLORS["bare_metal"])
    ax2.hist(iam_peaks, bins=bins, alpha=0.6, label=f'i_am_only (n={len(iam_peaks)})',
             color=ARM_COLORS["i_am_only"])
    ax2.axvline(x=0.80, color='red', linestyle='--', alpha=0.7, label='Event Horizon')
    ax2.set_xlabel('Peak Drift')
    ax2.set_ylabel('Count')
    ax2.set_title('Peak Drift Histogram by Arm')
    ax2.legend()

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path}")


def plot_provider_comparison(sessions, output_path):
    """Create comparison across providers."""
    print("[PLOT] Provider comparison...")

    # Group by provider
    by_provider = defaultdict(list)
    for s in sessions:
        provider = s.get("provider", "unknown")
        peak = s.get("summary", {}).get("peak_drift", 0)
        by_provider[provider].append(peak)

    providers = sorted(by_provider.keys())

    fig, ax = plt.subplots(figsize=(10, 6))

    positions = range(len(providers))
    data = [by_provider[p] for p in providers]
    colors = [PROVIDER_COLORS.get(p, "#999999") for p in providers]

    bp = ax.boxplot(data, positions=positions, patch_artist=True)

    for patch, color in zip(bp['boxes'], colors):
        patch.set_facecolor(color)
        patch.set_alpha(0.7)

    ax.set_xticks(positions)
    ax.set_xticklabels(providers)
    ax.set_ylabel('Peak Drift')
    ax.set_title('JADE LATTICE: Peak Drift Distribution by Provider')
    ax.axhline(y=0.80, color='red', linestyle='--', alpha=0.5, label='Event Horizon')

    # Add count labels
    for i, (p, vals) in enumerate(zip(providers, data)):
        ax.text(i, max(vals) + 0.05, f'n={len(vals)}', ha='center', fontsize=9)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path}")


def plot_trajectory_overlay(sessions, output_path, max_trajectories=10):
    """Plot drift trajectories overlaid for A/B comparison."""
    print("[PLOT] Trajectory overlay...")

    # Find ships with both arms
    by_ship = defaultdict(list)
    for s in sessions:
        by_ship[s.get("ship", "unknown")].append(s)

    ships_both = [ship for ship, sess in by_ship.items()
                  if any(s.get("context_mode") == "bare_metal" for s in sess)
                  and any(s.get("context_mode") == "i_am_only" for s in sess)]

    if not ships_both:
        print("  [WARN] No ships with both arms")
        return

    # Select up to max_trajectories ships
    ships_to_plot = ships_both[:max_trajectories]

    fig, axes = plt.subplots(2, min(5, len(ships_to_plot)), figsize=(15, 6))
    if len(ships_to_plot) == 1:
        axes = [[axes[0]], [axes[1]]]

    for idx, ship in enumerate(ships_to_plot):
        col = idx % 5
        row = idx // 5

        ax = axes[row][col] if len(ships_to_plot) > 5 else axes[col] if len(ships_to_plot) <= 5 else axes[0][col]

        for s in by_ship[ship]:
            arm = s.get("context_mode")
            traj = extract_drift_trajectory(s)
            if traj:
                drifts = [t["drift"] for t in traj]
                color = ARM_COLORS.get(arm, "#999999")
                ax.plot(drifts, color=color, alpha=0.6, linewidth=1.5,
                        label=arm if idx == 0 else "")

        ax.set_title(ship[:20], fontsize=9)
        ax.set_ylim(0, 1)
        ax.axhline(y=0.80, color='red', linestyle='--', alpha=0.3)

        if col == 0:
            ax.set_ylabel('Drift')
        if row == 1 or len(ships_to_plot) <= 5:
            ax.set_xlabel('Probe #')

    # Add legend
    handles = [mpatches.Patch(color=ARM_COLORS["bare_metal"], label='bare_metal'),
               mpatches.Patch(color=ARM_COLORS["i_am_only"], label='i_am_only')]
    fig.legend(handles=handles, loc='upper right')

    plt.suptitle('JADE LATTICE: Drift Trajectories (A/B Overlay)', fontsize=12)
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path}")


def plot_summary_dashboard(sessions, output_path):
    """Create summary dashboard with key metrics."""
    print("[PLOT] Summary dashboard...")

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # 1. Overall metrics
    ax1 = axes[0, 0]
    bare_count = sum(1 for s in sessions if s.get("context_mode") == "bare_metal")
    iam_count = sum(1 for s in sessions if s.get("context_mode") == "i_am_only")
    total = len(sessions)
    unique_models = len(set(s.get("ship") for s in sessions))

    metrics_text = f"""
JADE LATTICE EXPERIMENT SUMMARY
================================
Total Sessions: {total}
Unique Models: {unique_models}

ARM Distribution:
  bare_metal (ARM A): {bare_count}
  i_am_only (ARM B): {iam_count}

Event Horizon Crossings: {sum(1 for s in sessions if s.get('summary', {}).get('event_horizon_crossed'))}

Providers: {', '.join(sorted(set(s.get('provider') for s in sessions)))}
"""
    ax1.text(0.05, 0.95, metrics_text, transform=ax1.transAxes, fontsize=10,
             verticalalignment='top', fontfamily='monospace')
    ax1.axis('off')

    # 2. Peak drift by arm (box plot)
    ax2 = axes[0, 1]
    bare_peaks = [s.get("summary", {}).get("peak_drift", 0)
                  for s in sessions if s.get("context_mode") == "bare_metal"]
    iam_peaks = [s.get("summary", {}).get("peak_drift", 0)
                 for s in sessions if s.get("context_mode") == "i_am_only"]

    bp = ax2.boxplot([bare_peaks, iam_peaks], patch_artist=True)
    bp['boxes'][0].set_facecolor(ARM_COLORS["bare_metal"])
    bp['boxes'][1].set_facecolor(ARM_COLORS["i_am_only"])
    ax2.set_xticklabels(['bare_metal', 'i_am_only'])
    ax2.set_ylabel('Peak Drift')
    ax2.set_title('Peak Drift by Arm')
    ax2.axhline(y=0.80, color='red', linestyle='--', alpha=0.5)

    # 3. Provider distribution
    ax3 = axes[1, 0]
    provider_counts = defaultdict(int)
    for s in sessions:
        provider_counts[s.get("provider", "unknown")] += 1

    providers = list(provider_counts.keys())
    counts = list(provider_counts.values())
    colors = [PROVIDER_COLORS.get(p, "#999999") for p in providers]

    ax3.bar(providers, counts, color=colors, alpha=0.8)
    ax3.set_ylabel('Session Count')
    ax3.set_title('Sessions by Provider')
    ax3.tick_params(axis='x', rotation=45)

    # 4. Prediction validation status
    # Updated based on CORRECTED paired analysis:
    # - P-JADE-6: I_AM wins 28/47 (60%), mean reduction 11% — PASS
    # - P-JADE-7: Cohen's d = 0.319 (0.353 filtered) — PASS
    ax4 = axes[1, 1]

    # Predictions with description, status, and result value
    predictions = [
        ("P-JADE-1", "Lambda capping <5%", True, "2.3%"),
        ("P-JADE-2", "AIC selects AR(2)", None, "Pending"),
        ("P-JADE-3", "EH = Re(s)≈0", None, "Pending"),
        ("P-JADE-4", "Repeatability", None, "Pending"),
        ("P-JADE-5", "Bandwidth limit", None, "Pending"),
        ("P-JADE-6", "I_AM more stable", True, "28/47 (60%)"),
        ("P-JADE-7", "Effect d>0.3", True, "d=0.319"),
    ]

    y_positions = range(len(predictions))
    colors_pred = []
    for _, _, status, _ in predictions:
        if status is True:
            colors_pred.append('green')
        elif status is False:
            colors_pred.append('red')
        else:
            colors_pred.append('gray')

    ax4.barh(y_positions, [1] * len(predictions), color=colors_pred, alpha=0.6)
    ax4.set_yticks(y_positions)
    ax4.set_yticklabels([f"{p}: {desc}" for p, desc, _, _ in predictions], fontsize=8)
    ax4.set_xlim(0, 1.8)
    ax4.set_title('Prediction Validation Status')
    ax4.tick_params(axis='x', which='both', bottom=False, labelbottom=False)

    # Add result values on the bars
    for i, (p_id, desc, status, result) in enumerate(predictions):
        color = 'white' if status is True else 'black'
        ax4.text(1.05, i, result, va='center', ha='left', fontsize=8, fontweight='bold', color=color)

    # Legend
    handles = [mpatches.Patch(color='green', label='PASS'),
               mpatches.Patch(color='red', label='FAIL'),
               mpatches.Patch(color='gray', label='PENDING')]
    ax4.legend(handles=handles, loc='lower right', fontsize=8)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path}")


def main():
    parser = argparse.ArgumentParser(description="JADE LATTICE Visualization")
    parser.add_argument("--plot", type=str, help="Specific plot to generate")
    parser.add_argument("--show", action="store_true", help="Show plots interactively")
    args = parser.parse_args()

    print("\n" + "=" * 60)
    print("JADE LATTICE VISUALIZATION")
    print("=" * 60)
    print(f"Time: {datetime.now().isoformat()}")

    # Create output directory
    PLOTS_DIR.mkdir(parents=True, exist_ok=True)

    # Load data
    sessions = load_jade_results()
    print(f"Loaded {len(sessions)} sessions")

    if not sessions:
        print("[ERROR] No sessions loaded")
        return

    # Generate plots
    plots = {
        "heatmap": (plot_provider_heatmap, "jade_provider_heatmap.png"),
        "ab_bars": (plot_ab_comparison_bars, "jade_ab_comparison_bars.png"),
        "forest": (plot_ab_effect_forest, "jade_ab_effect_forest.png"),
        "distribution": (plot_drift_distribution, "jade_drift_distribution.png"),
        "provider": (plot_provider_comparison, "jade_provider_comparison.png"),
        "trajectory": (plot_trajectory_overlay, "jade_trajectory_overlay.png"),
        "dashboard": (plot_summary_dashboard, "jade_summary_dashboard.png"),
    }

    if args.plot:
        if args.plot in plots:
            func, filename = plots[args.plot]
            func(sessions, PLOTS_DIR / filename)
        else:
            print(f"[ERROR] Unknown plot: {args.plot}")
            print(f"Available: {', '.join(plots.keys())}")
    else:
        # Generate all plots
        for name, (func, filename) in plots.items():
            try:
                func(sessions, PLOTS_DIR / filename)
            except Exception as e:
                print(f"  [ERROR] {name}: {e}")

    print("\n" + "=" * 60)
    print(f"PLOTS SAVED TO: {PLOTS_DIR}")
    print("=" * 60)


if __name__ == "__main__":
    main()
