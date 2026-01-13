#!/usr/bin/env python3
"""
S8_gamma_visualization.py - Identity Gravity Visualization Suite

Generates publication-ready visualizations for S8 empirical results.

VISUALIZATIONS:
1. Provider gamma comparison (bar chart with error bars)
2. Force curve type distribution (stacked bar)
3. Gamma vs Settling Time scatter
4. Model-level gamma heatmap
5. Recovery trajectory samples (per force curve type)

Author: Claude + Nyquist
Date: 2026-01-11
"""

import json
import math
import os
from pathlib import Path
from collections import defaultdict

# Check for matplotlib
try:
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("WARNING: matplotlib not available. Install with: pip install matplotlib")

# ============================================================================
# CONFIGURATION
# ============================================================================

RESULTS_DIR = Path(__file__).parent / "results"
INPUT_FILE = RESULTS_DIR / "S8_gamma_analysis_CURRENT.json"
OUTPUT_DIR = Path(__file__).parent.parent.parent.parent.parent / "experiments" / "S8" / "visualizations"

# Provider colors (consistent with existing visualizations)
PROVIDER_COLORS = {
    'anthropic': '#D4A574',   # Claude tan
    'openai': '#74AA9C',      # GPT teal
    'google': '#4285F4',      # Google blue
    'xai': '#1DA1F2',         # Grok blue
    'together': '#FF6B6B',    # Together red
}

# Force curve colors
FORCE_CURVE_COLORS = {
    'I': '#2E7D32',    # Strong - dark green
    'II': '#7CB342',   # Moderate - light green
    'III': '#FFA726',  # Weak - orange
    'IV': '#EF5350',   # Very weak - red
    '0': '#9E9E9E',    # No recovery - gray
}

# ============================================================================
# VISUALIZATION FUNCTIONS
# ============================================================================

def plot_provider_gamma_comparison(data: dict, output_dir: Path):
    """Bar chart comparing gamma across providers."""
    if not HAS_MATPLOTLIB:
        return

    provider_stats = data['provider_stats']

    # Sort by gamma descending
    sorted_providers = sorted(provider_stats.items(), key=lambda x: x[1]['gamma_mean'], reverse=True)

    providers = [p[0] for p in sorted_providers]
    gammas = [p[1]['gamma_mean'] for p in sorted_providers]
    # Use Standard Error (std / sqrt(n)) instead of std for comparing means
    n_experiments = [p[1]['n_experiments'] for p in sorted_providers]
    stds = [p[1]['gamma_std'] for p in sorted_providers]
    std_errors = [s / math.sqrt(n) for s, n in zip(stds, n_experiments)]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    fig, ax = plt.subplots(figsize=(10, 6))

    bars = ax.bar(providers, gammas, yerr=std_errors, capsize=5, color=colors, edgecolor='black', linewidth=1.2)

    ax.set_ylabel('Identity Gravity (Zigs)', fontsize=12)
    ax.set_xlabel('Provider', fontsize=12)
    ax.set_title('S8: Identity Gravity by Provider\n(First Empirical Measurement of γ, error bars = SE)', fontsize=14, fontweight='bold')

    # Add value labels on bars
    for bar, gamma in zip(bars, gammas):
        height = bar.get_height()
        ax.annotate(f'{gamma:.1f}',
                    xy=(bar.get_x() + bar.get_width() / 2, height),
                    xytext=(0, 3),
                    textcoords="offset points",
                    ha='center', va='bottom', fontsize=10, fontweight='bold')

    # Add gravity ratio annotation
    ratio = max(gammas) / min(gammas)
    ax.annotate(f'Gravity Ratio: {ratio:.1f}x',
                xy=(0.95, 0.95), xycoords='axes fraction',
                fontsize=11, ha='right', va='top',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    ax.set_ylim(0, max(gammas) * 1.3)
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    output_path = output_dir / "S8_provider_gamma_comparison.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {output_path}")


def plot_force_curve_distribution(data: dict, output_dir: Path):
    """Stacked bar showing force curve type distribution by provider."""
    if not HAS_MATPLOTLIB:
        return

    provider_stats = data['provider_stats']

    # Get all providers and force curve types
    providers = sorted(provider_stats.keys())
    fc_types = ['I', 'II', 'III', 'IV', '0']

    fig, ax = plt.subplots(figsize=(10, 6))

    # Create stacked bars
    bottom = [0] * len(providers)
    for fc_type in fc_types:
        counts = []
        for provider in providers:
            dist = provider_stats[provider]['force_curve_distribution']
            n_total = provider_stats[provider]['n_experiments']
            count = dist.get(fc_type, 0)
            pct = (count / n_total * 100) if n_total > 0 else 0
            counts.append(pct)

        ax.bar(providers, counts, bottom=bottom, label=f'Type {fc_type}',
               color=FORCE_CURVE_COLORS[fc_type], edgecolor='white', linewidth=0.5)
        bottom = [b + c for b, c in zip(bottom, counts)]

    ax.set_ylabel('Percentage of Experiments', fontsize=12)
    ax.set_xlabel('Provider', fontsize=12)
    ax.set_title('S8: Force Curve Type Distribution by Provider\n(I=Strong Gravity, IV=Weak, 0=No Recovery)', fontsize=14, fontweight='bold')

    # Legend
    handles = [mpatches.Patch(color=FORCE_CURVE_COLORS[t], label=f'Type {t}') for t in fc_types]
    ax.legend(handles=handles, loc='upper right', fontsize=9)

    ax.set_ylim(0, 100)
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()
    output_path = output_dir / "S8_force_curve_distribution.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {output_path}")


def plot_gamma_vs_settling(data: dict, output_dir: Path):
    """Scatter plot of gamma vs settling time by provider."""
    if not HAS_MATPLOTLIB:
        return

    individual = data['individual_results']

    fig, ax = plt.subplots(figsize=(10, 8))

    for provider in PROVIDER_COLORS.keys():
        subset = [r for r in individual if r['provider'] == provider and r['gamma_zigs'] > 0]
        if not subset:
            continue

        gammas = [r['gamma_zigs'] for r in subset]
        settling = [r['settling_time'] for r in subset]

        ax.scatter(settling, gammas, c=PROVIDER_COLORS[provider], label=provider,
                   alpha=0.6, s=50, edgecolor='white', linewidth=0.5)

    ax.set_xlabel('Settling Time (probes)', fontsize=12)
    ax.set_ylabel('Identity Gravity (Zigs)', fontsize=12)
    ax.set_title('S8: Gamma vs Settling Time\n(Higher gamma = faster recovery)', fontsize=14, fontweight='bold')

    ax.legend(loc='upper right', fontsize=10)
    ax.grid(alpha=0.3)

    # Add theoretical prediction line: tau_s ~ ln(2) / gamma
    # Rearranged: gamma ~ ln(2) * 100 / tau_s (in Zigs)
    import numpy as np
    tau_range = np.linspace(1, 20, 100)
    gamma_theory = np.log(2) * 100 / tau_range
    ax.plot(tau_range, gamma_theory, 'k--', alpha=0.5, label='Theory: gamma = ln(2)/tau')

    plt.tight_layout()
    output_path = output_dir / "S8_gamma_vs_settling.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {output_path}")


def plot_model_gamma_heatmap(data: dict, output_dir: Path):
    """Heatmap of gamma values by model."""
    if not HAS_MATPLOTLIB:
        return

    model_stats = data['model_stats']

    # Sort by gamma
    sorted_models = sorted(model_stats.items(), key=lambda x: x[1]['gamma_mean'], reverse=True)

    # Truncate model names for display
    models = [m[0].split('/')[-1][:30] for m in sorted_models]
    gammas = [m[1]['gamma_mean'] for m in sorted_models]
    providers = [m[1]['provider'] for m in sorted_models]

    fig, ax = plt.subplots(figsize=(12, 10))

    # Create horizontal bar chart (easier to read model names)
    y_pos = range(len(models))
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    bars = ax.barh(y_pos, gammas, color=colors, edgecolor='black', linewidth=0.5)

    ax.set_yticks(y_pos)
    ax.set_yticklabels(models, fontsize=9)
    ax.set_xlabel('Identity Gravity (Zigs)', fontsize=12)
    ax.set_title('S8: Identity Gravity by Model\n(Ranked by gamma - Higher = Stronger Recovery)', fontsize=14, fontweight='bold')

    # Add provider legend
    handles = [mpatches.Patch(color=c, label=p) for p, c in PROVIDER_COLORS.items()]
    ax.legend(handles=handles, loc='lower right', fontsize=9)

    ax.grid(axis='x', alpha=0.3)
    ax.invert_yaxis()  # Highest gamma at top

    plt.tight_layout()
    output_path = output_dir / "S8_model_gamma_ranking.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {output_path}")


def plot_fleet_summary(data: dict, output_dir: Path):
    """Combined summary visualization."""
    if not HAS_MATPLOTLIB:
        return

    provider_stats = data['provider_stats']
    fc_dist = data['fleet_force_curve_distribution']

    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    # Panel 1: Gamma by provider
    ax1 = axes[0]
    sorted_providers = sorted(provider_stats.items(), key=lambda x: x[1]['gamma_mean'], reverse=True)
    providers = [p[0] for p in sorted_providers]
    gammas = [p[1]['gamma_mean'] for p in sorted_providers]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    ax1.bar(providers, gammas, color=colors, edgecolor='black')
    ax1.set_ylabel('Gamma (Zigs)')
    ax1.set_title('Identity Gravity\nby Provider')
    ax1.tick_params(axis='x', rotation=45)

    # Panel 2: Force curve distribution
    ax2 = axes[1]
    fc_types = ['I', 'II', 'III', 'IV', '0']
    fc_counts = [fc_dist.get(t, 0) for t in fc_types]
    fc_colors = [FORCE_CURVE_COLORS[t] for t in fc_types]

    ax2.pie(fc_counts, labels=[f'Type {t}' for t in fc_types], colors=fc_colors,
            autopct='%1.1f%%', startangle=90)
    ax2.set_title('Force Curve Type\nDistribution')

    # Panel 3: Key metrics table
    ax3 = axes[2]
    ax3.axis('off')

    # Calculate fleet-wide stats
    all_gammas = [r['gamma_zigs'] for r in data['individual_results'] if r['gamma_zigs'] > 0]
    fleet_mean = sum(all_gammas) / len(all_gammas) if all_gammas else 0
    fleet_median = sorted(all_gammas)[len(all_gammas)//2] if all_gammas else 0

    table_data = [
        ['Metric', 'Value'],
        ['Total Experiments', str(data['total_experiments'])],
        ['Fleet Mean Gamma', f'{fleet_mean:.1f} Zigs'],
        ['Fleet Median Gamma', f'{fleet_median:.1f} Zigs'],
        ['Strongest Provider', f"{sorted_providers[0][0]} ({sorted_providers[0][1]['gamma_mean']:.1f})"],
        ['Weakest Provider', f"{sorted_providers[-1][0]} ({sorted_providers[-1][1]['gamma_mean']:.1f})"],
        ['Gravity Ratio', f'{gammas[0]/gammas[-1]:.1f}x'],
        ['Type I (Strong)', f"{fc_dist.get('I', 0)} ({fc_dist.get('I', 0)/data['total_experiments']*100:.1f}%)"],
        ['Type 0 (No Recovery)', f"{fc_dist.get('0', 0)} ({fc_dist.get('0', 0)/data['total_experiments']*100:.1f}%)"],
    ]

    table = ax3.table(cellText=table_data, cellLoc='left', loc='center',
                      colWidths=[0.4, 0.6])
    table.auto_set_font_size(False)
    table.set_fontsize(10)
    table.scale(1.2, 1.5)

    # Header row styling
    for i in range(2):
        table[(0, i)].set_facecolor('#E0E0E0')
        table[(0, i)].set_text_props(fontweight='bold')

    ax3.set_title('Fleet Summary', fontsize=12, fontweight='bold', pad=20)

    plt.suptitle('S8: Identity Gravity - First Empirical Measurement\n(N=750 experiments, Run 023d)',
                 fontsize=14, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = output_dir / "S8_fleet_summary.png"
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {output_path}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 70)
    print("S8 IDENTITY GRAVITY - VISUALIZATION SUITE")
    print("=" * 70)
    print()

    # Load data
    print(f"Loading: {INPUT_FILE}")
    with open(INPUT_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    print(f"Loaded {data['total_experiments']} experiment results")
    print()

    # Create output directory
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    print(f"Output directory: {OUTPUT_DIR}")
    print()

    if not HAS_MATPLOTLIB:
        print("ERROR: matplotlib required for visualizations")
        print("Install with: pip install matplotlib")
        return

    # Generate visualizations
    print("Generating visualizations...")
    print()

    plot_provider_gamma_comparison(data, OUTPUT_DIR)
    plot_force_curve_distribution(data, OUTPUT_DIR)
    plot_gamma_vs_settling(data, OUTPUT_DIR)
    plot_model_gamma_heatmap(data, OUTPUT_DIR)
    plot_fleet_summary(data, OUTPUT_DIR)

    print()
    print("=" * 70)
    print("VISUALIZATION COMPLETE")
    print("=" * 70)
    print()
    print(f"Output files in: {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
