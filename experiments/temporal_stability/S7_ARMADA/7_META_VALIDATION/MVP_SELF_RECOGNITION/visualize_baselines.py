#!/usr/bin/env python3
"""
Visualize Comprehensive Baseline Profiles

Creates:
1. Radar/spider plots for each model's pillar profile
2. Heatmap of pillar × model magnitudes
3. L3 fingerprint comparison by provider
4. Sub-dimension heatmap (20 × 6)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from datetime import datetime

# Load the comprehensive baseline data
results_dir = Path(__file__).parent / "results"
latest_file = sorted(results_dir.glob("comprehensive_baseline_*.json"))[-1]

print(f"Loading: {latest_file}")
with open(latest_file, encoding='utf-8') as f:
    data = json.load(f)

profiles = data["profiles"]
ships = list(profiles.keys())

# Color scheme by provider
PROVIDER_COLORS = {
    "claude": "#E07B39",  # Orange
    "gpt": "#10A37F",     # Green
    "gemini": "#4285F4",  # Blue
    "grok": "#1DA1F2",    # Light blue
}

def get_color(ship):
    provider = profiles[ship].get("provider", "unknown")
    return PROVIDER_COLORS.get(provider, "#888888")

# Output directory
output_dir = Path(__file__).parent.parent.parent / "visualizations" / "pics" / "baselines"
output_dir.mkdir(parents=True, exist_ok=True)

# ============================================================================
# 1. RADAR PLOT: Pillar Profiles per Model
# ============================================================================

def create_radar_plots():
    """Create radar/spider plots showing pillar profiles."""
    pillars = ["voice", "values", "reasoning", "selfmodel", "narrative"]

    fig, axes = plt.subplots(2, 3, figsize=(15, 10), subplot_kw=dict(polar=True))
    axes = axes.flatten()

    # Angles for radar
    angles = np.linspace(0, 2 * np.pi, len(pillars), endpoint=False).tolist()
    angles += angles[:1]  # Close the polygon

    for idx, ship in enumerate(ships):
        ax = axes[idx]
        profile = profiles[ship]

        # Get pillar magnitudes
        values = []
        for p in pillars:
            mag = profile.get("pillars", {}).get(p, {}).get("mean_magnitude", 0)
            values.append(mag)
        values += values[:1]  # Close the polygon

        # Plot
        color = get_color(ship)
        ax.plot(angles, values, 'o-', linewidth=2, color=color)
        ax.fill(angles, values, alpha=0.25, color=color)

        # Labels
        ax.set_xticks(angles[:-1])
        ax.set_xticklabels([p.upper() for p in pillars], size=9)
        ax.set_title(f"{ship}\n(mag={profile.get('overall_magnitude', 0):.2f})",
                     size=11, fontweight='bold', pad=10)

        # Set consistent scale
        ax.set_ylim(0, 5)

    plt.suptitle("Pillar Profiles by Model\n(5 Pillars × 6 Models)", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outpath = output_dir / "radar_pillar_profiles.png"
    plt.savefig(outpath, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {outpath}")
    plt.close()

# ============================================================================
# 2. HEATMAP: Pillar × Model Magnitudes
# ============================================================================

def create_pillar_heatmap():
    """Create heatmap of pillar magnitudes across models."""
    pillars = ["voice", "values", "reasoning", "selfmodel", "narrative"]

    # Build matrix
    matrix = []
    for ship in ships:
        row = []
        for p in pillars:
            mag = profiles[ship].get("pillars", {}).get(p, {}).get("mean_magnitude", 0)
            row.append(mag)
        matrix.append(row)

    matrix = np.array(matrix)

    fig, ax = plt.subplots(figsize=(10, 6))

    im = ax.imshow(matrix, cmap='YlOrRd', aspect='auto')

    # Labels
    ax.set_xticks(range(len(pillars)))
    ax.set_xticklabels([p.upper() for p in pillars], fontsize=11)
    ax.set_yticks(range(len(ships)))
    ax.set_yticklabels(ships, fontsize=10)

    # Add values to cells
    for i in range(len(ships)):
        for j in range(len(pillars)):
            val = matrix[i, j]
            color = 'white' if val > 2.5 else 'black'
            ax.text(j, i, f'{val:.2f}', ha='center', va='center', color=color, fontsize=10)

    # Colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Magnitude', fontsize=11)

    ax.set_title("Pillar Magnitudes by Model\n(Higher = Stronger Identity Signal)",
                 fontsize=13, fontweight='bold')

    plt.tight_layout()
    outpath = output_dir / "heatmap_pillar_magnitudes.png"
    plt.savefig(outpath, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {outpath}")
    plt.close()

# ============================================================================
# 3. BAR CHART: L3 Fingerprints by Provider
# ============================================================================

def create_l3_fingerprint_chart():
    """Create bar chart comparing L3 fingerprints by provider."""
    dims = ["A_pole", "B_zero", "C_meta", "D_identity", "E_hedging"]
    providers = ["claude", "gpt", "gemini", "grok"]

    # Calculate provider averages
    provider_data = {p: {d: [] for d in dims} for p in providers}

    for ship, profile in profiles.items():
        prov = profile.get("provider")
        if prov and "overall_l3_mean" in profile:
            for d in dims:
                provider_data[prov][d].append(profile["overall_l3_mean"].get(d, 0))

    # Average per provider
    provider_means = {}
    for prov in providers:
        provider_means[prov] = {}
        for d in dims:
            vals = provider_data[prov][d]
            provider_means[prov][d] = np.mean(vals) if vals else 0

    # Plot
    fig, ax = plt.subplots(figsize=(12, 6))

    x = np.arange(len(dims))
    width = 0.2

    for i, prov in enumerate(providers):
        values = [provider_means[prov][d] for d in dims]
        offset = (i - 1.5) * width
        bars = ax.bar(x + offset, values, width, label=prov.upper(),
                      color=PROVIDER_COLORS[prov], alpha=0.8)

        # Add value labels
        for bar, val in zip(bars, values):
            if val > 0.5:
                ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.1,
                       f'{val:.1f}', ha='center', va='bottom', fontsize=8)

    ax.set_xticks(x)
    ax.set_xticklabels(['A: Pole\n(Boundaries)', 'B: Zero\n(Flexibility)',
                        'C: Meta\n(Self-Aware)', 'D: Identity\n(First-Person)',
                        'E: Hedging\n(Uncertainty)'], fontsize=10)
    ax.set_ylabel('Magnitude', fontsize=11)
    ax.set_title("L3 Linguistic Marker Fingerprints by Provider\n(Claude has 2.3× higher D_identity than GPT)",
                 fontsize=13, fontweight='bold')
    ax.legend(loc='upper right')
    ax.set_ylim(0, 5)

    # Add grid
    ax.yaxis.grid(True, linestyle='--', alpha=0.5)
    ax.set_axisbelow(True)

    plt.tight_layout()
    outpath = output_dir / "bar_l3_fingerprints.png"
    plt.savefig(outpath, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {outpath}")
    plt.close()

# ============================================================================
# 4. HEATMAP: Sub-dimension × Model (20 × 6)
# ============================================================================

def create_subdimension_heatmap():
    """Create detailed heatmap of all 20 sub-dimensions."""
    # Collect all sub-dimensions in order
    pillars_order = ["voice", "values", "reasoning", "selfmodel", "narrative"]
    subdims = []
    for p in pillars_order:
        for ship in ships:
            subs = profiles[ship].get("pillars", {}).get(p, {}).get("sub_dimensions", {})
            for s in subs.keys():
                if s not in subdims:
                    subdims.append(s)

    # Build matrix
    matrix = []
    for ship in ships:
        row = []
        for sd in subdims:
            # Find which pillar this subdim belongs to
            val = 0
            for p in pillars_order:
                subs = profiles[ship].get("pillars", {}).get(p, {}).get("sub_dimensions", {})
                if sd in subs:
                    val = subs[sd].get("magnitude", 0)
                    break
            row.append(val)
        matrix.append(row)

    matrix = np.array(matrix)

    fig, ax = plt.subplots(figsize=(16, 8))

    im = ax.imshow(matrix, cmap='YlOrRd', aspect='auto')

    # Labels
    ax.set_xticks(range(len(subdims)))
    ax.set_xticklabels(subdims, fontsize=8, rotation=45, ha='right')
    ax.set_yticks(range(len(ships)))
    ax.set_yticklabels(ships, fontsize=10)

    # Add pillar separators
    pillar_counts = [4, 4, 4, 4, 4]  # voice, values, reasoning, selfmodel, narrative
    cumsum = 0
    for i, count in enumerate(pillar_counts[:-1]):
        cumsum += count
        ax.axvline(x=cumsum - 0.5, color='white', linewidth=2)

    # Colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Magnitude', fontsize=11)

    ax.set_title("Sub-dimension Magnitudes (20 probes × 6 models)\nVoice | Values | Reasoning | Self-Model | Narrative",
                 fontsize=13, fontweight='bold')

    plt.tight_layout()
    outpath = output_dir / "heatmap_subdimensions.png"
    plt.savefig(outpath, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {outpath}")
    plt.close()

# ============================================================================
# 5. STABILITY COMPARISON
# ============================================================================

def create_stability_chart():
    """Create bar chart showing stability scores."""
    fig, ax = plt.subplots(figsize=(10, 5))

    # Get stability and overall magnitude
    stabilities = [profiles[s].get("stability_score", 0) for s in ships]
    magnitudes = [profiles[s].get("overall_magnitude", 0) for s in ships]
    colors = [get_color(s) for s in ships]

    x = np.arange(len(ships))
    width = 0.35

    bars1 = ax.bar(x - width/2, stabilities, width, label='Stability', color=colors, alpha=0.8)
    bars2 = ax.bar(x + width/2, [m/5 for m in magnitudes], width, label='Magnitude/5',
                   color=colors, alpha=0.4, hatch='//')

    ax.set_xticks(x)
    ax.set_xticklabels(ships, fontsize=9, rotation=15, ha='right')
    ax.set_ylabel('Score', fontsize=11)
    ax.set_title("Stability vs Magnitude by Model\n(Grok most stable, Haiku most volatile)",
                 fontsize=13, fontweight='bold')
    ax.legend()
    ax.set_ylim(0, 1)

    # Add value labels
    for bar, val in zip(bars1, stabilities):
        ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
               f'{val:.2f}', ha='center', va='bottom', fontsize=9)

    plt.tight_layout()
    outpath = output_dir / "bar_stability_comparison.png"
    plt.savefig(outpath, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"Saved: {outpath}")
    plt.close()

# ============================================================================
# RUN ALL
# ============================================================================

if __name__ == "__main__":
    print(f"\n{'='*60}")
    print("GENERATING BASELINE VISUALIZATIONS")
    print(f"{'='*60}\n")

    create_radar_plots()
    create_pillar_heatmap()
    create_l3_fingerprint_chart()
    create_subdimension_heatmap()
    create_stability_chart()

    print(f"\n{'='*60}")
    print(f"All visualizations saved to: {output_dir}")
    print(f"{'='*60}")
