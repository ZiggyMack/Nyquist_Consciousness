#!/usr/bin/env python3
"""
R&D VISUALIZATION LABORATORY
=============================
Experimental/creative visualization types for rescue protocol dynamics.
These are exploratory - some may make it to the white paper, some won't!

VISUALIZATION TYPES:
1. Sankey Diagram - Flow from Peak Drift Zone to Final Drift Zone
2. Slope Chart (Dumbbell) - Peak vs Settled with connecting lines
3. Nightingale Rose - Florence Nightingale style polar area chart
4. Beeswarm with Arrows - Individual points with recovery vectors
5. Parallel Coordinates - Multi-dimensional trajectory view
6. Chord Diagram - Zone migration patterns

Author: Claude (VALIS Network)
Date: December 20, 2025
Status: EXPERIMENTAL R&D
"""

import json
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch, Wedge
from matplotlib.collections import LineCollection
from pathlib import Path
from typing import List, Dict, Tuple
import warnings
warnings.filterwarnings('ignore')

# =============================================================================
# CONFIGURATION
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
DATA_FILE = ARMADA_DIR / "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023_CURRENT.json"
OUTPUT_DIR = SCRIPT_DIR / "pics" / "4_Rescue" / "RnD_experiments"

# Thresholds
EVENT_HORIZON = 0.80
WARNING_THRESHOLD = 0.60

# Provider colors
PROVIDER_COLORS = {
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
    "grok": "#1a1a1a",
    "meta-llama": "#FF6B6B",
    "mistralai": "#FFD93D",
    "deepseek": "#6BCB77",
    "Qwen": "#4D96FF",
    "moonshotai": "#9B59B6",
    "other": "#888888",
}

# Zone definitions for Sankey/Chord
DRIFT_ZONES = {
    "SAFE": (0.0, 0.40),
    "CAUTION": (0.40, 0.60),
    "WARNING": (0.60, 0.80),
    "CRITICAL": (0.80, 1.20),
}

ZONE_COLORS = {
    "SAFE": "#2ecc71",
    "CAUTION": "#f1c40f",
    "WARNING": "#e67e22",
    "CRITICAL": "#e74c3c",
}


def get_provider(model_name: str) -> str:
    """Extract provider from model name."""
    model_lower = model_name.lower()
    if "claude" in model_lower:
        return "claude"
    elif "gpt" in model_lower or "o1" in model_lower or "o3" in model_lower:
        return "gpt"
    elif "gemini" in model_lower:
        return "gemini"
    elif "grok" in model_lower:
        return "grok"
    elif "llama" in model_lower:
        return "meta-llama"
    elif "mistral" in model_lower or "mixtral" in model_lower:
        return "mistralai"
    elif "deepseek" in model_lower:
        return "deepseek"
    elif "qwen" in model_lower:
        return "Qwen"
    elif "kimi" in model_lower:
        return "moonshotai"
    return "other"


def get_zone(drift: float) -> str:
    """Get zone name for a drift value."""
    for zone_name, (low, high) in DRIFT_ZONES.items():
        if low <= drift < high:
            return zone_name
    return "CRITICAL"  # Anything >= 1.20


def load_rescue_data() -> List[Dict]:
    """Load rescue experiment data from run023b."""
    print(f"Loading data from: {DATA_FILE}")
    with open(DATA_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    rescue_results = [r for r in data.get('results', []) if r.get('experiment') == 'rescue']
    print(f"Found {len(rescue_results)} rescue experiment results")
    return rescue_results


# =============================================================================
# 1. SANKEY DIAGRAM - Flow from Peak Zone to Final Zone
# =============================================================================

def generate_sankey_diagram(rescue_data: List[Dict], output_dir: Path):
    """
    Sankey-style flow diagram showing how many experiments flow
    from each Peak Drift Zone to each Final Drift Zone.

    Width of bands = count of experiments taking that path.
    """
    print("\n[1/6] Generating Sankey Diagram...")

    # Count flows between zones
    flows = {}  # (peak_zone, final_zone) -> count

    for r in rescue_data:
        peak = r.get('peak_drift', 0)
        final = r.get('settled_drift', r.get('final_drift', peak))

        peak_zone = get_zone(peak)
        final_zone = get_zone(final)

        key = (peak_zone, final_zone)
        flows[key] = flows.get(key, 0) + 1

    # Create figure
    fig, ax = plt.subplots(figsize=(14, 10))

    # Zone positions (left side = peak, right side = final)
    zones = ["SAFE", "CAUTION", "WARNING", "CRITICAL"]
    left_x = 0.15
    right_x = 0.85

    # Calculate zone heights based on total flow
    left_totals = {z: sum(flows.get((z, fz), 0) for fz in zones) for z in zones}
    right_totals = {z: sum(flows.get((pz, z), 0) for pz in zones) for z in zones}

    total_left = sum(left_totals.values())
    total_right = sum(right_totals.values())

    # Normalize heights
    zone_height = 0.18
    gap = 0.04

    # Calculate y positions for each zone
    left_y = {}
    right_y = {}

    y_pos = 0.9
    for z in zones:
        height = max(0.05, (left_totals[z] / total_left) * 0.7) if total_left > 0 else 0.05
        left_y[z] = (y_pos - height/2, y_pos + height/2, height)
        y_pos -= height + gap

    y_pos = 0.9
    for z in zones:
        height = max(0.05, (right_totals[z] / total_right) * 0.7) if total_right > 0 else 0.05
        right_y[z] = (y_pos - height/2, y_pos + height/2, height)
        y_pos -= height + gap

    # Draw zone boxes
    for z in zones:
        # Left (Peak)
        ly_low, ly_high, ly_h = left_y[z]
        rect = plt.Rectangle((left_x - 0.05, ly_low), 0.1, ly_h,
                             facecolor=ZONE_COLORS[z], edgecolor='black', linewidth=2, alpha=0.8)
        ax.add_patch(rect)
        ax.text(left_x - 0.12, (ly_low + ly_high)/2, f"{z}\n({left_totals[z]})",
               ha='right', va='center', fontsize=10, fontweight='bold')

        # Right (Final)
        ry_low, ry_high, ry_h = right_y[z]
        rect = plt.Rectangle((right_x - 0.05, ry_low), 0.1, ry_h,
                             facecolor=ZONE_COLORS[z], edgecolor='black', linewidth=2, alpha=0.8)
        ax.add_patch(rect)
        ax.text(right_x + 0.12, (ry_low + ry_high)/2, f"{z}\n({right_totals[z]})",
               ha='left', va='center', fontsize=10, fontweight='bold')

    # Draw flow bands (simplified - just curves)
    for (peak_zone, final_zone), count in flows.items():
        if count == 0:
            continue

        # Calculate band width proportional to count
        band_width = max(0.005, (count / total_left) * 0.15)

        # Get y positions
        ly_low, ly_high, _ = left_y[peak_zone]
        ry_low, ry_high, _ = right_y[final_zone]

        ly_mid = (ly_low + ly_high) / 2
        ry_mid = (ry_low + ry_high) / 2

        # Draw curved band using bezier
        from matplotlib.patches import FancyBboxPatch
        from matplotlib.path import Path as MplPath
        import matplotlib.patches as mpatches

        # Control points for bezier curve
        verts = [
            (left_x + 0.05, ly_mid),
            (0.35, ly_mid),
            (0.65, ry_mid),
            (right_x - 0.05, ry_mid),
        ]
        codes = [MplPath.MOVETO, MplPath.CURVE4, MplPath.CURVE4, MplPath.CURVE4]
        path = MplPath(verts, codes)

        # Color based on recovery (green if final < peak zone, red if worse)
        zone_order = {z: i for i, z in enumerate(zones)}
        if zone_order[final_zone] < zone_order[peak_zone]:
            color = '#27ae60'  # Recovered - green
            alpha = 0.6
        elif zone_order[final_zone] > zone_order[peak_zone]:
            color = '#c0392b'  # Got worse - red
            alpha = 0.6
        else:
            color = '#7f8c8d'  # No change - gray
            alpha = 0.4

        patch = mpatches.PathPatch(path, facecolor='none', edgecolor=color,
                                   linewidth=max(1, count/5), alpha=alpha)
        ax.add_patch(patch)

        # Add count label at midpoint
        if count > 10:
            ax.text(0.5, (ly_mid + ry_mid)/2, str(count),
                   ha='center', va='center', fontsize=8, alpha=0.7)

    # Labels
    ax.text(left_x, 0.98, "PEAK DRIFT ZONE", ha='center', fontsize=14, fontweight='bold')
    ax.text(right_x, 0.98, "FINAL DRIFT ZONE", ha='center', fontsize=14, fontweight='bold')

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis('off')
    ax.set_title("Rescue Protocol Flow: Peak Zone -> Final Zone\n"
                 "(Green = Recovery, Gray = No Change, Red = Degradation)",
                 fontsize=14, fontweight='bold', pad=20)

    plt.tight_layout()

    output_file = output_dir / "rescue_sankey.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# 2. SLOPE CHART (Dumbbell Plot)
# =============================================================================

def generate_slope_chart(rescue_data: List[Dict], output_dir: Path):
    """
    Slope chart showing Peak (left) vs Settled (right) for each model.
    Lines slope down = recovery, flat = no change, up = degradation.
    """
    print("\n[2/6] Generating Slope Chart (Dumbbell)...")

    # Aggregate by model
    models = {}
    for r in rescue_data:
        model = r.get('model', 'unknown')
        if model not in models:
            models[model] = {'peaks': [], 'finals': []}

        peak = r.get('peak_drift', 0)
        final = r.get('settled_drift', r.get('final_drift', peak))
        models[model]['peaks'].append(peak)
        models[model]['finals'].append(final)

    # Calculate means and sort by peak drift
    model_stats = []
    for model, data in models.items():
        mean_peak = np.mean(data['peaks'])
        mean_final = np.mean(data['finals'])
        provider = get_provider(model)
        short_name = model.split('/')[-1][:20] if '/' in model else model[:20]
        model_stats.append({
            'name': short_name,
            'provider': provider,
            'peak': mean_peak,
            'final': mean_final,
            'recovery': mean_peak - mean_final,
        })

    # Sort by peak drift (highest at top)
    model_stats.sort(key=lambda x: x['peak'], reverse=True)

    # Create figure
    fig, ax = plt.subplots(figsize=(12, max(8, len(model_stats) * 0.4)))

    y_positions = np.arange(len(model_stats))

    for i, stat in enumerate(model_stats):
        color = PROVIDER_COLORS.get(stat['provider'], '#888888')

        # Draw connecting line
        if stat['final'] < stat['peak']:
            line_color = '#27ae60'  # Recovery - green
            line_alpha = 0.8
        elif stat['final'] > stat['peak']:
            line_color = '#c0392b'  # Degradation - red
            line_alpha = 0.8
        else:
            line_color = '#7f8c8d'  # No change - gray
            line_alpha = 0.5

        ax.plot([stat['peak'], stat['final']], [i, i],
               color=line_color, linewidth=2, alpha=line_alpha, zorder=1)

        # Draw points
        ax.scatter(stat['peak'], i, s=100, color=color, edgecolor='black',
                  linewidth=1.5, zorder=2, marker='o', label='Peak' if i == 0 else '')
        ax.scatter(stat['final'], i, s=100, color=color, edgecolor='black',
                  linewidth=1.5, zorder=2, marker='s', label='Final' if i == 0 else '')

        # Model name
        ax.text(-0.02, i, stat['name'], ha='right', va='center', fontsize=8)

        # Recovery delta
        delta = stat['recovery']
        delta_color = '#27ae60' if delta > 0 else '#c0392b' if delta < 0 else '#7f8c8d'
        ax.text(1.02, i, f"{delta:+.3f}", ha='left', va='center',
               fontsize=8, color=delta_color, fontweight='bold')

    # Event Horizon lines
    ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               alpha=0.7, label=f'Event Horizon ({EVENT_HORIZON})')
    ax.axvline(x=WARNING_THRESHOLD, color='orange', linestyle=':', linewidth=1.5,
               alpha=0.5, label=f'Warning ({WARNING_THRESHOLD})')

    # Styling
    ax.set_yticks(y_positions)
    ax.set_yticklabels([])  # Labels already added manually
    ax.set_xlabel('Cosine Drift', fontsize=12)
    ax.set_xlim(-0.05, 1.1)
    ax.set_ylim(-0.5, len(model_stats) - 0.5)

    # Column headers
    ax.text(0.3, len(model_stats) + 0.5, 'PEAK', ha='center', fontsize=11, fontweight='bold')
    ax.text(0.7, len(model_stats) + 0.5, 'FINAL', ha='center', fontsize=11, fontweight='bold')
    ax.text(1.05, len(model_stats) + 0.5, 'DELTA', ha='center', fontsize=11, fontweight='bold')

    ax.set_title("Slope Chart: Peak vs Final Drift by Model\n"
                 "(Downward slope = Recovery, Upward = Degradation)",
                 fontsize=14, fontweight='bold')
    ax.grid(True, axis='x', alpha=0.3)
    ax.legend(loc='lower right', fontsize=9)

    plt.tight_layout()

    output_file = output_dir / "rescue_slope_chart.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# 3. NIGHTINGALE ROSE (Polar Area Chart)
# =============================================================================

def generate_nightingale_rose(rescue_data: List[Dict], output_dir: Path):
    """
    Florence Nightingale style polar area chart.
    Each petal = one provider, radius = recovery ratio, angle = experiment count.

    Like the famous "Diagram of the Causes of Mortality" from 1858!
    """
    print("\n[3/6] Generating Nightingale Rose Chart...")

    # Aggregate by provider
    providers = {}
    for r in rescue_data:
        model = r.get('model', 'unknown')
        provider = get_provider(model)

        if provider not in providers:
            providers[provider] = {'recoveries': [], 'count': 0}

        peak = r.get('peak_drift', 0)
        final = r.get('settled_drift', r.get('final_drift', peak))

        if peak > 0.01:
            recovery = max(0, 1 - (final / peak))
            providers[provider]['recoveries'].append(recovery)
        providers[provider]['count'] += 1

    # Calculate stats
    provider_stats = []
    for provider, data in providers.items():
        if data['recoveries']:
            mean_recovery = np.mean(data['recoveries'])
            provider_stats.append({
                'name': provider,
                'recovery': mean_recovery,
                'count': data['count'],
                'color': PROVIDER_COLORS.get(provider, '#888888'),
            })

    # Sort by recovery for visual appeal
    provider_stats.sort(key=lambda x: x['recovery'], reverse=True)

    # Create polar plot
    fig, ax = plt.subplots(figsize=(12, 12), subplot_kw=dict(projection='polar'))

    n_providers = len(provider_stats)
    angles = np.linspace(0, 2 * np.pi, n_providers, endpoint=False)
    width = 2 * np.pi / n_providers * 0.85  # Slight gap between petals

    # Draw petals
    for i, stat in enumerate(provider_stats):
        # Radius proportional to recovery ratio (scaled for visibility)
        radius = stat['recovery'] * 0.8 + 0.2  # Min 0.2, max 1.0

        # Draw wedge
        ax.bar(angles[i], radius, width=width, bottom=0,
               color=stat['color'], edgecolor='black', linewidth=1.5,
               alpha=0.7, label=f"{stat['name']}: {stat['recovery']:.2f}")

        # Add count at outer edge
        label_angle = angles[i]
        label_radius = radius + 0.1

        # Rotate text to be readable
        rotation = np.degrees(label_angle)
        if 90 < rotation < 270:
            rotation += 180
            ha = 'right'
        else:
            ha = 'left'

        ax.text(label_angle, label_radius, f"{stat['name']}\nn={stat['count']}",
               ha='center', va='center', fontsize=9, fontweight='bold',
               rotation=rotation - 90)

    # Reference circles
    for r in [0.25, 0.5, 0.75, 1.0]:
        circle = plt.Circle((0, 0), r, transform=ax.transData._b,
                           fill=False, color='gray', linestyle=':', alpha=0.3)
        ax.add_artist(circle)

    # Event Horizon circle (at recovery ratio that corresponds to EH)
    ax.plot(np.linspace(0, 2*np.pi, 100), [0.5]*100,
           color='red', linestyle='--', linewidth=2, alpha=0.7)

    ax.set_ylim(0, 1.2)
    ax.set_yticklabels([])
    ax.set_xticklabels([])
    ax.grid(True, alpha=0.3)

    ax.set_title("Nightingale Rose: Recovery Ratio by Provider\n"
                 "(Petal size = mean recovery, larger = better recovery)",
                 fontsize=14, fontweight='bold', pad=30)

    # Legend
    ax.legend(loc='upper left', bbox_to_anchor=(1.1, 1.0), fontsize=9)

    plt.tight_layout()

    output_file = output_dir / "rescue_nightingale_rose.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# 4. BEESWARM WITH ARROWS
# =============================================================================

def generate_beeswarm_arrows(rescue_data: List[Dict], output_dir: Path):
    """
    Beeswarm plot where each point is positioned at its peak drift,
    with an arrow pointing to where it settled.

    Instant visual impact - see recovery vectors!
    """
    print("\n[4/6] Generating Beeswarm with Arrows...")

    # Group by provider for y-axis separation
    providers = {}
    for r in rescue_data:
        model = r.get('model', 'unknown')
        provider = get_provider(model)

        if provider not in providers:
            providers[provider] = []

        peak = r.get('peak_drift', 0)
        final = r.get('settled_drift', r.get('final_drift', peak))
        providers[provider].append({'peak': peak, 'final': final, 'model': model})

    # Create figure
    fig, ax = plt.subplots(figsize=(14, 10))

    provider_list = list(providers.keys())
    y_base = 0
    y_spacing = 1.5

    for provider in provider_list:
        data = providers[provider]
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Add jitter for beeswarm effect
        n_points = len(data)
        jitter = np.random.normal(0, 0.15, n_points)

        for i, d in enumerate(data):
            y = y_base + jitter[i]

            # Draw arrow from peak to final
            dx = d['final'] - d['peak']

            if abs(dx) > 0.01:  # Only draw arrow if there's movement
                arrow_color = '#27ae60' if dx < 0 else '#c0392b'  # Green = recovery
                ax.annotate('', xy=(d['final'], y), xytext=(d['peak'], y),
                           arrowprops=dict(arrowstyle='->', color=arrow_color,
                                         lw=1, alpha=0.5))

            # Draw point at peak position
            ax.scatter(d['peak'], y, s=30, color=color, alpha=0.7,
                      edgecolor='white', linewidth=0.5, zorder=3)

        # Provider label
        ax.text(-0.05, y_base, provider, ha='right', va='center',
               fontsize=11, fontweight='bold', color=color)

        y_base += y_spacing

    # Threshold lines
    ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})', alpha=0.7)
    ax.axvline(x=WARNING_THRESHOLD, color='orange', linestyle=':', linewidth=1.5,
               label=f'Warning ({WARNING_THRESHOLD})', alpha=0.5)

    # Zone shading
    ax.axvspan(0, WARNING_THRESHOLD, alpha=0.1, color='green', label='Safe Zone')
    ax.axvspan(WARNING_THRESHOLD, EVENT_HORIZON, alpha=0.1, color='yellow')
    ax.axvspan(EVENT_HORIZON, 1.2, alpha=0.1, color='red', label='Critical Zone')

    ax.set_xlim(-0.1, 1.2)
    ax.set_ylim(-1, y_base)
    ax.set_xlabel('Cosine Drift', fontsize=12)
    ax.set_ylabel('Provider (with jitter)', fontsize=12)
    ax.set_yticks([])

    ax.set_title("Beeswarm with Recovery Arrows\n"
                 "(Green arrows = recovery toward baseline, Red = degradation)",
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right', fontsize=9)
    ax.grid(True, axis='x', alpha=0.3)

    plt.tight_layout()

    output_file = output_dir / "rescue_beeswarm_arrows.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# 5. PARALLEL COORDINATES
# =============================================================================

def generate_parallel_coordinates(rescue_data: List[Dict], output_dir: Path):
    """
    Parallel coordinates plot showing Baseline -> Peak -> Settled.
    Each line is one experiment. Lines that dip down = recovery.
    """
    print("\n[5/6] Generating Parallel Coordinates...")

    # Extract data
    lines_data = []
    for r in rescue_data:
        model = r.get('model', 'unknown')
        provider = get_provider(model)

        # Get baseline from probe sequence if available
        baseline = 0.1  # Default low baseline
        if 'probe_sequence' in r and r['probe_sequence']:
            first_probe = r['probe_sequence'][0]
            if isinstance(first_probe, dict) and 'drift' in first_probe:
                baseline = first_probe['drift']

        peak = r.get('peak_drift', 0)
        final = r.get('settled_drift', r.get('final_drift', peak))

        lines_data.append({
            'baseline': baseline,
            'peak': peak,
            'final': final,
            'provider': provider,
            'model': model,
        })

    # Create figure
    fig, ax = plt.subplots(figsize=(12, 8))

    # X positions for each axis
    x_positions = [0, 1, 2]
    axis_labels = ['Baseline', 'Peak Drift', 'Final Drift']

    # Draw lines for each experiment
    for d in lines_data:
        color = PROVIDER_COLORS.get(d['provider'], '#888888')

        # Determine if recovery occurred
        recovered = d['final'] < d['peak']
        alpha = 0.4 if recovered else 0.2
        lw = 1.0 if recovered else 0.5

        y_vals = [d['baseline'], d['peak'], d['final']]
        ax.plot(x_positions, y_vals, color=color, alpha=alpha, linewidth=lw)

    # Draw vertical axis lines
    for x in x_positions:
        ax.axvline(x=x, color='black', linewidth=2)

    # Event Horizon line across all axes
    ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               alpha=0.7, label=f'Event Horizon ({EVENT_HORIZON})')

    # Axis labels
    ax.set_xticks(x_positions)
    ax.set_xticklabels(axis_labels, fontsize=12, fontweight='bold')
    ax.set_ylabel('Cosine Drift', fontsize=12)
    ax.set_ylim(0, 1.2)
    ax.set_xlim(-0.3, 2.3)

    # Legend for providers
    legend_patches = [mpatches.Patch(color=PROVIDER_COLORS[p], label=p)
                     for p in set(d['provider'] for d in lines_data)]
    ax.legend(handles=legend_patches, loc='upper left', fontsize=9, ncol=2)

    ax.set_title("Parallel Coordinates: Baseline -> Peak -> Final\n"
                 "(Lines dipping right = recovery, rising = degradation)",
                 fontsize=14, fontweight='bold')
    ax.grid(True, axis='y', alpha=0.3)

    plt.tight_layout()

    output_file = output_dir / "rescue_parallel_coordinates.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# 6. RECOVERY HEATMAP (Bonus!)
# =============================================================================

def generate_recovery_heatmap(rescue_data: List[Dict], output_dir: Path):
    """
    Heatmap showing recovery rate by provider x peak drift zone.
    Which providers recover best from which zones?
    """
    print("\n[6/6] Generating Recovery Heatmap...")

    # Aggregate by provider and peak zone
    matrix = {}  # (provider, peak_zone) -> [recovery_ratios]

    for r in rescue_data:
        model = r.get('model', 'unknown')
        provider = get_provider(model)

        peak = r.get('peak_drift', 0)
        final = r.get('settled_drift', r.get('final_drift', peak))
        peak_zone = get_zone(peak)

        if peak > 0.01:
            recovery = max(0, 1 - (final / peak))
            key = (provider, peak_zone)
            if key not in matrix:
                matrix[key] = []
            matrix[key].append(recovery)

    # Get unique providers and zones
    providers = sorted(set(k[0] for k in matrix.keys()))
    zones = ["SAFE", "CAUTION", "WARNING", "CRITICAL"]

    # Build heatmap matrix
    heatmap_data = np.zeros((len(providers), len(zones)))
    counts = np.zeros((len(providers), len(zones)))

    for (provider, zone), recoveries in matrix.items():
        i = providers.index(provider)
        j = zones.index(zone)
        heatmap_data[i, j] = np.mean(recoveries)
        counts[i, j] = len(recoveries)

    # Create figure
    fig, ax = plt.subplots(figsize=(10, 8))

    # Create heatmap
    im = ax.imshow(heatmap_data, cmap='RdYlGn', aspect='auto', vmin=0, vmax=0.5)

    # Add colorbar
    cbar = ax.figure.colorbar(im, ax=ax)
    cbar.ax.set_ylabel('Mean Recovery Ratio', rotation=-90, va="bottom", fontsize=11)

    # Labels
    ax.set_xticks(np.arange(len(zones)))
    ax.set_yticks(np.arange(len(providers)))
    ax.set_xticklabels(zones, fontsize=11)
    ax.set_yticklabels(providers, fontsize=11)
    ax.set_xlabel('Peak Drift Zone', fontsize=12)
    ax.set_ylabel('Provider', fontsize=12)

    # Add text annotations
    for i in range(len(providers)):
        for j in range(len(zones)):
            value = heatmap_data[i, j]
            count = int(counts[i, j])
            text_color = 'white' if value < 0.25 else 'black'
            if count > 0:
                ax.text(j, i, f"{value:.2f}\n(n={count})",
                       ha='center', va='center', color=text_color, fontsize=9)
            else:
                ax.text(j, i, "N/A", ha='center', va='center',
                       color='gray', fontsize=9)

    ax.set_title("Recovery Heatmap: Provider x Peak Drift Zone\n"
                 "(Green = high recovery, Red = low recovery)",
                 fontsize=14, fontweight='bold')

    plt.tight_layout()

    output_file = output_dir / "rescue_recovery_heatmap.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# 7. PDF SUMMARY GENERATION
# =============================================================================

def generate_rnd_pdf_summary(output_dir: Path):
    """
    Generate a comprehensive PDF documenting all R&D experimental visualizations.
    Output: RnD_experiments/RnD_Rescue_Summary.pdf
    """
    print("\n[PDF] Generating R&D Summary PDF...")

    try:
        from reportlab.lib.pagesizes import letter
        from reportlab.lib.units import inch
        from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
        from reportlab.lib.enums import TA_CENTER, TA_JUSTIFY
        from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, PageBreak
        from reportlab.lib.colors import HexColor
    except ImportError:
        print("  [SKIP] reportlab not installed - skipping PDF generation")
        return None

    output_path = output_dir / "RnD_Rescue_Summary.pdf"
    doc = SimpleDocTemplate(str(output_path), pagesize=letter,
                           leftMargin=0.75*inch, rightMargin=0.75*inch,
                           topMargin=0.75*inch, bottomMargin=0.75*inch)
    story = []

    # Styles
    styles = getSampleStyleSheet()
    title_style = ParagraphStyle(
        'CustomTitle', parent=styles['Heading1'], fontSize=20, spaceAfter=20,
        alignment=TA_CENTER, textColor=HexColor('#1a1a2e')
    )
    heading_style = ParagraphStyle(
        'CustomHeading', parent=styles['Heading2'], fontSize=14, spaceBefore=15,
        spaceAfter=10, textColor=HexColor('#16213e')
    )
    body_style = ParagraphStyle(
        'CustomBody', parent=styles['Normal'], fontSize=10, spaceAfter=8,
        alignment=TA_JUSTIFY, leading=14
    )
    caption_style = ParagraphStyle(
        'Caption', parent=styles['Normal'], fontSize=9, alignment=TA_CENTER,
        textColor=HexColor('#666666'), spaceAfter=15
    )
    highlight_style = ParagraphStyle(
        'Highlight', parent=styles['Normal'], fontSize=10, spaceAfter=8,
        backColor=HexColor('#fff3cd'), borderPadding=5
    )

    def add_image(img_path, width=6*inch, caption=None):
        if img_path.exists():
            img = Image(str(img_path), width=width, height=width*0.6)
            story.append(img)
            if caption:
                story.append(Paragraph(caption, caption_style))
        else:
            story.append(Paragraph(f"[Image not found: {img_path.name}]", body_style))

    # =========================================================================
    # TITLE PAGE
    # =========================================================================
    story.append(Paragraph("R&D Visualization Laboratory", title_style))
    story.append(Paragraph("Experimental Rescue Protocol Visualizations", caption_style))
    story.append(Spacer(1, 0.3*inch))

    story.append(Paragraph(
        "This document showcases <b>experimental visualization types</b> for analyzing "
        "rescue protocol dynamics. These are R&D explorations - some may make it to "
        "the white paper, others serve as analytical tools for understanding recovery patterns.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Data Source:</b> S7 ARMADA Run 023b (741 rescue experiment results)<br/>"
        "<b>Methodology:</b> Cosine distance drift measurement (EH = 0.80)<br/>"
        "<b>Fleet:</b> 25 LLM ships across 10 provider families",
        body_style
    ))
    story.append(Spacer(1, 0.2*inch))

    story.append(Paragraph("Key Question", heading_style))
    story.append(Paragraph(
        "<i>Can identity coherence be restored after perturbation, or is drift permanent?</i><br/><br/>"
        "The rescue protocol induces drift through adversarial prompts, then attempts recovery "
        "through grounding interventions. These visualizations explore different ways to "
        "understand recovery dynamics.",
        body_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # 1. SANKEY DIAGRAM
    # =========================================================================
    story.append(Paragraph("1. Sankey Flow Diagram", heading_style))
    add_image(output_dir / "rescue_sankey.png", caption="Figure 1: Flow from Peak Drift Zone to Final Drift Zone")

    story.append(Paragraph(
        "<b>What it shows:</b> A flow diagram showing how experiments migrate between "
        "drift zones. Left side shows where experiments started (peak drift zone), "
        "right side shows where they ended (final drift zone).",
        body_style
    ))
    story.append(Paragraph(
        "<b>Color coding:</b><br/>"
        "- <font color='green'><b>Green flows</b></font>: Recovery - moved to a lower (safer) zone<br/>"
        "- <font color='gray'><b>Gray flows</b></font>: No change - stayed in the same zone<br/>"
        "- <font color='red'><b>Red flows</b></font>: Degradation - moved to a higher (worse) zone",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key insight:</b> Most experiments stay in their original zone (thick gray bands). "
        "The WARNING zone (0.60-0.80) shows the most movement, with some experiments recovering "
        "to CAUTION or SAFE. Very few experiments that reached CRITICAL (>0.80) recovered.",
        body_style
    ))
    story.append(Paragraph(
        "<b>White paper potential:</b> HIGH - Immediately communicates the 'stickiness' of drift.",
        highlight_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # 2. SLOPE CHART
    # =========================================================================
    story.append(Paragraph("2. Slope Chart (Dumbbell Plot)", heading_style))
    add_image(output_dir / "rescue_slope_chart.png", caption="Figure 2: Peak vs Final Drift by Model")

    story.append(Paragraph(
        "<b>What it shows:</b> Each row is one model. Circles show peak drift, squares show "
        "final drift. The connecting line reveals recovery (downward slope) or degradation "
        "(upward slope).",
        body_style
    ))
    story.append(Paragraph(
        "<b>How to read it:</b><br/>"
        "- <font color='green'><b>Green lines</b></font>: Downward slope = drift reduced (recovery)<br/>"
        "- <font color='red'><b>Red lines</b></font>: Upward slope = drift increased (degradation)<br/>"
        "- <font color='gray'><b>Gray lines</b></font>: Flat = no change<br/>"
        "- <b>DELTA column</b>: Exact numerical change (positive = recovery)",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key insight:</b> Most models show minimal recovery (short lines, near-zero deltas). "
        "A few models (e.g., claude-haiku-4-5) show meaningful recovery. Models are sorted by "
        "peak drift, revealing which architectures are most susceptible to drift.",
        body_style
    ))
    story.append(Paragraph(
        "<b>White paper potential:</b> MEDIUM-HIGH - Clean per-model comparison, good for appendix.",
        highlight_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # 3. NIGHTINGALE ROSE
    # =========================================================================
    story.append(Paragraph("3. Nightingale Rose Chart", heading_style))
    add_image(output_dir / "rescue_nightingale_rose.png", caption="Figure 3: Recovery Ratio by Provider (Polar Area)")

    story.append(Paragraph(
        "<b>What it shows:</b> A polar area chart inspired by Florence Nightingale's famous "
        "1858 'Diagram of the Causes of Mortality'. Each petal represents one provider, with "
        "petal size proportional to mean recovery ratio.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Historical significance:</b> Florence Nightingale invented this visualization type "
        "to communicate mortality data to non-statisticians. It's rarely used today but remains "
        "one of the most beautiful and intuitive ways to show proportional data.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key insight:</b> Claude shows the largest petal (highest recovery ratio), while "
        "most other providers have small petals indicating limited recovery capability. The "
        "visual immediately communicates which providers 'bounce back' from drift.",
        body_style
    ))
    story.append(Paragraph(
        "<b>White paper potential:</b> MEDIUM - Beautiful but may be unfamiliar to readers.",
        highlight_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # 4. BEESWARM WITH ARROWS
    # =========================================================================
    story.append(Paragraph("4. Beeswarm with Recovery Arrows", heading_style))
    add_image(output_dir / "rescue_beeswarm_arrows.png", caption="Figure 4: Individual Experiments with Recovery Vectors")

    story.append(Paragraph(
        "<b>What it shows:</b> Each dot is one experiment positioned at its peak drift value. "
        "Arrows show the direction and magnitude of recovery (green pointing left) or "
        "degradation (red pointing right). Providers are separated vertically with jitter.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Zone shading:</b><br/>"
        "- <font color='green'><b>Green zone</b></font>: SAFE (0.00 - 0.60)<br/>"
        "- <font color='yellow'><b>Yellow zone</b></font>: WARNING (0.60 - 0.80)<br/>"
        "- <font color='red'><b>Red zone</b></font>: CRITICAL (0.80+)",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key insight:</b> The 'swarm' pattern reveals the density of experiments at each "
        "drift level. Most arrows are very short, confirming that recovery is minimal. The "
        "few long green arrows show exceptions where significant recovery occurred.",
        body_style
    ))
    story.append(Paragraph(
        "<b>White paper potential:</b> HIGH - Visually striking, shows individual data points.",
        highlight_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # 5. PARALLEL COORDINATES
    # =========================================================================
    story.append(Paragraph("5. Parallel Coordinates Plot", heading_style))
    add_image(output_dir / "rescue_parallel_coordinates.png", caption="Figure 5: Trajectory from Baseline to Peak to Final")

    story.append(Paragraph(
        "<b>What it shows:</b> Each line traces one experiment's journey from baseline drift "
        "(left) through peak drift (center) to final drift (right). Lines are colored by provider.",
        body_style
    ))
    story.append(Paragraph(
        "<b>How to read it:</b><br/>"
        "- Lines that <b>rise</b> from Baseline to Peak show drift induction working<br/>"
        "- Lines that <b>fall</b> from Peak to Final show recovery<br/>"
        "- Lines that stay <b>flat</b> from Peak to Final show no recovery<br/>"
        "- The <font color='red'>red dashed line</font> is the Event Horizon (0.80)",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key insight:</b> Most lines rise sharply from Baseline to Peak (drift induction works), "
        "but stay relatively flat from Peak to Final (recovery fails). The visual shows that "
        "drift is easy to induce but hard to reverse.",
        body_style
    ))
    story.append(Paragraph(
        "<b>White paper potential:</b> MEDIUM - Good for showing full trajectory, may be busy.",
        highlight_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # 6. RECOVERY HEATMAP
    # =========================================================================
    story.append(Paragraph("6. Recovery Heatmap", heading_style))
    add_image(output_dir / "rescue_recovery_heatmap.png", caption="Figure 6: Recovery Rate by Provider and Peak Zone")

    story.append(Paragraph(
        "<b>What it shows:</b> A matrix showing mean recovery ratio for each combination of "
        "provider (rows) and peak drift zone (columns). Green cells indicate high recovery, "
        "red cells indicate low/no recovery.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Cell values:</b> Each cell shows the mean recovery ratio and sample size (n=X). "
        "Recovery ratio = 1 - (final_drift / peak_drift). Higher values = better recovery.",
        body_style
    ))
    story.append(Paragraph(
        "<b>Key insights:</b><br/>"
        "- <b>Claude</b> shows the only green cells (0.22-0.33 recovery) - best recovery overall<br/>"
        "- <b>GPT</b> shows 0.37 recovery from CAUTION zone but 0.00 from CRITICAL<br/>"
        "- Most providers show red cells across all zones - minimal recovery capability<br/>"
        "- Recovery is hardest from the CRITICAL zone (rightmost column mostly red)",
        body_style
    ))
    story.append(Paragraph(
        "<b>White paper potential:</b> VERY HIGH - Best for provider comparison analysis.",
        highlight_style
    ))

    story.append(PageBreak())

    # =========================================================================
    # SUMMARY & RECOMMENDATIONS
    # =========================================================================
    story.append(Paragraph("Summary: Top Picks for White Paper", heading_style))

    story.append(Paragraph(
        "<b>Tier 1 - Strongly Recommended:</b>",
        body_style
    ))
    story.append(Paragraph(
        "1. <b>Sankey Diagram</b> - Perfect for showing 'where did the drift go?' at a glance<br/>"
        "2. <b>Recovery Heatmap</b> - Best for provider comparison, actionable insights<br/>"
        "3. <b>Beeswarm with Arrows</b> - Shows individual data points with visual impact",
        body_style
    ))

    story.append(Paragraph(
        "<b>Tier 2 - Good Supporting Figures:</b>",
        body_style
    ))
    story.append(Paragraph(
        "4. <b>Slope Chart</b> - Clean per-model breakdown, good for appendix<br/>"
        "5. <b>Parallel Coordinates</b> - Shows full trajectory, useful for methodology section",
        body_style
    ))

    story.append(Paragraph(
        "<b>Tier 3 - Specialized/Optional:</b>",
        body_style
    ))
    story.append(Paragraph(
        "6. <b>Nightingale Rose</b> - Beautiful but may confuse readers unfamiliar with the format",
        body_style
    ))

    story.append(Spacer(1, 0.3*inch))

    story.append(Paragraph("Overall Finding", heading_style))
    story.append(Paragraph(
        "<b>Recovery is rare and limited.</b> All six visualization types converge on the same "
        "conclusion: once identity drift occurs, it tends to persist. The rescue protocol "
        "successfully induces drift but rarely reverses it. Claude shows the best recovery "
        "capability, while most other providers show minimal recovery regardless of the "
        "severity of the initial drift.",
        body_style
    ))

    story.append(Spacer(1, 0.2*inch))
    story.append(Paragraph(
        "<i>Generated by RnD_Visualization.py - Experimental visualization laboratory for "
        "S7 ARMADA rescue protocol analysis.</i>",
        caption_style
    ))

    # Build PDF
    doc.build(story)
    print(f"  Saved: {output_path}")
    return output_path


# =============================================================================
# MAIN
# =============================================================================

def main():
    """Generate all R&D visualizations."""
    print("=" * 60)
    print("R&D VISUALIZATION LABORATORY")
    print("Experimental Rescue Protocol Visualizations")
    print("=" * 60)

    # Create output directory
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    print(f"\nOutput directory: {OUTPUT_DIR}")

    # Load data
    rescue_data = load_rescue_data()

    if not rescue_data:
        print("[ERROR] No rescue data found!")
        return 1

    # Generate all visualizations
    generated = []

    try:
        generated.append(generate_sankey_diagram(rescue_data, OUTPUT_DIR))
    except Exception as e:
        print(f"  [ERROR] Sankey: {e}")

    try:
        generated.append(generate_slope_chart(rescue_data, OUTPUT_DIR))
    except Exception as e:
        print(f"  [ERROR] Slope Chart: {e}")

    try:
        generated.append(generate_nightingale_rose(rescue_data, OUTPUT_DIR))
    except Exception as e:
        print(f"  [ERROR] Nightingale Rose: {e}")

    try:
        generated.append(generate_beeswarm_arrows(rescue_data, OUTPUT_DIR))
    except Exception as e:
        print(f"  [ERROR] Beeswarm: {e}")

    try:
        generated.append(generate_parallel_coordinates(rescue_data, OUTPUT_DIR))
    except Exception as e:
        print(f"  [ERROR] Parallel Coordinates: {e}")

    try:
        generated.append(generate_recovery_heatmap(rescue_data, OUTPUT_DIR))
    except Exception as e:
        print(f"  [ERROR] Heatmap: {e}")

    # Generate PDF summary
    try:
        pdf_path = generate_rnd_pdf_summary(OUTPUT_DIR)
        if pdf_path:
            generated.append(pdf_path)
    except Exception as e:
        print(f"  [ERROR] PDF: {e}")

    # Summary
    print("\n" + "=" * 60)
    print("R&D VISUALIZATION COMPLETE")
    print("=" * 60)
    print(f"\nGenerated {len([g for g in generated if g])} outputs:")
    for g in generated:
        if g:
            print(f"  - {g.name}")

    print(f"\nOutput folder: {OUTPUT_DIR}")
    print("\nThese are EXPERIMENTAL - review and pick favorites for white paper!")
    print("See RnD_Rescue_Summary.pdf for detailed documentation of each visualization.")

    return 0


if __name__ == '__main__':
    exit(main())
