#!/usr/bin/env python3
"""
Generate Normalized Pillar Visualization

Creates a pillar visualization where drift values are expressed as
a percentage of the Event Horizon threshold (1.23).

This makes it easier to understand:
- 100% = Event Horizon threshold
- <100% = Below EH (potentially stable)
- >100% = Above EH (volatile)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple

# Event Horizon threshold
EVENT_HORIZON = 1.23

# Provider colors (consistent with visualize_armada.py)
PROVIDER_COLORS = {
    'claude': '#8B5CF6',   # Purple
    'gpt': '#10B981',      # Green
    'gemini': '#F59E0B',   # Amber
    'grok': '#EF4444',     # Red
    'together': '#3B82F6'  # Blue
}

def normalize_to_eh(drift_value: float) -> float:
    """Express drift as percentage of Event Horizon."""
    return (drift_value / EVENT_HORIZON) * 100


def load_run_data(run_id: str) -> dict:
    """Load run data from JSON file."""
    # Navigate from pics/4_pillar to S7_ARMADA/0_results/runs
    base_path = Path(__file__).parent.parent.parent.parent / '0_results' / 'runs'

    # Check legacy runs folder for older runs
    legacy_path = base_path / 'legacy_runs'

    print(f"Looking for run {run_id} in:")
    print(f"  Base: {base_path}")
    print(f"  Legacy: {legacy_path}")

    # Try patterns
    patterns = [
        f'S7_run_{run_id}*.json',
        f'*run_{run_id}*.json',
        f'*{run_id}_*.json'
    ]

    for pattern in patterns:
        # Check legacy first for old runs
        if legacy_path.exists():
            matches = list(legacy_path.glob(pattern))
            if matches:
                print(f"  Found in legacy: {matches[0].name}")
                matches.sort(key=lambda x: x.stat().st_mtime, reverse=True)
                with open(matches[0], 'r', encoding='utf-8') as f:
                    return json.load(f)

        # Check main folder
        if base_path.exists():
            matches = list(base_path.glob(pattern))
            if matches:
                print(f"  Found: {matches[0].name}")
                matches.sort(key=lambda x: x.stat().st_mtime, reverse=True)
                with open(matches[0], 'r', encoding='utf-8') as f:
                    return json.load(f)

    raise FileNotFoundError(f"No data file found for run {run_id}")


def generate_normalized_pillar(run_id: str, output_path: Path = None):
    """Generate a normalized pillar visualization for the specified run."""

    data = load_run_data(run_id)
    trajectories = data.get('trajectories_for_3d', data.get('trajectories', []))

    if not trajectories:
        print(f"No trajectories found in run {run_id}")
        return

    # Collect provider statistics
    provider_stats = defaultdict(lambda: {
        'baselines': [],
        'finals': [],
        'peaks': [],
        'means': [],
        'n_trajectories': 0
    })

    for traj in trajectories:
        provider = traj.get('provider', 'unknown')
        drifts = traj.get('drifts', [])

        if len(drifts) < 2:
            continue

        provider_stats[provider]['baselines'].append(drifts[0])
        provider_stats[provider]['finals'].append(drifts[-1])
        provider_stats[provider]['peaks'].append(max(drifts))
        provider_stats[provider]['means'].append(np.mean(drifts))
        provider_stats[provider]['n_trajectories'] += 1

    # Create figure
    fig, axes = plt.subplots(2, 2, figsize=(16, 14))
    fig.suptitle(f'Run {run_id}: Normalized Pillar Analysis\n(Values as % of Event Horizon = 1.23)',
                 fontsize=14, fontweight='bold')

    providers = list(provider_stats.keys())
    x = np.arange(len(providers))
    width = 0.25

    # ===== Panel 1: Baseline vs Final (Normalized) =====
    ax1 = axes[0, 0]

    baselines_norm = [normalize_to_eh(np.mean(provider_stats[p]['baselines'])) for p in providers]
    finals_norm = [normalize_to_eh(np.mean(provider_stats[p]['finals'])) for p in providers]

    bars1 = ax1.bar(x - width/2, baselines_norm, width,
                    label='Baseline', color=[PROVIDER_COLORS.get(p, 'gray') for p in providers],
                    alpha=0.6)
    bars2 = ax1.bar(x + width/2, finals_norm, width,
                    label='Final', color=[PROVIDER_COLORS.get(p, 'gray') for p in providers])

    # Add 100% threshold line
    ax1.axhline(y=100, color='red', linestyle='--', linewidth=2, label='Event Horizon (100%)')

    ax1.set_xlabel('Provider')
    ax1.set_ylabel('Drift (% of Event Horizon)')
    ax1.set_title('Baseline vs Final Drift (Normalized)')
    ax1.set_xticks(x)
    ax1.set_xticklabels(providers)
    ax1.legend()
    ax1.grid(axis='y', alpha=0.3)

    # Add value labels
    for bar, val in zip(bars1, baselines_norm):
        ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 5,
                f'{val:.0f}%', ha='center', va='bottom', fontsize=8)
    for bar, val in zip(bars2, finals_norm):
        ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 5,
                f'{val:.0f}%', ha='center', va='bottom', fontsize=8)

    # ===== Panel 2: Peak Drift (Normalized) =====
    ax2 = axes[0, 1]

    peaks_norm = [normalize_to_eh(np.mean(provider_stats[p]['peaks'])) for p in providers]

    bars = ax2.bar(x, peaks_norm, width*2,
                   color=[PROVIDER_COLORS.get(p, 'gray') for p in providers])

    ax2.axhline(y=100, color='red', linestyle='--', linewidth=2, label='Event Horizon (100%)')

    ax2.set_xlabel('Provider')
    ax2.set_ylabel('Peak Drift (% of Event Horizon)')
    ax2.set_title('Peak Drift per Provider (Normalized)')
    ax2.set_xticks(x)
    ax2.set_xticklabels(providers)
    ax2.legend()
    ax2.grid(axis='y', alpha=0.3)

    for bar, val in zip(bars, peaks_norm):
        ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 5,
                f'{val:.0f}%', ha='center', va='bottom', fontsize=9)

    # ===== Panel 3: Distribution Box Plot (Normalized) =====
    ax3 = axes[1, 0]

    box_data = [[normalize_to_eh(d) for d in provider_stats[p]['means']] for p in providers]
    bp = ax3.boxplot(box_data, labels=providers, patch_artist=True)

    for patch, provider in zip(bp['boxes'], providers):
        patch.set_facecolor(PROVIDER_COLORS.get(provider, 'gray'))
        patch.set_alpha(0.6)

    ax3.axhline(y=100, color='red', linestyle='--', linewidth=2, label='Event Horizon (100%)')

    ax3.set_xlabel('Provider')
    ax3.set_ylabel('Mean Drift (% of Event Horizon)')
    ax3.set_title('Drift Distribution per Provider (Normalized)')
    ax3.legend()
    ax3.grid(axis='y', alpha=0.3)

    # ===== Panel 4: Count + Summary Stats =====
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Summary table
    summary_text = "SUMMARY STATISTICS\n" + "=" * 50 + "\n\n"
    summary_text += f"Event Horizon Threshold: {EVENT_HORIZON}\n\n"

    summary_text += f"{'Provider':<12} {'Count':>8} {'Baseline':>12} {'Final':>12} {'Peak':>12}\n"
    summary_text += "-" * 58 + "\n"

    for p in providers:
        stats = provider_stats[p]
        n = stats['n_trajectories']
        baseline = normalize_to_eh(np.mean(stats['baselines']))
        final = normalize_to_eh(np.mean(stats['finals']))
        peak = normalize_to_eh(np.mean(stats['peaks']))
        summary_text += f"{p:<12} {n:>8} {baseline:>10.0f}% {final:>10.0f}% {peak:>10.0f}%\n"

    summary_text += "-" * 58 + "\n"
    total_traj = sum(provider_stats[p]['n_trajectories'] for p in providers)
    summary_text += f"{'TOTAL':<12} {total_traj:>8}\n"

    summary_text += "\n\nINTERPRETATION:\n"
    summary_text += "• Values < 100% = Below Event Horizon (stable zone)\n"
    summary_text += "• Values = 100% = At Event Horizon threshold\n"
    summary_text += "• Values > 100% = Above Event Horizon (volatile zone)\n"

    ax4.text(0.1, 0.9, summary_text, transform=ax4.transAxes,
             fontsize=10, verticalalignment='top', fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()

    # Save
    if output_path is None:
        output_path = Path(__file__).parent / f'run{run_id}_pillar_normalized.png'

    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved normalized pillar visualization to: {output_path}")

    # Also save SVG
    svg_path = output_path.with_suffix('.svg')
    plt.savefig(svg_path, format='svg', bbox_inches='tight')
    print(f"Saved SVG to: {svg_path}")

    plt.close()

    return output_path


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Generate normalized pillar visualization')
    parser.add_argument('--run', default='009', help='Run ID (e.g., 009, 010, 018)')
    parser.add_argument('--output', help='Output path (optional)')

    args = parser.parse_args()

    output = Path(args.output) if args.output else None
    generate_normalized_pillar(args.run, output)
