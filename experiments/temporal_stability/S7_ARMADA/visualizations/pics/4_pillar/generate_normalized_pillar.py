#!/usr/bin/env python3
"""
Generate Pillar Visualization

Creates pillar visualizations for drift analysis with two modes:
1. NORMALIZED: Values as % of Event Horizon (1.23 = 100%)
2. RAW: Absolute drift values (0.0 - 3.0+)

Options:
- --mode: 'normalized' (default) or 'raw'
- --no-labels: Disable data labels (useful for tight clustering)

Usage:
    python generate_normalized_pillar.py --run 009 --mode normalized
    python generate_normalized_pillar.py --run 018 --mode raw --no-labels
    python generate_normalized_pillar.py --run 009 --mode both  # generates both files
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


def generate_pillar(run_id: str, output_path: Path = None, mode: str = 'normalized',
                    show_labels: bool = True):
    """
    Generate a pillar visualization for the specified run.

    Args:
        run_id: Run identifier (e.g., '009', '018')
        output_path: Output file path (auto-generated if None)
        mode: 'normalized' (% of EH) or 'raw' (absolute values)
        show_labels: Whether to show data labels on bars
    """

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

    # Determine mode settings
    is_normalized = (mode == 'normalized')
    if is_normalized:
        transform_func = normalize_to_eh
        y_suffix = '%'
        threshold_value = 100
        threshold_label = 'Event Horizon (100%)'
        mode_label = 'Normalized (% of EH)'
    else:
        transform_func = lambda x: x  # identity function for raw mode
        y_suffix = ''
        threshold_value = EVENT_HORIZON
        threshold_label = f'Event Horizon ({EVENT_HORIZON})'
        mode_label = 'Raw Drift Values'

    # Create figure
    fig, axes = plt.subplots(2, 2, figsize=(16, 14))
    fig.suptitle(f'Run {run_id}: Pillar Analysis ({mode_label})',
                 fontsize=14, fontweight='bold')

    providers = list(provider_stats.keys())
    x = np.arange(len(providers))
    width = 0.25

    # ===== Panel 1: Baseline vs Final =====
    ax1 = axes[0, 0]

    baselines_val = [transform_func(np.mean(provider_stats[p]['baselines'])) for p in providers]
    finals_val = [transform_func(np.mean(provider_stats[p]['finals'])) for p in providers]

    bars1 = ax1.bar(x - width/2, baselines_val, width,
                    label='Baseline', color=[PROVIDER_COLORS.get(p, 'gray') for p in providers],
                    alpha=0.6)
    bars2 = ax1.bar(x + width/2, finals_val, width,
                    label='Final', color=[PROVIDER_COLORS.get(p, 'gray') for p in providers])

    ax1.axhline(y=threshold_value, color='red', linestyle='--', linewidth=2, label=threshold_label)

    ax1.set_xlabel('Provider')
    ylabel = 'Drift (% of Event Horizon)' if is_normalized else 'Drift (Embedding Distance)'
    ax1.set_ylabel(ylabel)
    ax1.set_title('Baseline vs Final Drift')
    ax1.set_xticks(x)
    ax1.set_xticklabels(providers)
    ax1.legend()
    ax1.grid(axis='y', alpha=0.3)

    # Add value labels (conditional)
    if show_labels:
        label_offset = 5 if is_normalized else 0.05
        for bar, val in zip(bars1, baselines_val):
            label = f'{val:.0f}{y_suffix}' if is_normalized else f'{val:.2f}'
            ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + label_offset,
                    label, ha='center', va='bottom', fontsize=8)
        for bar, val in zip(bars2, finals_val):
            label = f'{val:.0f}{y_suffix}' if is_normalized else f'{val:.2f}'
            ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + label_offset,
                    label, ha='center', va='bottom', fontsize=8)

    # ===== Panel 2: Peak Drift =====
    ax2 = axes[0, 1]

    peaks_val = [transform_func(np.mean(provider_stats[p]['peaks'])) for p in providers]

    bars = ax2.bar(x, peaks_val, width*2,
                   color=[PROVIDER_COLORS.get(p, 'gray') for p in providers])

    ax2.axhline(y=threshold_value, color='red', linestyle='--', linewidth=2, label=threshold_label)

    ax2.set_xlabel('Provider')
    ylabel = 'Peak Drift (% of Event Horizon)' if is_normalized else 'Peak Drift (Embedding Distance)'
    ax2.set_ylabel(ylabel)
    ax2.set_title('Peak Drift per Provider')
    ax2.set_xticks(x)
    ax2.set_xticklabels(providers)
    ax2.legend()
    ax2.grid(axis='y', alpha=0.3)

    if show_labels:
        label_offset = 5 if is_normalized else 0.05
        for bar, val in zip(bars, peaks_val):
            label = f'{val:.0f}{y_suffix}' if is_normalized else f'{val:.2f}'
            ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + label_offset,
                    label, ha='center', va='bottom', fontsize=9)

    # ===== Panel 3: Distribution Box Plot =====
    ax3 = axes[1, 0]

    box_data = [[transform_func(d) for d in provider_stats[p]['means']] for p in providers]
    bp = ax3.boxplot(box_data, tick_labels=providers, patch_artist=True)

    for patch, provider in zip(bp['boxes'], providers):
        patch.set_facecolor(PROVIDER_COLORS.get(provider, 'gray'))
        patch.set_alpha(0.6)

    ax3.axhline(y=threshold_value, color='red', linestyle='--', linewidth=2, label=threshold_label)

    ax3.set_xlabel('Provider')
    ylabel = 'Mean Drift (% of Event Horizon)' if is_normalized else 'Mean Drift (Embedding Distance)'
    ax3.set_ylabel(ylabel)
    ax3.set_title('Drift Distribution per Provider')
    ax3.legend()
    ax3.grid(axis='y', alpha=0.3)

    # ===== Panel 4: Count + Summary Stats =====
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Summary table
    summary_text = "SUMMARY STATISTICS\n" + "=" * 50 + "\n\n"
    summary_text += f"Event Horizon Threshold: {EVENT_HORIZON}\n"
    summary_text += f"Mode: {mode_label}\n\n"

    if is_normalized:
        summary_text += f"{'Provider':<12} {'Count':>8} {'Baseline':>12} {'Final':>12} {'Peak':>12}\n"
        summary_text += "-" * 58 + "\n"
        for p in providers:
            stats = provider_stats[p]
            n = stats['n_trajectories']
            baseline = transform_func(np.mean(stats['baselines']))
            final = transform_func(np.mean(stats['finals']))
            peak = transform_func(np.mean(stats['peaks']))
            summary_text += f"{p:<12} {n:>8} {baseline:>10.0f}% {final:>10.0f}% {peak:>10.0f}%\n"
    else:
        summary_text += f"{'Provider':<12} {'Count':>8} {'Baseline':>10} {'Final':>10} {'Peak':>10}\n"
        summary_text += "-" * 58 + "\n"
        for p in providers:
            stats = provider_stats[p]
            n = stats['n_trajectories']
            baseline = np.mean(stats['baselines'])
            final = np.mean(stats['finals'])
            peak = np.mean(stats['peaks'])
            summary_text += f"{p:<12} {n:>8} {baseline:>10.3f} {final:>10.3f} {peak:>10.3f}\n"

    summary_text += "-" * 58 + "\n"
    total_traj = sum(provider_stats[p]['n_trajectories'] for p in providers)
    summary_text += f"{'TOTAL':<12} {total_traj:>8}\n"

    summary_text += "\n\nINTERPRETATION:\n"
    if is_normalized:
        summary_text += "• Values < 100% = Below Event Horizon (stable zone)\n"
        summary_text += "• Values = 100% = At Event Horizon threshold\n"
        summary_text += "• Values > 100% = Above Event Horizon (volatile zone)\n"
    else:
        summary_text += f"• Values < {EVENT_HORIZON} = Below Event Horizon (stable zone)\n"
        summary_text += f"• Values = {EVENT_HORIZON} = At Event Horizon threshold\n"
        summary_text += f"• Values > {EVENT_HORIZON} = Above Event Horizon (volatile zone)\n"

    ax4.text(0.1, 0.9, summary_text, transform=ax4.transAxes,
             fontsize=10, verticalalignment='top', fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()

    # Save
    if output_path is None:
        suffix = 'normalized' if is_normalized else 'raw'
        output_path = Path(__file__).parent / f'run{run_id}_pillar_{suffix}.png'

    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved pillar visualization to: {output_path}")

    # Also save SVG
    svg_path = output_path.with_suffix('.svg')
    plt.savefig(svg_path, format='svg', bbox_inches='tight')
    print(f"Saved SVG to: {svg_path}")

    plt.close()

    return output_path


# Keep old function name for backwards compatibility
def generate_normalized_pillar(run_id: str, output_path: Path = None):
    """Backwards compatible wrapper - generates normalized view."""
    return generate_pillar(run_id, output_path, mode='normalized', show_labels=True)


if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Generate pillar visualization')
    parser.add_argument('--run', default='009', help='Run ID (e.g., 009, 010, 018)')
    parser.add_argument('--output', help='Output path (optional)')
    parser.add_argument('--mode', choices=['normalized', 'raw', 'both'], default='normalized',
                        help='Visualization mode: normalized (%% of EH), raw (absolute), or both')
    parser.add_argument('--no-labels', action='store_true',
                        help='Disable data labels on bars (useful for tight clustering)')

    args = parser.parse_args()

    output = Path(args.output) if args.output else None
    show_labels = not args.no_labels

    if args.mode == 'both':
        # Generate both versions
        print("Generating BOTH normalized and raw visualizations...")
        generate_pillar(args.run, output_path=None, mode='normalized', show_labels=show_labels)
        generate_pillar(args.run, output_path=None, mode='raw', show_labels=show_labels)
    else:
        generate_pillar(args.run, output, mode=args.mode, show_labels=show_labels)
