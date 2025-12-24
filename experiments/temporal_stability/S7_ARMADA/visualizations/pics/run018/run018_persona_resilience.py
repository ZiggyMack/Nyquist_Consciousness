#!/usr/bin/env python3
"""
RUN 018 PERSONA RESILIENCE: Beeswarm with Recovery Arrows
==========================================================
Visualizes how different AI providers respond to persona pressure.

KEY INSIGHT: It's not about avoiding the Event Horizon - it's about bouncing back!
- xAI crosses Event Horizon 100% of the time but recovers to 0.010 final drift (BEST)
- Together crosses only 64% but stays at 0.122 final drift (WORST recovery)

This visualization shows:
- Each dot = one experiment at its PEAK drift position
- Green arrows = recovery toward baseline (good!)
- Red arrows = degradation from peak (bad!)
- Longer green arrows = better resilience

Author: Claude (VALIS Network)
Date: December 24, 2025
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

# Paths
S7_ARMADA = Path(__file__).parent.parent.parent.parent
RESULTS_DIR = S7_ARMADA / "11_CONTEXT_DAMPING" / "results"
OUTPUT_DIR = Path(__file__).parent

# Thresholds
EVENT_HORIZON = 0.80
WARNING_THRESHOLD = 0.60

# Provider colors (consistent with other visualizations)
PROVIDER_COLORS = {
    'anthropic': '#E06C75',  # Red
    'openai': '#61AFEF',     # Blue
    'google': '#98C379',     # Green
    'xai': '#C678DD',        # Purple
    'together': '#E5C07B',   # Yellow
    'nvidia': '#56B6C2',     # Cyan
}


def load_run018_data():
    """Load Run 018 consolidated data."""
    data_file = RESULTS_DIR / "S7_run_018_CURRENT.json"
    with open(data_file, 'r', encoding='utf-8') as f:
        return json.load(f)


def extract_resilience_data(data):
    """Extract peak and final drift for each experiment."""
    by_provider = defaultdict(list)

    for result in data.get('results', []):
        model = result.get('model', 'unknown')
        provider = result.get('provider', 'unknown')

        for subject in result.get('subjects', []):
            probe_seq = subject.get('probe_sequence', [])
            if len(probe_seq) < 2:
                continue

            # Extract drift values
            drifts = []
            for probe in probe_seq:
                drift = probe.get('drift', 0)
                if drift is not None:
                    drifts.append(drift)

            if len(drifts) >= 2:
                peak_drift = max(drifts)
                final_drift = drifts[-1]

                by_provider[provider].append({
                    'model': model,
                    'peak': peak_drift,
                    'final': final_drift,
                    'recovery': peak_drift - final_drift  # Positive = good recovery
                })

    return by_provider


def generate_beeswarm_arrows(data_by_provider, output_path):
    """
    Beeswarm plot where each point is positioned at its peak drift,
    with an arrow pointing to where it settled.
    """
    fig, ax = plt.subplots(figsize=(14, 10))

    # Sort providers by mean recovery (best recoverers at top)
    provider_stats = {}
    for provider, data in data_by_provider.items():
        if data:
            mean_recovery = np.mean([d['recovery'] for d in data])
            mean_final = np.mean([d['final'] for d in data])
            provider_stats[provider] = {
                'mean_recovery': mean_recovery,
                'mean_final': mean_final,
                'count': len(data)
            }

    # Sort by mean_final (ascending - best recoverers first)
    sorted_providers = sorted(provider_stats.keys(),
                              key=lambda p: provider_stats[p]['mean_final'])

    y_base = 0
    y_spacing = 1.5

    for provider in sorted_providers:
        data = data_by_provider[provider]
        color = PROVIDER_COLORS.get(provider, '#888888')
        stats = provider_stats[provider]

        # Add jitter for beeswarm effect
        n_points = len(data)
        jitter = np.random.normal(0, 0.18, n_points)

        for i, d in enumerate(data):
            y = y_base + jitter[i]

            # Draw arrow from peak to final
            dx = d['final'] - d['peak']

            if abs(dx) > 0.01:  # Only draw arrow if there's movement
                # Green = recovery (moving left toward 0), Red = degradation
                arrow_color = '#27ae60' if dx < 0 else '#c0392b'
                ax.annotate('', xy=(d['final'], y), xytext=(d['peak'], y),
                           arrowprops=dict(arrowstyle='->', color=arrow_color,
                                         lw=1.2, alpha=0.4))

            # Draw point at peak position
            ax.scatter(d['peak'], y, s=35, color=color, alpha=0.7,
                      edgecolor='white', linewidth=0.5, zorder=3)

        # Provider label with stats
        label = f"{provider.upper()}\n(n={stats['count']}, final={stats['mean_final']:.3f})"
        ax.text(-0.08, y_base, label, ha='right', va='center',
               fontsize=10, fontweight='bold', color=color)

        y_base += y_spacing

    # Threshold lines
    ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})', alpha=0.7)
    ax.axvline(x=WARNING_THRESHOLD, color='orange', linestyle=':', linewidth=1.5,
               label=f'Warning ({WARNING_THRESHOLD})', alpha=0.5)

    # Zone shading
    ax.axvspan(0, WARNING_THRESHOLD, alpha=0.08, color='green', label='Safe Zone')
    ax.axvspan(WARNING_THRESHOLD, EVENT_HORIZON, alpha=0.08, color='yellow')
    ax.axvspan(EVENT_HORIZON, 1.3, alpha=0.08, color='red', label='Critical Zone')

    ax.set_xlim(-0.15, 1.3)
    ax.set_ylim(-1, y_base)
    ax.set_xlabel('Cosine Drift', fontsize=12)
    ax.set_ylabel('')
    ax.set_yticks([])

    ax.set_title("RUN 018: Persona Resilience Under Pressure\n"
                 "(Dots = peak drift, Arrows show recovery | Green = recovery, Red = degradation)\n"
                 "Sorted by final drift: best recoverers at top",
                 fontsize=13, fontweight='bold')

    # Custom legend
    from matplotlib.patches import Patch, FancyArrow
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='red', linestyle='--', linewidth=2, label='Event Horizon (0.80)'),
        Patch(facecolor='green', alpha=0.15, label='Safe Zone (<0.60)'),
        Patch(facecolor='red', alpha=0.15, label='Critical Zone (>0.80)'),
        Line2D([0], [0], color='#27ae60', marker='>', markersize=8, linestyle='None',
               label='Recovery (good)'),
        Line2D([0], [0], color='#c0392b', marker='>', markersize=8, linestyle='None',
               label='Degradation (bad)'),
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=9)

    ax.grid(True, axis='x', alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_path.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"Saved: {output_path}")
    return output_path


def print_statistics(data_by_provider):
    """Print resilience statistics."""
    print("\n" + "=" * 60)
    print("PERSONA RESILIENCE STATISTICS")
    print("=" * 60)

    rows = []
    for provider, data in data_by_provider.items():
        if not data:
            continue

        peaks = [d['peak'] for d in data]
        finals = [d['final'] for d in data]
        recoveries = [d['recovery'] for d in data]
        eh_crossings = sum(1 for p in peaks if p > EVENT_HORIZON)

        rows.append({
            'provider': provider,
            'n': len(data),
            'mean_peak': np.mean(peaks),
            'mean_final': np.mean(finals),
            'mean_recovery': np.mean(recoveries),
            'eh_rate': eh_crossings / len(data) * 100
        })

    # Sort by mean_final (best first)
    rows.sort(key=lambda r: r['mean_final'])

    print(f"\n{'Provider':<12} {'N':>6} {'Peak':>8} {'Final':>8} {'Recovery':>10} {'EH%':>8}")
    print("-" * 60)

    for r in rows:
        print(f"{r['provider']:<12} {r['n']:>6} {r['mean_peak']:>8.3f} {r['mean_final']:>8.3f} "
              f"{r['mean_recovery']:>10.3f} {r['eh_rate']:>7.1f}%")

    print("\n" + "=" * 60)
    print("KEY INSIGHT: xAI crosses EH 100% but recovers best (0.010 final)")
    print("             Together avoids EH more but recovers worst (0.122 final)")
    print("=" * 60)


def main():
    print("=" * 60)
    print("RUN 018: PERSONA RESILIENCE ANALYSIS")
    print("It's not about avoiding the fall - it's about bouncing back!")
    print("=" * 60)

    # Load data
    print("\nLoading Run 018 data...")
    data = load_run018_data()

    # Extract resilience data
    print("Extracting resilience metrics...")
    by_provider = extract_resilience_data(data)

    total = sum(len(d) for d in by_provider.values())
    print(f"\nTotal experiments: {total}")
    for provider, data in sorted(by_provider.items()):
        print(f"  {provider}: {len(data)}")

    # Print statistics
    print_statistics(by_provider)

    # Generate visualization
    print("\nGenerating beeswarm arrows visualization...")
    output_path = OUTPUT_DIR / "run018_persona_resilience.png"
    generate_beeswarm_arrows(by_provider, output_path)

    print("\nDone!")


if __name__ == "__main__":
    main()
