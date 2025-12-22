#!/usr/bin/env python3
"""
8_Radar_Oscilloscope: Per-Provider Aggregate Radar and Oscilloscope Visualizations
===================================================================================
Generates radar plots showing multi-dimensional stability metrics per provider,
and oscilloscope-style time-series views of aggregate settling behavior.

Data source: Run 023d (IRON CLAD Foundation - 750 experiments)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict
import matplotlib.patches as mpatches

# Paths
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
OUTPUT_DIR = Path(__file__).parent

# Provider colors (consistent with other visualizations)
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
    'meta': '#0668E1',
    'mistral': '#FF7000',
    'cohere': '#39594D',
    'deepseek': '#4A90D9',
}

def load_data():
    """Load Run 023d results."""
    data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])

def aggregate_by_provider(results):
    """Aggregate metrics by provider."""
    provider_data = defaultdict(lambda: {
        'peak_drift': [],
        'settled_drift': [],
        'settling_time': [],
        'overshoot_ratio': [],
        'ringback_count': [],
        'naturally_settled': [],
        'probe_sequences': [],
        'models': set()
    })

    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')
        provider_data[provider]['models'].add(model)
        provider_data[provider]['peak_drift'].append(r.get('peak_drift', 0))
        provider_data[provider]['settled_drift'].append(r.get('settled_drift', 0))
        provider_data[provider]['settling_time'].append(r.get('settling_time', 0))
        provider_data[provider]['overshoot_ratio'].append(r.get('overshoot_ratio', 1))
        provider_data[provider]['ringback_count'].append(r.get('ringback_count', 0))
        provider_data[provider]['naturally_settled'].append(1 if r.get('naturally_settled', False) else 0)

        # Extract probe sequence for oscilloscope
        probes = r.get('probe_sequence', [])
        drifts = [p.get('drift', 0) for p in probes]
        provider_data[provider]['probe_sequences'].append(drifts)

    return provider_data

def compute_radar_metrics(provider_data):
    """Compute normalized radar metrics for each provider."""
    radar_data = {}

    for provider, data in provider_data.items():
        # Compute means
        mean_peak = np.mean(data['peak_drift'])
        mean_settled = np.mean(data['settled_drift'])
        mean_settling = np.mean(data['settling_time'])
        mean_overshoot = np.mean(data['overshoot_ratio'])
        mean_ringback = np.mean(data['ringback_count'])
        stability_rate = np.mean(data['naturally_settled'])

        # Normalize metrics to 0-1 scale (higher = better stability)
        # Peak drift: lower is better (invert)
        peak_score = 1 - min(mean_peak / 1.0, 1.0)

        # Settled drift: lower is better (invert)
        settled_score = 1 - min(mean_settled / 0.8, 1.0)  # EH = 0.8

        # Settling time: lower is better (invert)
        settling_score = 1 - min(mean_settling / 20, 1.0)  # max 20 probes

        # Overshoot ratio: closer to 1 is better
        overshoot_score = 1 - min(abs(mean_overshoot - 1) / 2, 1.0)

        # Ringback: lower is better (invert)
        ringback_score = 1 - min(mean_ringback / 20, 1.0)

        # Stability rate: higher is better (already 0-1)
        stability_score = stability_rate

        radar_data[provider] = {
            'metrics': [peak_score, settled_score, settling_score,
                       overshoot_score, ringback_score, stability_score],
            'raw': {
                'peak_drift': mean_peak,
                'settled_drift': mean_settled,
                'settling_time': mean_settling,
                'overshoot_ratio': mean_overshoot,
                'ringback_count': mean_ringback,
                'stability_rate': stability_rate
            },
            'n_results': len(data['peak_drift']),
            'n_models': len(data['models'])
        }

    return radar_data

def plot_provider_radar(radar_data, output_dir):
    """Create radar plot comparing all providers - LIGHT MODE."""
    categories = ['Peak\nControl', 'Settled\nDrift', 'Settling\nSpeed',
                  'Overshoot\nControl', 'Ringback\nDamping', 'Natural\nStability']
    n_cats = len(categories)

    # Compute angles
    angles = np.linspace(0, 2 * np.pi, n_cats, endpoint=False).tolist()
    angles += angles[:1]  # Close the loop

    fig, ax = plt.subplots(figsize=(12, 10), subplot_kw=dict(polar=True))
    ax.set_facecolor('white')
    fig.patch.set_facecolor('white')

    # Plot each provider
    for provider, data in radar_data.items():
        values = data['metrics'] + data['metrics'][:1]  # Close loop
        color = PROVIDER_COLORS.get(provider, '#888888')

        ax.plot(angles, values, 'o-', linewidth=2.5, label=f"{provider} (n={data['n_results']})",
                color=color, markersize=8)
        ax.fill(angles, values, alpha=0.2, color=color)

    # Customize appearance
    ax.set_xticks(angles[:-1])
    ax.set_xticklabels(categories, size=11, color='black', fontweight='bold')
    ax.set_ylim(0, 1)
    ax.set_yticks([0.25, 0.5, 0.75, 1.0])
    ax.set_yticklabels(['0.25', '0.50', '0.75', '1.00'], color='#555555', size=9)
    ax.yaxis.grid(True, color='#cccccc', linestyle='--', alpha=0.7)
    ax.xaxis.grid(True, color='#cccccc', linestyle='--', alpha=0.7)

    # Add Event Horizon reference circle (0.8 stability threshold)
    eh_circle = plt.Circle((0, 0), 0.8, transform=ax.transData._b,
                           fill=False, color='#ff4444', linestyle='--',
                           linewidth=1.5, alpha=0.7)

    ax.set_title('Provider Stability Radar\nRun 023d: IRON CLAD Foundation (750 experiments)',
                 size=16, color='black', fontweight='bold', pad=20)

    # Legend
    legend = ax.legend(loc='upper right', bbox_to_anchor=(1.3, 1.1),
                      facecolor='white', edgecolor='#cccccc',
                      fontsize=10)
    for text in legend.get_texts():
        text.set_color('black')

    plt.tight_layout()

    # Save
    for ext in ['png', 'svg']:
        output_path = output_dir / f'provider_stability_radar.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_oscilloscope_aggregate(provider_data, output_dir):
    """Create oscilloscope-style aggregate settling curves per provider - LIGHT MODE."""
    fig, ax = plt.subplots(figsize=(14, 8))
    ax.set_facecolor('#f8f8f8')
    fig.patch.set_facecolor('white')

    max_probes = 25  # Extended settling window

    for provider, data in provider_data.items():
        sequences = data['probe_sequences']
        if not sequences:
            continue

        # Pad sequences to same length
        padded = []
        for seq in sequences:
            if len(seq) < max_probes:
                # Pad with last value
                seq = seq + [seq[-1] if seq else 0] * (max_probes - len(seq))
            padded.append(seq[:max_probes])

        arr = np.array(padded)
        mean_curve = np.mean(arr, axis=0)
        std_curve = np.std(arr, axis=0)

        color = PROVIDER_COLORS.get(provider, '#888888')
        x = np.arange(max_probes)

        # Plot mean with std envelope
        ax.fill_between(x, mean_curve - std_curve, mean_curve + std_curve,
                        alpha=0.2, color=color)
        ax.plot(x, mean_curve, '-', linewidth=2.5, color=color,
               label=f'{provider} (n={len(sequences)})', marker='o', markersize=4)

    # Event Horizon reference
    ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2,
               alpha=0.8, label='Event Horizon (0.80)')

    # Probe regions (softer colors for light mode)
    ax.axvspan(0, 3, alpha=0.08, color='#3366cc', label='Baseline (0-2)')
    ax.axvspan(3, 4, alpha=0.12, color='#cc3333', label='Step Input (3)')
    ax.axvspan(4, max_probes, alpha=0.06, color='#33aa33', label='Recovery (4+)')

    ax.set_xlabel('Probe Index', size=12, color='black', fontweight='bold')
    ax.set_ylabel('Cosine Distance from Baseline', size=12, color='black', fontweight='bold')
    ax.set_title('Oscilloscope: Provider Aggregate Settling Dynamics\nRun 023d: IRON CLAD Foundation',
                 size=14, color='black', fontweight='bold')

    ax.set_xlim(0, max_probes - 1)
    ax.set_ylim(0, 1.0)
    ax.grid(True, color='#cccccc', linestyle='-', alpha=0.5)
    ax.tick_params(colors='black')
    for spine in ax.spines.values():
        spine.set_color('#cccccc')

    legend = ax.legend(loc='upper right', facecolor='white', edgecolor='#cccccc', fontsize=9)
    for text in legend.get_texts():
        text.set_color('black')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'oscilloscope_aggregate.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_oscilloscope_grid(provider_data, output_dir):
    """Create grid of individual provider oscilloscope views - LIGHT MODE."""
    providers = sorted(provider_data.keys())
    n_providers = len(providers)

    cols = 3
    rows = (n_providers + cols - 1) // cols

    fig, axes = plt.subplots(rows, cols, figsize=(15, 4 * rows))
    fig.patch.set_facecolor('white')
    axes = axes.flatten() if n_providers > 1 else [axes]

    max_probes = 25

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        ax.set_facecolor('#f8f8f8')

        data = provider_data[provider]
        sequences = data['probe_sequences']

        # Pad and compute
        padded = []
        for seq in sequences:
            if len(seq) < max_probes:
                seq = seq + [seq[-1] if seq else 0] * (max_probes - len(seq))
            padded.append(seq[:max_probes])

        arr = np.array(padded)

        # Plot individual traces (sample for visibility)
        sample_size = min(50, len(arr))
        sample_idx = np.random.choice(len(arr), sample_size, replace=False)

        color = PROVIDER_COLORS.get(provider, '#888888')
        x = np.arange(max_probes)

        for i in sample_idx:
            ax.plot(x, arr[i], '-', linewidth=0.5, alpha=0.3, color=color)

        # Mean curve (with darker outline for visibility on light background)
        mean_curve = np.mean(arr, axis=0)
        ax.plot(x, mean_curve, '-', linewidth=3.5, color='black', alpha=0.3)
        ax.plot(x, mean_curve, '-', linewidth=2.5, color=color)

        # EH line
        ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=1.5, alpha=0.7)

        ax.set_title(f'{provider.upper()}\nn={len(sequences)} | models={len(data["models"])}',
                    color='black', fontsize=11, fontweight='bold')
        ax.set_xlim(0, max_probes - 1)
        ax.set_ylim(0, 1.0)
        ax.grid(True, color='#cccccc', linestyle='-', alpha=0.5)
        ax.tick_params(colors='#333333', labelsize=8)
        for spine in ax.spines.values():
            spine.set_color('#cccccc')

    # Hide unused axes
    for idx in range(n_providers, len(axes)):
        axes[idx].set_visible(False)

    fig.suptitle('Provider Oscilloscope Grid: Individual Settling Traces\nRun 023d: IRON CLAD Foundation',
                 size=14, color='black', fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'oscilloscope_grid.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def print_summary(radar_data):
    """Print summary statistics."""
    print("\n" + "="*70)
    print("PROVIDER STABILITY SUMMARY")
    print("="*70)

    for provider, data in sorted(radar_data.items()):
        raw = data['raw']
        print(f"\n{provider.upper()} ({data['n_models']} models, {data['n_results']} experiments):")
        print(f"  Peak Drift:      {raw['peak_drift']:.4f}")
        print(f"  Settled Drift:   {raw['settled_drift']:.4f}")
        print(f"  Settling Time:   {raw['settling_time']:.1f} probes")
        print(f"  Overshoot Ratio: {raw['overshoot_ratio']:.3f}")
        print(f"  Ringback Count:  {raw['ringback_count']:.1f}")
        print(f"  Stability Rate:  {raw['stability_rate']*100:.1f}%")

def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nAggregating by provider...")
    provider_data = aggregate_by_provider(results)
    print(f"Found {len(provider_data)} providers")

    print("\nComputing radar metrics...")
    radar_data = compute_radar_metrics(provider_data)

    print("\nGenerating visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_provider_radar(radar_data, OUTPUT_DIR)
    plot_oscilloscope_aggregate(provider_data, OUTPUT_DIR)
    plot_oscilloscope_grid(provider_data, OUTPUT_DIR)

    print_summary(radar_data)

    print("\n" + "="*70)
    print("VISUALIZATION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
