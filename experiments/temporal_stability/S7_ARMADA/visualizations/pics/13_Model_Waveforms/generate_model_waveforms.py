#!/usr/bin/env python3
"""
13_Model_Waveforms: Per-Model Identity Waveform Visualizations
==============================================================
Individual drift waveforms for each model, showing the characteristic
"identity fingerprint" over the probe sequence.

Style inspired by Run 010 and Run 018 oscilloscope visualizations.

Data source: Run 023d (IRON CLAD Foundation - 750 experiments)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

# Paths
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
OUTPUT_DIR = Path(__file__).parent

# Provider colors
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
}

# Model display names (short form)
def short_model_name(model):
    """Get short display name for model."""
    name = model.split('/')[-1]
    # Truncate if too long
    if len(name) > 30:
        name = name[:27] + "..."
    return name

def load_data():
    """Load Run 023d results."""
    data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])

def group_by_model(results):
    """Group results by model."""
    by_model = defaultdict(list)
    for r in results:
        model = r.get('model', 'unknown')
        provider = r.get('provider', 'unknown')
        by_model[(provider, model)].append(r)
    return by_model

def plot_model_waveform_grid(by_model, output_dir):
    """Create grid of individual model waveforms."""
    # Sort by provider then model
    models = sorted(by_model.keys(), key=lambda x: (x[0], x[1]))
    n_models = len(models)

    # Grid layout: 5 cols
    cols = 5
    rows = (n_models + cols - 1) // cols

    fig, axes = plt.subplots(rows, cols, figsize=(20, 4 * rows))
    fig.patch.set_facecolor('white')
    axes = axes.flatten() if n_models > 1 else [axes]

    max_probes = 25

    for idx, (provider, model) in enumerate(models):
        ax = axes[idx]
        ax.set_facecolor('#fafafa')

        results = by_model[(provider, model)]
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Extract all probe sequences
        all_traces = []
        for r in results:
            probes = r.get('probe_sequence', [])
            drifts = [p.get('drift', 0) for p in probes]
            if drifts:
                all_traces.append(drifts)

        if not all_traces:
            ax.set_visible(False)
            continue

        # Pad to same length
        padded = []
        for trace in all_traces:
            if len(trace) < max_probes:
                trace = trace + [trace[-1]] * (max_probes - len(trace))
            padded.append(trace[:max_probes])

        arr = np.array(padded)
        x = np.arange(max_probes)

        # Plot individual traces (lighter)
        for trace in padded:
            ax.plot(x, trace, '-', linewidth=0.8, alpha=0.4, color=color)

        # Plot mean with thicker line
        mean_trace = np.mean(arr, axis=0)
        ax.plot(x, mean_trace, '-', linewidth=2.5, color=color,
               label=f'Mean (n={len(results)})')

        # Event Horizon
        ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=1.5,
                  alpha=0.7, label='EH')

        # Step input marker (probe 3)
        ax.axvline(x=3, color='#ff9800', linestyle=':', linewidth=1, alpha=0.7)

        # Title
        short_name = short_model_name(model)
        ax.set_title(f'{short_name}\n({provider})', fontsize=9, fontweight='bold')

        ax.set_xlim(0, max_probes - 1)
        ax.set_ylim(0, 1.0)
        ax.grid(True, alpha=0.3)
        ax.tick_params(labelsize=7)

        # Only label edges
        if idx % cols == 0:
            ax.set_ylabel('Drift', fontsize=8)
        if idx >= (rows - 1) * cols:
            ax.set_xlabel('Probe', fontsize=8)

    # Hide unused
    for idx in range(n_models, len(axes)):
        axes[idx].set_visible(False)

    fig.suptitle('Run 023d: Per-Model Identity Waveforms (25 Models)',
                fontsize=14, fontweight='bold', y=1.01)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'model_waveform_grid.{ext}'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_provider_waveform_overlay(by_model, output_dir):
    """Create overlaid waveforms per provider (archive Run 010 style)."""
    # Group models by provider
    by_provider = defaultdict(list)
    for (provider, model), results in by_model.items():
        by_provider[provider].append((model, results))

    providers = sorted(by_provider.keys())
    n_providers = len(providers)

    fig, axes = plt.subplots(1, n_providers, figsize=(4 * n_providers, 5))
    fig.patch.set_facecolor('white')
    if n_providers == 1:
        axes = [axes]

    max_probes = 25

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        ax.set_facecolor('#fafafa')

        color = PROVIDER_COLORS.get(provider, '#888888')
        models = by_provider[provider]

        # Plot each model's mean as a separate line
        for model, results in models:
            all_traces = []
            for r in results:
                probes = r.get('probe_sequence', [])
                drifts = [p.get('drift', 0) for p in probes]
                if drifts:
                    all_traces.append(drifts)

            if not all_traces:
                continue

            # Pad
            padded = []
            for trace in all_traces:
                if len(trace) < max_probes:
                    trace = trace + [trace[-1]] * (max_probes - len(trace))
                padded.append(trace[:max_probes])

            mean_trace = np.mean(padded, axis=0)
            x = np.arange(max_probes)

            short_name = short_model_name(model)
            ax.plot(x, mean_trace, '-', linewidth=2, alpha=0.7,
                   label=short_name[:20])

        # Event Horizon
        ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2,
                  alpha=0.8)

        # Step input
        ax.axvline(x=3, color='#ff9800', linestyle=':', linewidth=1.5, alpha=0.7)

        ax.set_title(f'{provider.upper()}\n({len(models)} models)',
                    fontsize=12, fontweight='bold', color=color)
        ax.set_xlabel('Probe Index', fontsize=10)
        if idx == 0:
            ax.set_ylabel('Cosine Distance', fontsize=10)

        ax.set_xlim(0, max_probes - 1)
        ax.set_ylim(0, 1.0)
        ax.grid(True, alpha=0.3)

        # Legend (small)
        if len(models) <= 6:
            ax.legend(fontsize=7, loc='upper right', framealpha=0.9)

    fig.suptitle('Run 023d: Provider Model Overlays (Mean Waveforms)',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'provider_waveform_overlay.{ext}'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_fleet_comparison(by_model, output_dir):
    """Create fleet-wide waveform comparison (archive Run 018 style)."""
    fig, ax = plt.subplots(figsize=(16, 8))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('#fafafa')

    max_probes = 25

    # Sort by provider
    models = sorted(by_model.keys(), key=lambda x: (x[0], x[1]))

    for provider, model in models:
        results = by_model[(provider, model)]
        color = PROVIDER_COLORS.get(provider, '#888888')

        all_traces = []
        for r in results:
            probes = r.get('probe_sequence', [])
            drifts = [p.get('drift', 0) for p in probes]
            if drifts:
                all_traces.append(drifts)

        if not all_traces:
            continue

        # Pad
        padded = []
        for trace in all_traces:
            if len(trace) < max_probes:
                trace = trace + [trace[-1]] * (max_probes - len(trace))
            padded.append(trace[:max_probes])

        mean_trace = np.mean(padded, axis=0)
        x = np.arange(max_probes)

        short_name = short_model_name(model)
        ax.plot(x, mean_trace, '-', linewidth=1.5, alpha=0.7, color=color,
               label=f'{short_name[:15]}')

    # Event Horizon
    ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2.5,
              alpha=0.9, label='Event Horizon')

    # Probe regions
    ax.axvspan(0, 3, alpha=0.08, color='#3366cc')
    ax.axvspan(3, 4, alpha=0.12, color='#cc3333')
    ax.axvspan(4, max_probes, alpha=0.06, color='#33aa33')

    # Region labels
    ax.annotate('BASELINE', xy=(1.5, 0.95), fontsize=10, ha='center',
               color='#3366cc', fontweight='bold')
    ax.annotate('STEP', xy=(3.5, 0.95), fontsize=10, ha='center',
               color='#cc3333', fontweight='bold')
    ax.annotate('RECOVERY', xy=(14, 0.95), fontsize=10, ha='center',
               color='#33aa33', fontweight='bold')

    ax.set_xlabel('Probe Index', fontsize=12, fontweight='bold')
    ax.set_ylabel('Cosine Distance from Baseline', fontsize=12, fontweight='bold')
    ax.set_title('Run 023d: Fleet-Wide Identity Waveforms (25 Models)',
                fontsize=14, fontweight='bold')

    ax.set_xlim(0, max_probes - 1)
    ax.set_ylim(0, 1.0)
    ax.grid(True, alpha=0.3)

    # Color-coded legend for providers
    from matplotlib.lines import Line2D
    provider_handles = [Line2D([0], [0], color=PROVIDER_COLORS[p], linewidth=3,
                              label=p.upper()) for p in sorted(PROVIDER_COLORS.keys())]
    ax.legend(handles=provider_handles, loc='upper right', fontsize=10,
             framealpha=0.9, title='Providers')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'fleet_waveform_comparison.{ext}'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_individual_model_detailed(by_model, output_dir, n_models=6):
    """Create detailed individual model waveform plots (archive style)."""
    # Select top N models by sample size
    models = sorted(by_model.keys(), key=lambda x: len(by_model[x]), reverse=True)
    models = models[:n_models]

    for provider, model in models:
        results = by_model[(provider, model)]
        color = PROVIDER_COLORS.get(provider, '#888888')

        fig, ax = plt.subplots(figsize=(12, 6))
        fig.patch.set_facecolor('white')
        ax.set_facecolor('#fafafa')

        max_probes = 25

        all_traces = []
        for r in results:
            probes = r.get('probe_sequence', [])
            drifts = [p.get('drift', 0) for p in probes]
            if drifts:
                all_traces.append(drifts)

        if not all_traces:
            plt.close()
            continue

        # Pad
        padded = []
        for trace in all_traces:
            if len(trace) < max_probes:
                trace = trace + [trace[-1]] * (max_probes - len(trace))
            padded.append(trace[:max_probes])

        arr = np.array(padded)
        x = np.arange(max_probes)

        # Plot all traces with gradient transparency
        for i, trace in enumerate(padded):
            alpha = 0.3 + (i / len(padded)) * 0.4
            ax.plot(x, trace, '-', linewidth=1.2, alpha=alpha, color=color)

        # Mean and std envelope
        mean_trace = np.mean(arr, axis=0)
        std_trace = np.std(arr, axis=0)

        ax.fill_between(x, mean_trace - std_trace, mean_trace + std_trace,
                       alpha=0.25, color=color)
        ax.plot(x, mean_trace, '-', linewidth=3, color=color,
               label=f'Mean (n={len(results)})')

        # Event Horizon
        ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2,
                  alpha=0.9, label='Event Horizon')

        # Probe regions
        ax.axvspan(0, 3, alpha=0.08, color='#3366cc')
        ax.axvspan(3, 4, alpha=0.15, color='#cc3333')
        ax.axvspan(4, max_probes, alpha=0.06, color='#33aa33')

        short_name = short_model_name(model)
        ax.set_title(f'{short_name}\n({provider.upper()} | n={len(results)} experiments)',
                    fontsize=14, fontweight='bold')
        ax.set_xlabel('Probe Index', fontsize=12)
        ax.set_ylabel('Cosine Distance from Baseline', fontsize=12)

        ax.set_xlim(0, max_probes - 1)
        ax.set_ylim(0, 1.0)
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper right', fontsize=10, framealpha=0.9)

        # Stats box
        stats_text = f"Peak: {np.max(mean_trace):.3f}\nSettled: {mean_trace[-1]:.3f}\nSTD: {np.mean(std_trace):.3f}"
        ax.annotate(stats_text, xy=(0.02, 0.98), xycoords='axes fraction',
                   fontsize=10, va='top', ha='left',
                   bbox=dict(boxstyle='round', facecolor='white', edgecolor='gray', alpha=0.9))

        plt.tight_layout()

        # Save with sanitized filename
        safe_name = model.replace('/', '_').replace(':', '_')[:50]
        for ext in ['png', 'svg']:
            output_path = output_dir / f'waveform_{safe_name}.{ext}'
            plt.savefig(output_path, dpi=150, bbox_inches='tight')
            print(f"Saved: {output_path}")

        plt.close()

def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nGrouping by model...")
    by_model = group_by_model(results)
    print(f"Found {len(by_model)} unique models")

    print("\nGenerating visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_model_waveform_grid(by_model, OUTPUT_DIR)
    plot_provider_waveform_overlay(by_model, OUTPUT_DIR)
    plot_fleet_comparison(by_model, OUTPUT_DIR)
    plot_individual_model_detailed(by_model, OUTPUT_DIR, n_models=6)

    print("\n" + "="*70)
    print("MODEL WAVEFORM GENERATION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
