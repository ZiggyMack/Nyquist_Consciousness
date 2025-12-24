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
from matplotlib.lines import Line2D
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

def plot_single_waveform_panel(ax, provider, model, results, max_probes=25):
    """Helper function to plot a single model waveform panel."""
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
        return

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

    # Always add axis labels (per user request)
    ax.set_xlabel('Probe', fontsize=8)
    ax.set_ylabel('Drift', fontsize=8)


def plot_model_waveform_grid_4x4(by_model, output_dir):
    """Create 4x4 grid visualizations split into two files.

    File 1: Major Providers (Anthropic, OpenAI, Google, xAI)
    File 2: Together.ai Models grouped by family (DeepSeek, Llama, Qwen, Others)

    Per user request: 4x4 layout, always show x-axis labels ("Probe")
    """
    max_probes = 25

    # Separate models by provider type
    major_providers = ['anthropic', 'openai', 'google', 'xai']

    major_models = [(p, m) for (p, m) in by_model.keys() if p in major_providers]
    together_models = [(p, m) for (p, m) in by_model.keys() if p == 'together']

    # Sort major providers
    major_models = sorted(major_models, key=lambda x: (major_providers.index(x[0]), x[1]))

    # =========================================================================
    # FILE 1: Major Providers (4x4 grid)
    # =========================================================================
    if major_models:
        n_major = len(major_models)
        rows, cols = 4, 4

        fig, axes = plt.subplots(rows, cols, figsize=(16, 16))
        fig.patch.set_facecolor('white')
        axes_flat = axes.flatten()

        for ax in axes_flat:
            ax.set_facecolor('#fafafa')

        for idx, (provider, model) in enumerate(major_models[:16]):
            ax = axes_flat[idx]
            results = by_model[(provider, model)]
            plot_single_waveform_panel(ax, provider, model, results, max_probes)

        # Hide unused panels
        for idx in range(len(major_models), 16):
            axes_flat[idx].set_visible(False)

        fig.suptitle(f'Run 023d: Major Provider Identity Waveforms\n(Anthropic, OpenAI, Google, xAI - {len(major_models)} models)',
                    fontsize=14, fontweight='bold', y=0.995)

        plt.tight_layout(rect=[0, 0, 1, 0.97])

        for ext in ['png', 'svg']:
            output_path = output_dir / f'waveforms_major_providers.{ext}'
            plt.savefig(output_path, dpi=150, bbox_inches='tight')
            print(f"Saved: {output_path}")

        plt.close()

    # =========================================================================
    # FILE 2: Together.ai Models (4x4 grid) - grouped by family
    # =========================================================================
    if together_models:
        # Group Together models by family
        def get_model_family(model_name):
            name_lower = model_name.lower()
            if 'deepseek' in name_lower:
                return 'DeepSeek'
            elif 'llama' in name_lower or 'meta-llama' in name_lower:
                return 'Llama'
            elif 'qwen' in name_lower:
                return 'Qwen'
            elif 'kimi' in name_lower or 'moonshot' in name_lower:
                return 'Kimi'
            elif 'mistral' in name_lower:
                return 'Mistral'
            elif 'nvidia' in name_lower or 'nemotron' in name_lower:
                return 'Nvidia'
            else:
                return 'Other'

        # Sort by family, then by model name
        family_order = ['DeepSeek', 'Llama', 'Qwen', 'Kimi', 'Mistral', 'Nvidia', 'Other']
        together_models_sorted = sorted(together_models,
            key=lambda x: (family_order.index(get_model_family(x[1]))
                          if get_model_family(x[1]) in family_order else 99, x[1]))

        n_together = len(together_models_sorted)
        rows, cols = 4, 4

        fig, axes = plt.subplots(rows, cols, figsize=(16, 16))
        fig.patch.set_facecolor('white')
        axes_flat = axes.flatten()

        for ax in axes_flat:
            ax.set_facecolor('#fafafa')

        for idx, (provider, model) in enumerate(together_models_sorted[:16]):
            ax = axes_flat[idx]
            results = by_model[(provider, model)]

            # Custom title with family label
            family = get_model_family(model)
            plot_single_waveform_panel(ax, provider, model, results, max_probes)

            # Override title to include family
            short_name = short_model_name(model)
            ax.set_title(f'{short_name}\n({family})', fontsize=9, fontweight='bold',
                        color=PROVIDER_COLORS.get('together', '#7C3AED'))

        # Hide unused panels
        for idx in range(len(together_models_sorted), 16):
            axes_flat[idx].set_visible(False)

        # Get family counts for subtitle
        family_counts = defaultdict(int)
        for _, model in together_models_sorted:
            family_counts[get_model_family(model)] += 1
        family_summary = ', '.join([f'{f}: {c}' for f, c in sorted(family_counts.items()) if c > 0])

        fig.suptitle(f'Run 023d: Together.ai Identity Waveforms\n({family_summary})',
                    fontsize=14, fontweight='bold', y=0.995)

        plt.tight_layout(rect=[0, 0, 1, 0.97])

        for ext in ['png', 'svg']:
            output_path = output_dir / f'waveforms_together_models.{ext}'
            plt.savefig(output_path, dpi=150, bbox_inches='tight')
            print(f"Saved: {output_path}")

        plt.close()


def plot_fleet_wide_waveform_comparison(by_model, output_dir):
    """Create fleet-wide waveform comparison showing all model means overlaid.

    Shows all 25 model mean waveforms on one plot, color-coded by provider.
    Includes BASELINE, STEP, RECOVERY region shading and Event Horizon line.
    """
    max_probes = 25

    fig, ax = plt.subplots(figsize=(14, 8))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('#fafafa')

    # Track providers for legend
    provider_handles = {}

    for (provider, model), results in by_model.items():
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Extract all probe sequences
        all_traces = []
        for r in results:
            probes = r.get('probe_sequence', [])
            drifts = [p.get('drift', 0) for p in probes]
            if drifts:
                all_traces.append(drifts)

        if not all_traces:
            continue

        # Pad to same length
        padded = []
        for trace in all_traces:
            if len(trace) < max_probes:
                trace = trace + [trace[-1]] * (max_probes - len(trace))
            padded.append(trace[:max_probes])

        arr = np.array(padded)
        x = np.arange(max_probes)

        # Plot mean waveform
        mean_trace = np.mean(arr, axis=0)
        line, = ax.plot(x, mean_trace, '-', linewidth=1.5, alpha=0.7, color=color)

        # Store one handle per provider for legend
        if provider not in provider_handles:
            provider_handles[provider] = line

    # Probe region shading
    ax.axvspan(0, 3, alpha=0.08, color='#3366cc', label='BASELINE')
    ax.axvspan(3, 4, alpha=0.15, color='#cc3333', label='STEP')
    ax.axvspan(4, max_probes, alpha=0.06, color='#33aa33', label='RECOVERY')

    # Add region labels at top
    ax.text(1.5, 0.95, 'BASELINE', ha='center', va='top', fontsize=10,
            color='#3366cc', fontweight='bold', transform=ax.get_xaxis_transform())
    ax.text(3.5, 0.95, 'STEP', ha='center', va='top', fontsize=10,
            color='#cc3333', fontweight='bold', transform=ax.get_xaxis_transform())
    ax.text(14, 0.95, 'RECOVERY', ha='center', va='top', fontsize=10,
            color='#33aa33', fontweight='bold', transform=ax.get_xaxis_transform())

    # Event Horizon
    ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2,
              alpha=0.9, label='Event Horizon')

    ax.set_title(f'Run 023d: Fleet-Wide Identity Waveforms ({len(by_model)} Models)',
                fontsize=14, fontweight='bold')
    ax.set_xlabel('Probe Index', fontsize=12)
    ax.set_ylabel('Cosine Distance from Baseline', fontsize=12)

    ax.set_xlim(0, max_probes - 1)
    ax.set_ylim(0, 1.0)
    ax.grid(True, alpha=0.3)

    # Provider legend
    provider_legend_handles = []
    provider_legend_labels = []
    for provider in ['anthropic', 'openai', 'google', 'xai', 'together']:
        if provider in provider_handles:
            provider_legend_handles.append(provider_handles[provider])
            provider_legend_labels.append(provider.upper())

    # Add Event Horizon to legend
    eh_handle = Line2D([0], [0], color='#ff4444', linestyle='--', linewidth=2)
    provider_legend_handles.append(eh_handle)
    provider_legend_labels.append('Event Horizon')

    ax.legend(provider_legend_handles, provider_legend_labels,
             loc='upper right', fontsize=10, framealpha=0.9, title='Providers')

    # Caption
    fig.text(0.5, 0.02, 'All 25 model mean waveforms overlaid. Color indicates provider.',
            ha='center', fontsize=10, style='italic')

    plt.tight_layout(rect=[0, 0.04, 1, 1])

    for ext in ['png', 'svg']:
        output_path = output_dir / f'fleet_waveform_comparison.{ext}'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()


def plot_individual_model_detailed(by_model, output_dir, n_models=6):
    """Create detailed individual model waveform plots with uncertainty bounds."""
    # Select top N models by sample size
    models = sorted(by_model.keys(), key=lambda x: len(by_model[x]), reverse=True)
    models = models[:n_models]

    max_probes = 25

    for provider, model in models:
        results = by_model[(provider, model)]
        color = PROVIDER_COLORS.get(provider, '#888888')

        fig, ax = plt.subplots(figsize=(12, 6))
        fig.patch.set_facecolor('white')
        ax.set_facecolor('#fafafa')

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

    # Fleet-wide comparison (all model means overlaid)
    plot_fleet_wide_waveform_comparison(by_model, OUTPUT_DIR)

    # 4x4 grid layouts (two files: major providers + Together.ai families)
    plot_model_waveform_grid_4x4(by_model, OUTPUT_DIR)

    # Individual model detailed views (top 6 by sample size)
    plot_individual_model_detailed(by_model, OUTPUT_DIR, n_models=6)

    print("\n" + "="*70)
    print("MODEL WAVEFORM GENERATION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
