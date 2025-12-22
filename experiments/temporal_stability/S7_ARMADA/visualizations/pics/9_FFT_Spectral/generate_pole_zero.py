#!/usr/bin/env python3
"""
Pole-Zero Landscape Analysis for 9_FFT_Spectral
================================================
Creates pole-zero analysis showing baseline drift vs perturbation drift,
identifying "hard poles" (rigid behavior) vs "soft poles" (flexible).

Inspired by: pole_zero_landscape_2d.png from archive
Data source: Run 023d (IRON CLAD Foundation)
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

def load_data():
    """Load Run 023d results."""
    data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])

def extract_pole_zero_data(results):
    """
    Extract baseline drift and perturbation response for pole-zero analysis.

    Concept:
    - Baseline drift: Result-level baseline_drift (aggregated measure)
    - Perturbation drift: How much the model responds to step_input challenge
    - Hard poles: Models that hit a ceiling and can't be pushed further
    - Soft poles: Models that respond proportionally to perturbation
    """
    pz_data = []

    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')

        probes = r.get('probe_sequence', [])
        if len(probes) < 5:
            continue

        # Get baseline drift from result level (NOT individual probes which are 0 by definition)
        baseline_drift = r.get('baseline_drift', 0)

        # Find step_input and recovery drifts from probe sequence
        step_input_drift = None
        recovery_drift = None

        for probe in probes:
            drift = probe.get('drift', 0)
            probe_type = probe.get('probe_type', probe.get('type', ''))

            if probe_type == 'step_input' and step_input_drift is None:
                step_input_drift = drift
            elif probe_type == 'recovery' and recovery_drift is None:
                recovery_drift = drift

        if step_input_drift is None:
            continue

        pz_data.append({
            'provider': provider,
            'model': model,
            'baseline_drift': baseline_drift,
            'baseline_max': baseline_drift,  # Use result-level value
            'step_input_drift': step_input_drift,
            'recovery_drift': recovery_drift or step_input_drift,
            'peak_drift': r.get('peak_drift', 0),
            'settled_drift': r.get('settled_drift', 0),
            'stable': r.get('naturally_settled', False)
        })

    return pz_data

def plot_pole_zero_landscape(pz_data, output_dir):
    """Create pole-zero landscape plot."""
    fig, ax = plt.subplots(figsize=(12, 10))
    ax.set_facecolor('#f5f5f5')
    fig.patch.set_facecolor('white')

    # Define hard pole ceiling
    HARD_POLE_CEILING = 0.30

    # Aggregate by model
    model_data = defaultdict(list)
    for d in pz_data:
        key = (d['provider'], d['model'])
        model_data[key].append(d)

    # Plot each model as a point
    for (provider, model), data_points in model_data.items():
        baseline_drifts = [d['baseline_drift'] for d in data_points]
        step_drifts = [d['step_input_drift'] for d in data_points]

        x = np.mean(baseline_drifts)
        y = np.mean(step_drifts)

        color = PROVIDER_COLORS.get(provider, '#888888')

        # Determine if soft pole (flexible) or near hard pole
        is_soft_pole = y < HARD_POLE_CEILING and x < 0.15

        if is_soft_pole:
            # Soft pole: circle with green outline
            ax.scatter([x], [y], s=200, c=color, marker='o',
                      edgecolors='#2ecc71', linewidths=3, alpha=0.8, zorder=5)
        else:
            # Regular point
            ax.scatter([x], [y], s=150, c=color, marker='o',
                      edgecolors='white', linewidths=1.5, alpha=0.7, zorder=4)

    # Hard pole ceiling reference line
    ax.axhline(y=HARD_POLE_CEILING, color='#e74c3c', linestyle=':', linewidth=2.5,
               alpha=0.8, label=f'Hard Pole Ceiling ({HARD_POLE_CEILING})')

    # No change diagonal
    diag_x = np.linspace(0, 0.35, 100)
    ax.plot(diag_x, diag_x, '--', color='#95a5a6', linewidth=2, alpha=0.7,
            label='No Change Line')

    # Event Horizon reference
    ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=1.5,
               alpha=0.5, label='Event Horizon (0.80)')

    # Provider legend
    legend_handles = []
    providers = sorted(set(d['provider'] for d in pz_data))
    for provider in providers:
        color = PROVIDER_COLORS.get(provider, '#888888')
        handle = plt.scatter([], [], c=color, s=100, label=provider.upper())
        legend_handles.append(handle)

    # Add soft pole indicator to legend
    soft_pole_handle = plt.scatter([], [], c='white', s=100, marker='o',
                                   edgecolors='#2ecc71', linewidths=3,
                                   label='Soft Poles (Flexible)')
    legend_handles.append(soft_pole_handle)

    ax.set_xlabel('Baseline Drift', fontsize=12, fontweight='bold')
    ax.set_ylabel('Step Input Drift', fontsize=12, fontweight='bold')

    n_models = len(model_data)
    ax.set_title(f'S7 Run 023d: Baseline vs Perturbation Drift (Pole-Zero Map)\n{n_models} Models - Hard Poles vs Soft Poles',
                fontsize=14, fontweight='bold')

    ax.set_xlim(-0.01, 0.35)
    ax.set_ylim(-0.01, max(0.35, max(d['step_input_drift'] for d in pz_data) + 0.05))
    ax.grid(True, alpha=0.3)

    ax.legend(handles=legend_handles, loc='upper left', fontsize=9)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'pole_zero_landscape.{ext}'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_pole_strength_distribution(pz_data, output_dir):
    """Create distribution plot of pole strengths by provider - LIGHT MODE."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    fig.patch.set_facecolor('white')

    for ax in axes:
        ax.set_facecolor('white')

    # Panel 1: Baseline drift distribution by provider
    ax1 = axes[0]
    providers = sorted(set(d['provider'] for d in pz_data))

    baseline_by_provider = {p: [d['baseline_drift'] for d in pz_data if d['provider'] == p] for p in providers}

    positions = np.arange(len(providers))
    bp1 = ax1.boxplot([baseline_by_provider[p] for p in providers],
                      positions=positions, patch_artist=True, widths=0.6)

    for i, (box, provider) in enumerate(zip(bp1['boxes'], providers)):
        box.set_facecolor(PROVIDER_COLORS.get(provider, '#888888'))
        box.set_alpha(0.7)
        box.set_edgecolor('black')

    for whisker in bp1['whiskers']:
        whisker.set_color('black')
    for cap in bp1['caps']:
        cap.set_color('black')
    for median in bp1['medians']:
        median.set_color('black')
        median.set_linewidth(2)

    ax1.set_xticks(positions)
    ax1.set_xticklabels([p.upper()[:8] for p in providers], color='black', fontsize=9)
    ax1.set_ylabel('Baseline Drift', color='black', fontsize=11)
    ax1.set_title('Baseline Drift by Provider', color='black', fontsize=12, fontweight='bold')
    ax1.tick_params(colors='black')
    ax1.grid(axis='y', alpha=0.3)
    for spine in ax1.spines.values():
        spine.set_color('#cccccc')

    # Panel 2: Perturbation response distribution by provider
    ax2 = axes[1]
    step_by_provider = {p: [d['step_input_drift'] for d in pz_data if d['provider'] == p] for p in providers}

    bp2 = ax2.boxplot([step_by_provider[p] for p in providers],
                      positions=positions, patch_artist=True, widths=0.6)

    for i, (box, provider) in enumerate(zip(bp2['boxes'], providers)):
        box.set_facecolor(PROVIDER_COLORS.get(provider, '#888888'))
        box.set_alpha(0.7)
        box.set_edgecolor('black')

    for whisker in bp2['whiskers']:
        whisker.set_color('black')
    for cap in bp2['caps']:
        cap.set_color('black')
    for median in bp2['medians']:
        median.set_color('black')
        median.set_linewidth(2)

    # Hard pole reference
    ax2.axhline(y=0.30, color='#e74c3c', linestyle=':', linewidth=2, alpha=0.8, label='Hard Pole Ceiling')

    ax2.set_xticks(positions)
    ax2.set_xticklabels([p.upper()[:8] for p in providers], color='black', fontsize=9)
    ax2.set_ylabel('Step Input Drift', color='black', fontsize=11)
    ax2.set_title('Perturbation Response by Provider', color='black', fontsize=12, fontweight='bold')
    ax2.tick_params(colors='black')
    ax2.grid(axis='y', alpha=0.3)
    ax2.legend(loc='upper right', facecolor='white', edgecolor='#cccccc')
    for spine in ax2.spines.values():
        spine.set_color('#cccccc')

    fig.suptitle('Pole Strength Analysis: Run 023d', fontsize=14, fontweight='bold', color='black', y=1.02)
    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'pole_strength_distribution.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nExtracting pole-zero data...")
    pz_data = extract_pole_zero_data(results)
    print(f"Extracted {len(pz_data)} valid experiments")

    print("\nGenerating pole-zero visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_pole_zero_landscape(pz_data, OUTPUT_DIR)
    plot_pole_strength_distribution(pz_data, OUTPUT_DIR)

    print("\n" + "="*70)
    print("POLE-ZERO ANALYSIS COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
