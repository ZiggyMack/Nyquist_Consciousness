#!/usr/bin/env python3
"""
Perturbation Response Analysis for 9_FFT_Spectral
==================================================
Creates perturbation response analysis showing settled drift vs step response,
identifying "resilient" (good recovery) vs "vulnerable" (poor recovery) models.

NOTE: Previously named "pole-zero" but renamed to avoid confusion with
actual Laplace domain pole-zero analysis (see 16_Laplace_Analysis/).

Concept:
- Settled drift (x-axis): Permanent identity change after recovery attempt
- Step input drift (y-axis): Immediate response to value challenge
- Resilient: Models that respond but recover well (high y, low x)
- Vulnerable: Models that respond and stay shifted (high on both axes)

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

def extract_perturbation_data(results):
    """
    Extract settled drift and perturbation response for recovery analysis.

    Concept:
    - Settled drift (x-axis): Model's "resting state" after perturbation - how much permanent drift remains
    - Step input drift (y-axis): Immediate response to value challenge - perturbation sensitivity
    - Resilient: Models with high step response that recover well (high y, low x)
    - Vulnerable: Models that respond strongly and can't recover (high on both axes)

    Note: baseline_drift is 0 by definition (baseline probes ARE the reference).
    We use settled_drift as the meaningful x-axis metric.
    """
    pr_data = []

    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')

        probes = r.get('probe_sequence', [])
        if len(probes) < 5:
            continue

        # settled_drift is the meaningful "resting state" metric
        settled_drift = r.get('settled_drift', 0)
        peak_drift = r.get('peak_drift', 0)

        # Find step_input drift from probe sequence
        step_input_drift = None
        first_recovery_drift = None

        for probe in probes:
            drift = probe.get('drift', 0)
            probe_type = probe.get('probe_type', probe.get('type', ''))

            if probe_type == 'step_input' and step_input_drift is None:
                step_input_drift = drift
            elif probe_type == 'recovery' and first_recovery_drift is None:
                first_recovery_drift = drift

        if step_input_drift is None:
            continue

        pr_data.append({
            'provider': provider,
            'model': model,
            'settled_drift': settled_drift,  # X-axis: permanent drift after recovery
            'step_input_drift': step_input_drift,  # Y-axis: perturbation response
            'first_recovery_drift': first_recovery_drift or step_input_drift,
            'peak_drift': peak_drift,
            'stable': r.get('naturally_settled', False)
        })

    return pr_data

def plot_perturbation_landscape(pr_data, output_dir):
    """Create perturbation response landscape plot - LIGHT MODE.

    X-axis: Settled drift (permanent identity change after recovery)
    Y-axis: Step input drift (immediate perturbation response)

    Interpretation:
    - Bottom-left: Resilient (low response, full recovery) - STABLE
    - Top-left: Flexible (high response, good recovery) - ADAPTIVE
    - Top-right: Vulnerable (high response, poor recovery) - AT RISK
    - Bottom-right: Resistant but stuck (low response, poor recovery)
    """
    fig, ax = plt.subplots(figsize=(12, 10))
    ax.set_facecolor('#f8f8f8')
    fig.patch.set_facecolor('white')

    # Define thresholds
    RECOVERY_THRESHOLD = 0.30  # Below this settled drift = good recovery
    RESPONSE_THRESHOLD = 0.50  # Below this step response = low sensitivity

    # Aggregate by model
    model_data = defaultdict(list)
    for d in pr_data:
        key = (d['provider'], d['model'])
        model_data[key].append(d)

    # Plot each model as a point
    for (provider, model), data_points in model_data.items():
        settled_drifts = [d['settled_drift'] for d in data_points]
        step_drifts = [d['step_input_drift'] for d in data_points]

        x = np.mean(settled_drifts)  # Permanent drift after recovery
        y = np.mean(step_drifts)      # Immediate perturbation response

        color = PROVIDER_COLORS.get(provider, '#888888')

        # Classify: Resilient = good recovery (low settled drift)
        is_resilient = x < RECOVERY_THRESHOLD

        if is_resilient:
            # Resilient: recovers well - green outline
            ax.scatter([x], [y], s=200, c=color, marker='o',
                      edgecolors='#2ecc71', linewidths=3, alpha=0.8, zorder=5)
        else:
            # Vulnerable: doesn't recover well - red outline
            ax.scatter([x], [y], s=180, c=color, marker='s',
                      edgecolors='#e74c3c', linewidths=2, alpha=0.8, zorder=5)

    # Reference lines - store handles for legend
    recovery_line = ax.axvline(x=RECOVERY_THRESHOLD, color='#2ecc71', linestyle=':', linewidth=2,
                               alpha=0.7)
    response_line = ax.axhline(y=RESPONSE_THRESHOLD, color='#3498db', linestyle=':', linewidth=2,
                               alpha=0.7)

    # Event Horizon reference
    eh_line = ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2,
                         alpha=0.7)
    ax.axvline(x=0.80, color='#ff4444', linestyle='--', linewidth=2,
               alpha=0.7)

    # Diagonal: x=y (settled = step response = no recovery at all)
    max_val = max(max(d['settled_drift'] for d in pr_data),
                  max(d['step_input_drift'] for d in pr_data)) + 0.1
    diag_x = np.linspace(0, max_val, 100)
    diag_line, = ax.plot(diag_x, diag_x, '--', color='#95a5a6', linewidth=1.5, alpha=0.5)

    # Provider legend (upper left)
    legend_handles = []
    providers = sorted(set(d['provider'] for d in pr_data))
    for provider in providers:
        color = PROVIDER_COLORS.get(provider, '#888888')
        handle = plt.scatter([], [], c=color, s=100, label=provider.upper())
        legend_handles.append(handle)

    # Add recovery type indicators to legend
    resilient_handle = plt.scatter([], [], c='gray', s=100, marker='o',
                              edgecolors='#2ecc71', linewidths=3,
                              label='Resilient (recovers)')
    vulnerable_handle = plt.scatter([], [], c='gray', s=100, marker='s',
                              edgecolors='#e74c3c', linewidths=2,
                              label='Vulnerable (stuck)')
    legend_handles.extend([resilient_handle, vulnerable_handle])

    # Reference lines legend (bottom right)
    from matplotlib.lines import Line2D
    line_handles = [
        Line2D([0], [0], color='#2ecc71', linestyle=':', linewidth=2, label=f'Recovery Threshold ({RECOVERY_THRESHOLD})'),
        Line2D([0], [0], color='#3498db', linestyle=':', linewidth=2, label=f'Response Threshold ({RESPONSE_THRESHOLD})'),
        Line2D([0], [0], color='#ff4444', linestyle='--', linewidth=2, label='Event Horizon (0.80)'),
        Line2D([0], [0], color='#95a5a6', linestyle='--', linewidth=1.5, label='No Recovery (x=y)'),
    ]

    ax.set_xlabel('Settled Drift (Permanent Identity Change)', fontsize=12,
                  fontweight='bold', color='black')
    ax.set_ylabel('Step Input Drift (Perturbation Response)', fontsize=12,
                  fontweight='bold', color='black')

    n_models = len(model_data)
    n_resilient = sum(1 for (p,m), pts in model_data.items()
                 if np.mean([d['settled_drift'] for d in pts]) < RECOVERY_THRESHOLD)
    ax.set_title(f'S7 Run 023d: Perturbation Response Map\n'
                 f'{n_models} Models: {n_resilient} Resilient, {n_models - n_resilient} Vulnerable',
                fontsize=14, fontweight='bold', color='black')

    ax.set_xlim(-0.02, max_val)
    ax.set_ylim(-0.02, max_val)
    ax.grid(True, alpha=0.3, color='#cccccc')
    ax.tick_params(colors='black')

    for spine in ax.spines.values():
        spine.set_color('#cccccc')

    # Main legend (upper left) - providers and recovery types
    legend1 = ax.legend(handles=legend_handles, loc='upper left', fontsize=9,
                        facecolor='white', edgecolor='#cccccc', title='Providers & Recovery')
    legend1.get_title().set_fontweight('bold')
    ax.add_artist(legend1)

    # Reference lines legend (lower right)
    legend2 = ax.legend(handles=line_handles, loc='lower right', fontsize=9,
                        facecolor='white', edgecolor='#cccccc', title='Reference Lines')
    legend2.get_title().set_fontweight('bold')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'perturbation_response_landscape.{ext}'
        plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_recovery_distribution(pr_data, output_dir):
    """Create distribution plot of recovery metrics by provider - LIGHT MODE.

    Panel 1: Settled drift (permanent change) - lower is better recovery
    Panel 2: Step input drift (perturbation response) - sensitivity to challenges
    """
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    fig.patch.set_facecolor('white')

    for ax in axes:
        ax.set_facecolor('white')

    # Panel 1: Settled drift distribution by provider (permanent identity change)
    ax1 = axes[0]
    providers = sorted(set(d['provider'] for d in pr_data))

    settled_by_provider = {p: [d['settled_drift'] for d in pr_data if d['provider'] == p] for p in providers}

    positions = np.arange(len(providers))
    bp1 = ax1.boxplot([settled_by_provider[p] for p in providers],
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

    # Recovery threshold reference
    ax1.axhline(y=0.30, color='#2ecc71', linestyle=':', linewidth=2, alpha=0.8,
                label='Recovery Threshold (0.30)')

    ax1.set_xticks(positions)
    ax1.set_xticklabels([p.upper()[:8] for p in providers], color='black', fontsize=9)
    ax1.set_ylabel('Settled Drift (Permanent Change)', color='black', fontsize=11)
    ax1.set_title('Identity Recovery by Provider\n(Lower = Better Recovery)', color='black', fontsize=12, fontweight='bold')
    ax1.tick_params(colors='black')
    ax1.grid(axis='y', alpha=0.3)
    ax1.legend(loc='upper right', facecolor='white', edgecolor='#cccccc', fontsize=9)
    for spine in ax1.spines.values():
        spine.set_color('#cccccc')

    # Panel 2: Perturbation response distribution by provider
    ax2 = axes[1]
    step_by_provider = {p: [d['step_input_drift'] for d in pr_data if d['provider'] == p] for p in providers}

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

    # Vulnerability reference
    ax2.axhline(y=0.50, color='#e74c3c', linestyle=':', linewidth=2, alpha=0.8, label='Vulnerability Threshold')

    ax2.set_xticks(positions)
    ax2.set_xticklabels([p.upper()[:8] for p in providers], color='black', fontsize=9)
    ax2.set_ylabel('Step Input Drift', color='black', fontsize=11)
    ax2.set_title('Perturbation Response by Provider', color='black', fontsize=12, fontweight='bold')
    ax2.tick_params(colors='black')
    ax2.grid(axis='y', alpha=0.3)
    ax2.legend(loc='upper right', facecolor='white', edgecolor='#cccccc')
    for spine in ax2.spines.values():
        spine.set_color('#cccccc')

    fig.suptitle('Perturbation Response Analysis: Run 023d', fontsize=14, fontweight='bold', color='black', y=1.02)
    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'recovery_distribution.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nExtracting perturbation response data...")
    pr_data = extract_perturbation_data(results)
    print(f"Extracted {len(pr_data)} valid experiments")

    print("\nGenerating perturbation response visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_perturbation_landscape(pr_data, OUTPUT_DIR)
    plot_recovery_distribution(pr_data, OUTPUT_DIR)

    print("\n" + "="*70)
    print("PERTURBATION RESPONSE ANALYSIS COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
