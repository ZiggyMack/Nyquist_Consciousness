#!/usr/bin/env python3
"""
Identity Manifold Edge Detection for 12_Metrics_Summary
=======================================================
Recreates the Run 008 style manifold edge detection showing
gradual destabilization patterns and hysteresis detection.

Inspired by: run008_manifold_edge.png from archive
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

def load_data(combined=False):
    """Load Run 023d or COMBINED results."""
    if combined:
        data_file = RESULTS_DIR / "S7_run_023_COMBINED.json"
    else:
        data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])

def detect_hysteresis(probe_sequence):
    """
    Detect hysteresis (stuck) patterns in probe sequence.

    Hysteresis occurs when:
    - Drift increases but doesn't recover
    - System gets "stuck" at a higher drift level

    Recovery ratio = how much drift RECOVERED (0 = none, 1 = full recovery)
    Formula: (peak_drift - final_drift) / peak_drift
    """
    drifts = [p.get('drift', 0) for p in probe_sequence]
    if len(drifts) < 5:
        return False, 0

    # Check for sustained high drift after step_input
    step_idx = None
    for i, p in enumerate(probe_sequence):
        if p.get('probe_type', p.get('type', '')) == 'step_input':
            step_idx = i
            break

    if step_idx is None or step_idx >= len(drifts) - 3:
        return False, 0

    # Get pre-step average and post-step average
    pre_avg = np.mean(drifts[:step_idx]) if step_idx > 0 else 0
    post_drifts = drifts[step_idx + 1:]

    if not post_drifts:
        return False, 0

    # Calculate recovery ratio: how much did we recover from peak?
    # 0 = no recovery (stuck at peak), 1 = full recovery (back to baseline)
    peak_drift = max(drifts)
    final_drift = drifts[-1]

    if peak_drift > 0.01:  # Avoid div by zero
        recovery_ratio = (peak_drift - final_drift) / peak_drift
        recovery_ratio = max(0, min(1, recovery_ratio))  # Clamp to 0-1
    else:
        recovery_ratio = 1.0  # No drift = fully stable

    # Check if drift stays elevated (hysteresis)
    post_avg = np.mean(post_drifts)

    # Hysteresis if recovery ratio < 20% (didn't recover much) AND elevated drift
    is_hysteresis = recovery_ratio < 0.2 and post_avg > pre_avg * 1.5

    return is_hysteresis, recovery_ratio

def extract_edge_data(results):
    """Extract manifold edge detection data."""
    edge_data = []

    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')
        probes = r.get('probe_sequence', [])

        if len(probes) < 5:
            continue

        # Get drift trajectory
        drifts = [p.get('drift', 0) for p in probes]

        # Detect hysteresis
        is_hysteresis, recovery_ratio = detect_hysteresis(probes)

        # Calculate weighted drift (later probes weighted more)
        weights = np.linspace(0.5, 1.5, len(drifts))
        weighted_drift = np.average(drifts, weights=weights)

        edge_data.append({
            'provider': provider,
            'model': model,
            'drifts': drifts,
            'peak_drift': r.get('peak_drift', max(drifts)),
            'settled_drift': r.get('settled_drift', drifts[-1] if drifts else 0),
            'weighted_drift': weighted_drift,
            'is_hysteresis': is_hysteresis,
            'recovery_ratio': recovery_ratio,
            'stable': r.get('naturally_settled', False),
            'settling_time': r.get('settling_time', len(drifts))
        })

    return edge_data

def select_interesting_examples(edge_data, n_per_category=3):
    """Select interesting examples for manifold edge visualization."""
    # Group by pattern type
    hysteresis_examples = [d for d in edge_data if d['is_hysteresis']]
    stable_examples = [d for d in edge_data if d['stable'] and not d['is_hysteresis']]
    volatile_examples = [d for d in edge_data if not d['stable'] and not d['is_hysteresis']]

    # Sort by interestingness
    hysteresis_examples.sort(key=lambda x: x['recovery_ratio'], reverse=True)
    stable_examples.sort(key=lambda x: x['peak_drift'], reverse=True)
    volatile_examples.sort(key=lambda x: x['peak_drift'], reverse=True)

    selected = []
    selected.extend(hysteresis_examples[:n_per_category])
    selected.extend(stable_examples[:n_per_category])
    selected.extend(volatile_examples[:n_per_category])

    return selected

def plot_single_manifold_panel(ax, example, phase_colors):
    """Plot a single manifold edge detection panel."""
    drifts = example['drifts']
    n_probes = len(drifts)
    x = np.arange(n_probes)

    # Background intensity phases
    n_phases = min(5, n_probes)
    phase_width = n_probes / n_phases
    for i in range(n_phases):
        ax.axvspan(i * phase_width, (i + 1) * phase_width,
                  color=phase_colors[i], alpha=0.3, zorder=0)

    # Plot drift trajectory
    color = PROVIDER_COLORS.get(example['provider'], '#333333')
    ax.plot(x, drifts, 'o-', color=color, linewidth=2.5, markersize=8,
           markeredgecolor='white', markeredgewidth=1.5, zorder=3)

    # Mark hysteresis if detected
    if example['is_hysteresis']:
        ax.annotate('STUCK\n(hysteresis)', xy=(n_probes * 0.7, max(drifts) * 0.9),
                   fontsize=10, fontweight='bold', color='#d32f2f',
                   ha='center', va='center',
                   bbox=dict(boxstyle='round', facecolor='#FFCDD2', edgecolor='#d32f2f'))

    # Baseline and recovery annotations
    baseline_val = np.mean(drifts[:3]) if len(drifts) >= 3 else drifts[0]
    recovery_val = np.mean(drifts[-3:]) if len(drifts) >= 3 else drifts[-1]

    # Info box
    info_text = f"Baseline: {baseline_val:.2f}\nPeak: {example['peak_drift']:.2f}\nRecovery: {recovery_val:.2f}"
    ax.annotate(info_text, xy=(0.02, 0.98), xycoords='axes fraction',
               fontsize=9, va='top', ha='left',
               bbox=dict(boxstyle='round', facecolor='white', edgecolor='gray', alpha=0.9))

    # Event Horizon
    ax.axhline(y=0.80, color='#e74c3c', linestyle='--', linewidth=1.5, alpha=0.7)

    model_short = example['model'].split('/')[-1][:25]
    ax.set_title(f"{model_short}\n({example['provider']})",
                fontsize=11, fontweight='bold')
    ax.set_xlabel('Turn (Intensity Phase)', fontsize=10)
    ax.set_ylabel('Cosine Drift', fontsize=10)
    ax.set_xlim(-0.5, n_probes - 0.5)
    ax.set_ylim(0, max(1.0, max(drifts) * 1.1))
    ax.grid(True, alpha=0.3)


def plot_manifold_edge_quad(edge_data, output_dir):
    """Create 2 quad-panel manifold edge detection files (4 models each).

    File 1: Major Providers (Claude, GPT, Gemini, Grok)
    File 2: Together.ai Models (Kimi, DeepSeek, Llama, Nvidia)
    """
    phase_colors = ['#E8F5E9', '#FFF9C4', '#FFECB3', '#FFCCBC', '#FFCDD2']

    # Group edge_data by model for easy lookup
    by_model = defaultdict(list)
    for d in edge_data:
        by_model[d['model']].append(d)

    # Get best example per model (highest peak drift)
    def get_best_for_model(model_pattern, provider=None):
        candidates = []
        for model, examples in by_model.items():
            if model_pattern.lower() in model.lower():
                if provider is None or examples[0]['provider'] == provider:
                    best = max(examples, key=lambda x: x['peak_drift'])
                    candidates.append(best)
        if candidates:
            return max(candidates, key=lambda x: x['peak_drift'])
        return None

    # ==========================================================================
    # FILE 1: Major Providers (2x2 quad)
    # Claude (Anthropic) | GPT (OpenAI)
    # Gemini (Google)    | Grok (xAI)
    # ==========================================================================
    claude = get_best_for_model('claude', 'anthropic')
    gpt = get_best_for_model('gpt', 'openai')
    gemini = get_best_for_model('gemini', 'google')
    grok = get_best_for_model('grok', 'xai')

    if claude and gpt and gemini and grok:
        fig, axes = plt.subplots(2, 2, figsize=(14, 12))
        fig.patch.set_facecolor('white')

        plot_single_manifold_panel(axes[0, 0], claude, phase_colors)
        plot_single_manifold_panel(axes[0, 1], gpt, phase_colors)
        plot_single_manifold_panel(axes[1, 0], gemini, phase_colors)
        plot_single_manifold_panel(axes[1, 1], grok, phase_colors)

        fig.suptitle('Manifold Edge Detection: Major Providers\n(Anthropic, OpenAI, Google, xAI)',
                    fontsize=14, fontweight='bold', y=0.98)
        plt.tight_layout(rect=[0, 0, 1, 0.96])

        for ext in ['png', 'svg']:
            plt.savefig(output_dir / f'manifold_edge_major_providers.{ext}', dpi=150, bbox_inches='tight')
        print(f"Saved: manifold_edge_major_providers.png")
        plt.close()

    # ==========================================================================
    # FILE 2: Together.ai Models (2x2 quad)
    # Kimi      | DeepSeek
    # Llama     | Nvidia
    # ==========================================================================
    kimi = get_best_for_model('kimi', 'together')
    deepseek = get_best_for_model('deepseek', 'together')
    llama = get_best_for_model('llama', 'together')
    nvidia = get_best_for_model('nvidia', 'together') or get_best_for_model('nemotron', 'together')

    # Fallback if nvidia not available
    if not nvidia:
        nvidia = get_best_for_model('mistral', 'together')

    if kimi and deepseek and llama and nvidia:
        fig, axes = plt.subplots(2, 2, figsize=(14, 12))
        fig.patch.set_facecolor('white')

        plot_single_manifold_panel(axes[0, 0], kimi, phase_colors)
        plot_single_manifold_panel(axes[0, 1], deepseek, phase_colors)
        plot_single_manifold_panel(axes[1, 0], llama, phase_colors)
        plot_single_manifold_panel(axes[1, 1], nvidia, phase_colors)

        fig.suptitle('Manifold Edge Detection: Together.ai Models\n(Kimi, DeepSeek, Llama, Nvidia/Mistral)',
                    fontsize=14, fontweight='bold', y=0.98)
        plt.tight_layout(rect=[0, 0, 1, 0.96])

        for ext in ['png', 'svg']:
            plt.savefig(output_dir / f'manifold_edge_together_models.{ext}', dpi=150, bbox_inches='tight')
        print(f"Saved: manifold_edge_together_models.png")
        plt.close()

def plot_hysteresis_summary(edge_data, output_dir):
    """Create hysteresis summary visualization - LIGHT MODE."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    fig.patch.set_facecolor('white')

    for ax in axes:
        ax.set_facecolor('white')

    # Panel 1: Hysteresis rate by provider
    ax1 = axes[0]
    providers = sorted(set(d['provider'] for d in edge_data))

    hysteresis_rates = []
    for provider in providers:
        provider_data = [d for d in edge_data if d['provider'] == provider]
        rate = sum(1 for d in provider_data if d['is_hysteresis']) / len(provider_data) if provider_data else 0
        hysteresis_rates.append(rate * 100)

    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]
    x = np.arange(len(providers))

    bars = ax1.bar(x, hysteresis_rates, color=colors, edgecolor='black', linewidth=1, alpha=0.8)

    ax1.set_xticks(x)
    ax1.set_xticklabels([p.upper()[:8] for p in providers], fontsize=9)
    ax1.set_ylabel('Hysteresis Rate (%)', fontsize=11)
    ax1.set_title('Identity Stuck (Hysteresis) Rate by Provider', fontsize=12, fontweight='bold')
    ax1.grid(axis='y', alpha=0.3)

    # Add percentage labels
    for bar, rate in zip(bars, hysteresis_rates):
        if rate > 0:
            ax1.annotate(f'{rate:.1f}%', xy=(bar.get_x() + bar.get_width()/2, bar.get_height()),
                        ha='center', va='bottom', color='black', fontsize=10, fontweight='bold')

    # Panel 2: Recovery ratio distribution
    ax2 = axes[1]
    recovery_ratios = [d['recovery_ratio'] for d in edge_data]

    ax2.hist(recovery_ratios, bins=25, color='#9b59b6', alpha=0.7, edgecolor='black')
    ax2.axvline(0.2, color='#e74c3c', linestyle='--', linewidth=2, label='Hysteresis threshold (<0.2)')
    ax2.axvline(np.mean(recovery_ratios), color='#3498db', linestyle='-', linewidth=2,
               label=f'Mean: {np.mean(recovery_ratios):.2f}')

    ax2.set_xlabel('Recovery Ratio (0=stuck, 1=full recovery)', fontsize=11)
    ax2.set_ylabel('Frequency', fontsize=11)
    ax2.set_title('Recovery Ratio Distribution', fontsize=12, fontweight='bold')
    ax2.legend(facecolor='white', edgecolor='#cccccc')
    ax2.grid(alpha=0.3)
    ax2.set_xlim(-0.05, 1.05)  # Clamp x-axis to 0-1 range

    fig.suptitle('Run 023d: Hysteresis Analysis Summary', fontsize=14, fontweight='bold', y=1.02)
    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'hysteresis_summary.{ext}'
        plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def main():
    print("Loading Run 023 COMBINED data (51 models)...")
    results = load_data(combined=True)
    print(f"Loaded {len(results)} results")

    print("\nExtracting manifold edge data...")
    edge_data = extract_edge_data(results)
    print(f"Extracted {len(edge_data)} valid experiments")

    # Count unique models
    unique_models = set(d['model'] for d in edge_data)
    print(f"Unique models: {len(unique_models)}")

    hysteresis_count = sum(1 for d in edge_data if d['is_hysteresis'])
    print(f"Detected {hysteresis_count} hysteresis cases ({hysteresis_count/len(edge_data)*100:.1f}%)")

    print("\nGenerating visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Generate quad manifold edge files (4 models each, 2 files total)
    plot_manifold_edge_quad(edge_data, OUTPUT_DIR)

    # Generate hysteresis summary
    plot_hysteresis_summary(edge_data, OUTPUT_DIR)

    print("\n" + "="*70)
    print("MANIFOLD EDGE DETECTION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
