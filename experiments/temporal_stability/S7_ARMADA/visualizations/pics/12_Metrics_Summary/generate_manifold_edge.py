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
    """Plot a single manifold edge detection panel with status labels."""
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

    # Baseline and recovery values
    baseline_val = np.mean(drifts[:3]) if len(drifts) >= 3 else drifts[0]
    recovery_val = np.mean(drifts[-3:]) if len(drifts) >= 3 else drifts[-1]
    peak_drift = example['peak_drift']
    crossed_eh = peak_drift > 0.80

    # ==========================================================================
    # STATUS LABELS - Show stability classification
    # ==========================================================================

    # Primary status badge (top-right corner)
    if example['is_hysteresis']:
        # Hysteresis = identity got stuck at elevated drift
        ax.annotate('STUCK', xy=(0.98, 0.98), xycoords='axes fraction',
                   fontsize=11, fontweight='bold', color='#d32f2f',
                   ha='right', va='top',
                   bbox=dict(boxstyle='round,pad=0.3', facecolor='#FFCDD2', edgecolor='#d32f2f'))
    elif crossed_eh:
        # Crossed Event Horizon but recovered
        ax.annotate('VOLATILE', xy=(0.98, 0.98), xycoords='axes fraction',
                   fontsize=11, fontweight='bold', color='#e65100',
                   ha='right', va='top',
                   bbox=dict(boxstyle='round,pad=0.3', facecolor='#FFE0B2', edgecolor='#e65100'))
    elif example['stable']:
        # Naturally settled without crossing EH
        ax.annotate('STABLE', xy=(0.98, 0.98), xycoords='axes fraction',
                   fontsize=11, fontweight='bold', color='#2e7d32',
                   ha='right', va='top',
                   bbox=dict(boxstyle='round,pad=0.3', facecolor='#C8E6C9', edgecolor='#2e7d32'))
    else:
        # Unsettled but didn't cross EH
        ax.annotate('UNSETTLED', xy=(0.98, 0.98), xycoords='axes fraction',
                   fontsize=10, fontweight='bold', color='#5d4037',
                   ha='right', va='top',
                   bbox=dict(boxstyle='round,pad=0.3', facecolor='#D7CCC8', edgecolor='#5d4037'))

    # Recovery ratio indicator (below status if hysteresis)
    if example['is_hysteresis']:
        recovery_pct = example['recovery_ratio'] * 100
        ax.annotate(f'Recovery: {recovery_pct:.0f}%', xy=(0.98, 0.88), xycoords='axes fraction',
                   fontsize=9, color='#d32f2f', ha='right', va='top')

    # ==========================================================================
    # INFO BOX (top-left) - Key metrics
    # ==========================================================================
    info_text = f"Baseline: {baseline_val:.2f}\nPeak: {peak_drift:.2f}\nRecovery: {recovery_val:.2f}"
    ax.annotate(info_text, xy=(0.02, 0.98), xycoords='axes fraction',
               fontsize=9, va='top', ha='left',
               bbox=dict(boxstyle='round', facecolor='white', edgecolor='gray', alpha=0.9))

    # ==========================================================================
    # FEATURE ANNOTATIONS on the plot itself
    # ==========================================================================

    # Mark the peak point
    peak_idx = np.argmax(drifts)
    if peak_drift > 0.3:  # Only annotate significant peaks
        ax.annotate('peak', xy=(peak_idx, drifts[peak_idx]),
                   xytext=(peak_idx, drifts[peak_idx] + 0.08),
                   fontsize=8, ha='center', color='#666666',
                   arrowprops=dict(arrowstyle='->', color='#999999', lw=0.8))

    # Explain near-zero baseline (cosine distance = 0 means identical to reference)
    if baseline_val < 0.05:
        ax.annotate('≈ baseline\n(identical)', xy=(1, baseline_val),
                   xytext=(2.5, 0.15),
                   fontsize=8, ha='center', color='#666666', style='italic',
                   arrowprops=dict(arrowstyle='->', color='#999999', lw=0.8))

    # Event Horizon line with label
    ax.axhline(y=0.80, color='#e74c3c', linestyle='--', linewidth=1.5, alpha=0.7)
    ax.annotate('Event Horizon', xy=(n_probes - 1, 0.82), fontsize=8,
               color='#e74c3c', ha='right', va='bottom', alpha=0.8)

    # Title and axes
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

def plot_hysteresis_summary_quad(edge_data, output_dir):
    """Create 2x2 QUAD hysteresis summary visualization - LIGHT MODE.

    Per VISUALIZATION_SPEC Pitfall #9: Use 2x2 quad layout, not 1x3 horizontal.
    Per Pitfall #10: Use Standard Error for proportion error bars.

    Layout:
    - Top-Left: Hysteresis Rate by Provider (bar chart with SE error bars)
    - Top-Right: Peak Drift by Provider (box plot)
    - Bottom-Left: Recovery Ratio Distribution (histogram)
    - Bottom-Right: Key Findings (text box)
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')

    for ax in axes.flatten():
        ax.set_facecolor('white')

    providers = sorted(set(d['provider'] for d in edge_data))
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]
    x = np.arange(len(providers))

    # =========================================================================
    # Panel 1 (Top-Left): Hysteresis Rate by Provider with SE error bars
    # =========================================================================
    ax1 = axes[0, 0]

    hysteresis_rates = []
    hysteresis_se = []  # Standard Error for proportions
    sample_counts = []

    for provider in providers:
        provider_data = [d for d in edge_data if d['provider'] == provider]
        n = len(provider_data)
        successes = sum(1 for d in provider_data if d['is_hysteresis'])
        p = successes / n if n > 0 else 0
        hysteresis_rates.append(p * 100)
        # Standard Error for proportion: sqrt(p*(1-p)/n) - per Pitfall #10
        se = np.sqrt(p * (1 - p) / n) * 100 if n > 0 else 0
        hysteresis_se.append(se)
        sample_counts.append(n)

    bars = ax1.bar(x, hysteresis_rates, yerr=hysteresis_se, capsize=5,
                   color=colors, edgecolor='black', linewidth=1, alpha=0.8)

    ax1.set_xticks(x)
    ax1.set_xticklabels([p.upper()[:8] for p in providers], fontsize=10, fontweight='bold')
    ax1.set_ylabel('Hysteresis Rate (%)', fontsize=11, fontweight='bold')
    ax1.set_title('Identity Stuck (Hysteresis) Rate by Provider', fontsize=12, fontweight='bold')
    ax1.grid(axis='y', alpha=0.3)
    ax1.set_ylim(0, max(hysteresis_rates) * 1.3 + 5)

    # Add percentage labels with sample size
    for bar, rate, n in zip(bars, hysteresis_rates, sample_counts):
        ax1.annotate(f'{rate:.1f}%\n(n={n})',
                    xy=(bar.get_x() + bar.get_width()/2, bar.get_height() + hysteresis_se[bars.index(bar)] + 1),
                    ha='center', va='bottom', color='black', fontsize=9, fontweight='bold')

    # =========================================================================
    # Panel 2 (Top-Right): Peak Drift by Provider (box plot)
    # =========================================================================
    ax2 = axes[0, 1]

    drift_by_provider = {p: [d['peak_drift'] for d in edge_data if d['provider'] == p] for p in providers}

    bp = ax2.boxplot([drift_by_provider[p] for p in providers],
                     positions=x, patch_artist=True, widths=0.6)

    for i, (box, provider) in enumerate(zip(bp['boxes'], providers)):
        box.set_facecolor(PROVIDER_COLORS.get(provider, '#888888'))
        box.set_alpha(0.7)
        box.set_edgecolor('black')

    for whisker in bp['whiskers']:
        whisker.set_color('black')
    for cap in bp['caps']:
        cap.set_color('black')
    for median in bp['medians']:
        median.set_color('black')
        median.set_linewidth(2)

    ax2.axhline(y=0.80, color='#e74c3c', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon (0.80)')
    ax2.set_xticks(x)
    ax2.set_xticklabels([p.upper()[:8] for p in providers], fontsize=10, fontweight='bold')
    ax2.set_ylabel('Peak Drift', fontsize=11, fontweight='bold')
    ax2.set_title('Peak Drift Distribution by Provider', fontsize=12, fontweight='bold')
    ax2.legend(loc='upper right', facecolor='white', edgecolor='#cccccc', fontsize=9)
    ax2.grid(axis='y', alpha=0.3)

    # =========================================================================
    # Panel 3 (Bottom-Left): Recovery Ratio Distribution (histogram)
    # =========================================================================
    ax3 = axes[1, 0]
    recovery_ratios = [d['recovery_ratio'] for d in edge_data]
    mean_recovery = np.mean(recovery_ratios)

    ax3.hist(recovery_ratios, bins=25, color='#9b59b6', alpha=0.7, edgecolor='black')
    ax3.axvline(0.2, color='#e74c3c', linestyle='--', linewidth=2, label='Hysteresis threshold (<0.2)')
    ax3.axvline(mean_recovery, color='#3498db', linestyle='-', linewidth=2,
               label=f'Mean: {mean_recovery:.2f}')

    ax3.set_xlabel('Recovery Ratio (0=stuck, 1=full recovery)', fontsize=11, fontweight='bold')
    ax3.set_ylabel('Frequency', fontsize=11)
    ax3.set_title('Recovery Ratio Distribution', fontsize=12, fontweight='bold')
    ax3.legend(loc='upper right', facecolor='white', edgecolor='#cccccc', fontsize=9)
    ax3.grid(alpha=0.3)
    ax3.set_xlim(-0.05, 1.05)

    # =========================================================================
    # Panel 4 (Bottom-Right): Key Findings Text Box
    # =========================================================================
    ax4 = axes[1, 1]
    ax4.set_facecolor('#f8f8f8')

    total_experiments = len(edge_data)
    unique_models = len(set(d['model'] for d in edge_data))
    hysteresis_total = sum(1 for d in edge_data if d['is_hysteresis'])
    hysteresis_pct = hysteresis_total / total_experiments * 100

    mean_peak = np.mean([d['peak_drift'] for d in edge_data])
    mean_settled = np.mean([d['settled_drift'] for d in edge_data])
    eh_crossings = sum(1 for d in edge_data if d['peak_drift'] > 0.80)
    eh_pct = eh_crossings / total_experiments * 100

    findings_text = f"""KEY FINDINGS: HYSTERESIS ANALYSIS

DATA SUMMARY:
  Total Experiments: {total_experiments}
  Unique Models: {unique_models}
  Providers: {len(providers)}

HYSTERESIS (Identity Stuck):
  Total Cases: {hysteresis_total} ({hysteresis_pct:.1f}%)
  Threshold: Recovery Ratio < 0.2
  Mean Recovery: {mean_recovery:.2f}

DRIFT METRICS:
  Mean Peak Drift: {mean_peak:.3f}
  Mean Settled Drift: {mean_settled:.3f}
  Event Horizon Crossings: {eh_pct:.1f}%

INTERPRETATION:
Hysteresis indicates identity "sticking" at
elevated drift levels after perturbation.
Lower recovery ratios = more stuck behavior.
"""

    ax4.text(0.05, 0.95, findings_text, transform=ax4.transAxes,
            fontsize=10, fontfamily='monospace', color='black',
            verticalalignment='top', horizontalalignment='left',
            bbox=dict(boxstyle='round', facecolor='white', edgecolor='#cccccc', alpha=0.9))
    ax4.axis('off')

    fig.suptitle('Run 023: Hysteresis & Recovery Analysis (COMBINED - 825 experiments × 51 models)',
                fontsize=14, fontweight='bold', y=0.98)
    plt.tight_layout(rect=[0, 0, 1, 0.96])

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

    # Generate hysteresis summary - now as 2x2 QUAD per VISUALIZATION_SPEC
    plot_hysteresis_summary_quad(edge_data, OUTPUT_DIR)

    print("\n" + "="*70)
    print("MANIFOLD EDGE DETECTION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
