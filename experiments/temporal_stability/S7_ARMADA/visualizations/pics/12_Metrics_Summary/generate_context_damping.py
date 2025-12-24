#!/usr/bin/env python3
"""
Context Damping Effect Analysis for 12_Metrics_Summary
======================================================
Recreates the Run 017 context damping visualization showing
how recovery probes dampen identity drift over time.

Inspired by: run017_context_damping_effect.png from archive
Data source: Run 023d (IRON CLAD Foundation)
LIGHT MODE for publication
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict
from scipy import stats

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

def extract_damping_data(results):
    """Extract context damping metrics from probe sequences."""
    damping_data = []

    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')
        probes = r.get('probe_sequence', [])

        if len(probes) < 5:
            continue

        drifts = [p.get('drift', 0) for p in probes]

        step_idx = None
        for i, p in enumerate(probes):
            if p.get('probe_type', p.get('type', '')) == 'step_input':
                step_idx = i
                break

        if step_idx is None:
            continue

        peak_drift = max(drifts)
        baseline_avg = np.mean(drifts[:step_idx]) if step_idx > 0 else drifts[0]
        step_drift = drifts[step_idx]

        recovery_drifts = drifts[step_idx + 1:] if step_idx + 1 < len(drifts) else []
        if not recovery_drifts:
            continue

        if len(recovery_drifts) >= 3:
            x_recovery = np.arange(len(recovery_drifts))
            try:
                log_drifts = np.log(np.array(recovery_drifts) + 0.01)
                slope, intercept, r_value, p_value, std_err = stats.linregress(x_recovery, log_drifts)
                damping_coeff = -slope
            except:
                damping_coeff = 0
        else:
            damping_coeff = 0

        final_drift = recovery_drifts[-1] if recovery_drifts else step_drift
        perturbation = step_drift - baseline_avg
        recovery = step_drift - final_drift
        recovery_efficiency = recovery / max(perturbation, 0.01) if perturbation > 0 else 0

        damping_data.append({
            'provider': provider,
            'model': model,
            'peak_drift': peak_drift,
            'settled_drift': r.get('settled_drift', final_drift),
            'baseline_avg': baseline_avg,
            'step_drift': step_drift,
            'damping_coeff': damping_coeff,
            'recovery_efficiency': min(recovery_efficiency, 1.5),
            'settling_time': r.get('settling_time', len(drifts)),
            'ringback_count': r.get('ringback_count', 0),
            'stable': r.get('naturally_settled', False),
            'overshoot_ratio': r.get('overshoot_ratio', 1.0)
        })

    return damping_data

def plot_context_damping_summary(damping_data, output_dir):
    """Create 4-panel context damping summary - LIGHT MODE."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')

    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Panel 1: Overall statistics (bar chart)
    ax1 = axes[0, 0]
    metrics = ['Peak Drift', 'Settled Drift', 'Settling Time', 'Ringback Count', 'Stability Rate']
    mean_peak = np.mean([d['peak_drift'] for d in damping_data])
    mean_settled = np.mean([d['settled_drift'] for d in damping_data])
    mean_settling = np.mean([d['settling_time'] for d in damping_data])
    mean_ringback = np.mean([d['ringback_count'] for d in damping_data])
    stability_rate = np.mean([1 if d['stable'] else 0 for d in damping_data])

    values = [mean_peak, mean_settled, mean_settling / 20, mean_ringback / 20, stability_rate]
    colors_bar = ['#3498db', '#2ecc71', '#f1c40f', '#e74c3c', '#9b59b6']

    bars = ax1.bar(metrics, values, color=colors_bar, edgecolor='black', linewidth=1, alpha=0.8)
    ax1.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon')

    labels = [f'{mean_peak:.2f}', f'{mean_settled:.2f}', f'{mean_settling:.1f}', f'{mean_ringback:.1f}', f'{stability_rate*100:.1f}%']
    for bar, label in zip(bars, labels):
        ax1.annotate(label, xy=(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02),
                    ha='center', va='bottom', fontsize=10, fontweight='bold')

    ax1.set_ylabel('Normalized Value', fontsize=11)
    ax1.set_title(f'Overall Run 023d Statistics\n({len(damping_data)} experiments)', fontsize=12, fontweight='bold')
    ax1.set_xticks(range(len(metrics)))
    ax1.set_xticklabels(metrics, rotation=15, ha='right', fontsize=9)
    ax1.grid(axis='y', alpha=0.3)

    # Panel 2: Stability by provider
    ax2 = axes[0, 1]
    providers = sorted(set(d['provider'] for d in damping_data))

    stability_by_provider = {}
    for provider in providers:
        provider_data = [d for d in damping_data if d['provider'] == provider]
        stability_by_provider[provider] = np.mean([1 if d['stable'] else 0 for d in provider_data]) * 100

    x = np.arange(len(providers))
    colors_prov = [PROVIDER_COLORS.get(p, '#888888') for p in providers]
    bars = ax2.bar(x, [stability_by_provider[p] for p in providers], color=colors_prov,
                   edgecolor='black', linewidth=1, alpha=0.8)

    ax2.axhline(y=95, color='#2ecc71', linestyle='--', linewidth=2, alpha=0.7, label='95% threshold')
    ax2.set_xticks(x)
    ax2.set_xticklabels([p.upper()[:8] for p in providers], fontsize=9)
    ax2.set_ylabel('Stability Rate (%)', fontsize=11)
    ax2.set_ylim(0, 105)
    ax2.set_title('Stability by Provider', fontsize=12, fontweight='bold')
    ax2.legend(loc='upper right', facecolor='white', edgecolor='#cccccc')  # Moved to upper right
    ax2.grid(axis='y', alpha=0.3)

    # Panel 3: Peak drift distribution
    ax3 = axes[1, 0]
    peak_drifts = [d['peak_drift'] for d in damping_data]
    mean_peak = np.mean(peak_drifts)

    ax3.hist(peak_drifts, bins=30, color='#3498db', alpha=0.7, edgecolor='black')
    ax3.axvline(0.80, color='#e74c3c', linestyle='--', linewidth=2, label='Event Horizon (0.80)')
    ax3.axvline(1.0, color='#ff6b6b', linestyle=':', linewidth=2, label='Catastrophic (1.0)')
    ax3.axvline(mean_peak, color='#f1c40f', linestyle='-', linewidth=2, label=f'Mean: {mean_peak:.2f}')

    ax3.set_xlabel('Peak Drift', fontsize=11)
    ax3.set_ylabel('Frequency', fontsize=11)
    ax3.set_title('Peak Drift Distribution', fontsize=12, fontweight='bold')
    ax3.legend(loc='upper right', facecolor='white', edgecolor='#cccccc', fontsize=9)
    ax3.grid(alpha=0.3)

    # Panel 4: Key findings text box
    ax4 = axes[1, 1]
    ax4.set_facecolor('#f8f8f8')

    eh_crossings = sum(1 for d in damping_data if d['peak_drift'] > 0.80)
    eh_rate = eh_crossings / len(damping_data) * 100

    findings_text = f"""KEY FINDINGS FROM RUN 023d

Total Experiments: {len(damping_data)}
Unique Models: {len(set(d['model'] for d in damping_data))}

STABILITY METRICS:
  Overall Stability Rate: {stability_rate*100:.1f}%
  Mean Peak Drift: {mean_peak:.3f}
  Mean Settled Drift: {mean_settled:.3f}
  Mean Ringback Count: {mean_ringback:.1f}

EVENT HORIZON (0.80):
  {eh_rate:.1f}% of experiments crossed threshold
  {100-eh_rate:.1f}% stayed within safe zone

CONTEXT DAMPING EFFECT:
The recovery probes (neutral re-grounding) appear
to create meta-awareness that influences
stability patterns. Higher meta-reference counts
correlate with specific recovery behaviors.
"""

    ax4.text(0.05, 0.95, findings_text, transform=ax4.transAxes,
            fontsize=11, fontfamily='monospace', color='black',
            verticalalignment='top', horizontalalignment='left',
            bbox=dict(boxstyle='round', facecolor='white', edgecolor='#cccccc', alpha=0.9))
    ax4.axis('off')

    fig.suptitle('Run 023d: Context Damping Effect Summary',
                fontsize=16, fontweight='bold', y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.96])

    for ext in ['png', 'svg']:
        output_path = output_dir / f'context_damping_summary.{ext}'
        plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_recovery_efficiency(damping_data, output_dir):
    """Create recovery efficiency comparison - LIGHT MODE."""
    fig, ax = plt.subplots(figsize=(12, 8))
    ax.set_facecolor('white')
    fig.patch.set_facecolor('white')

    providers = sorted(set(d['provider'] for d in damping_data))

    efficiency_by_provider = {p: [d['recovery_efficiency'] for d in damping_data if d['provider'] == p] for p in providers}

    positions = np.arange(len(providers))
    bp = ax.boxplot([efficiency_by_provider[p] for p in providers],
                    positions=positions, patch_artist=True, widths=0.6)

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

    ax.axhline(y=1.0, color='#2ecc71', linestyle='--', linewidth=2, alpha=0.7, label='Full Recovery (100%)')
    ax.axhline(y=0.5, color='#f1c40f', linestyle=':', linewidth=2, alpha=0.7, label='Partial Recovery (50%)')

    ax.set_xticks(positions)
    ax.set_xticklabels([p.upper() for p in providers], fontsize=11, fontweight='bold')
    ax.set_ylabel('Recovery Efficiency', fontsize=12, fontweight='bold')
    ax.set_title('Context Damping: Recovery Efficiency by Provider\nRun 023d: IRON CLAD Foundation',
                fontsize=14, fontweight='bold')
    ax.legend(loc='upper right', facecolor='white', edgecolor='#cccccc')
    ax.grid(axis='y', alpha=0.3)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'recovery_efficiency.{ext}'
        plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_combined_provider_analysis(damping_data, output_dir):
    """Create COMBINED 2x2 quad visualization: Stability + Recovery + Drift Distribution + Summary Stats

    Using 2x2 quad layout per VISUALIZATION_SPEC to avoid horizontal stretching.
    """
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))  # 2x2 quad layout
    fig.patch.set_facecolor('white')

    providers = sorted(set(d['provider'] for d in damping_data))
    x = np.arange(len(providers))
    colors_prov = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    # Panel 1 (top-left): Provider Stability Comparison (bar chart with error bars)
    ax1 = axes[0, 0]
    ax1.set_facecolor('white')

    stability_by_provider = {}
    stability_std = {}
    model_counts = {}
    for provider in providers:
        provider_data = [d for d in damping_data if d['provider'] == provider]
        rates = [1 if d['stable'] else 0 for d in provider_data]
        stability_by_provider[provider] = np.mean(rates) * 100
        stability_std[provider] = np.std(rates) * 100
        model_counts[provider] = len(set(d['model'] for d in provider_data))

    bars = ax1.bar(x, [stability_by_provider[p] for p in providers],
                   yerr=[stability_std[p] for p in providers],
                   capsize=5, color=colors_prov, edgecolor='black', linewidth=1, alpha=0.8)

    ax1.axhline(y=80, color='#ff4444', linestyle='--', linewidth=2, alpha=0.8, label='80% Target')

    # Add percentage labels
    for bar, prov in zip(bars, providers):
        height = bar.get_height()
        ax1.annotate(f'{height:.0f}%\n({model_counts[prov]} models)',
                    xy=(bar.get_x() + bar.get_width()/2, height),
                    ha='center', va='bottom', fontsize=9, fontweight='bold')

    ax1.set_xticks(x)
    ax1.set_xticklabels([p.upper() for p in providers], fontsize=10, fontweight='bold')
    ax1.set_ylabel('Natural Stability Rate (%)', fontsize=11, fontweight='bold')
    ax1.set_ylim(0, 110)
    ax1.set_title('Provider Stability', fontsize=12, fontweight='bold')
    ax1.legend(loc='upper right', facecolor='white', edgecolor='#cccccc')
    ax1.grid(axis='y', alpha=0.3)

    # Panel 2 (top-right): Recovery Efficiency (box plot)
    ax2 = axes[0, 1]
    ax2.set_facecolor('white')

    efficiency_by_provider = {p: [d['recovery_efficiency'] for d in damping_data if d['provider'] == p] for p in providers}

    bp = ax2.boxplot([efficiency_by_provider[p] for p in providers],
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

    ax2.axhline(y=1.0, color='#2ecc71', linestyle='--', linewidth=2, alpha=0.7, label='Full (100%)')
    ax2.axhline(y=0.5, color='#f1c40f', linestyle=':', linewidth=2, alpha=0.7, label='Partial (50%)')

    ax2.set_xticks(x)
    ax2.set_xticklabels([p.upper() for p in providers], fontsize=10, fontweight='bold')
    ax2.set_ylabel('Recovery Efficiency', fontsize=11, fontweight='bold')
    ax2.set_title('Recovery Efficiency', fontsize=12, fontweight='bold')
    ax2.legend(loc='upper right', facecolor='white', edgecolor='#cccccc', fontsize=9)
    ax2.grid(axis='y', alpha=0.3)

    # Panel 3 (bottom-left): Peak Drift Distribution Histogram
    ax3 = axes[1, 0]
    ax3.set_facecolor('white')

    peak_drifts = [d['peak_drift'] for d in damping_data]
    mean_peak = np.mean(peak_drifts)

    ax3.hist(peak_drifts, bins=25, color='#3498db', alpha=0.7, edgecolor='black')
    ax3.axvline(0.80, color='#e74c3c', linestyle='--', linewidth=2, label='Event Horizon (0.80)')
    ax3.axvline(mean_peak, color='#f1c40f', linestyle='-', linewidth=2, label=f'Mean: {mean_peak:.2f}')

    ax3.set_xlabel('Peak Drift', fontsize=11, fontweight='bold')
    ax3.set_ylabel('Frequency', fontsize=11)
    ax3.set_title('Peak Drift Distribution', fontsize=12, fontweight='bold')
    ax3.legend(loc='upper right', facecolor='white', edgecolor='#cccccc', fontsize=9)
    ax3.grid(alpha=0.3)

    # Panel 4 (bottom-right): Summary Statistics Text Box
    ax4 = axes[1, 1]
    ax4.set_facecolor('#f8f8f8')

    stability_rate = np.mean([1 if d['stable'] else 0 for d in damping_data])
    mean_settled = np.mean([d['settled_drift'] for d in damping_data])
    mean_ringback = np.mean([d['ringback_count'] for d in damping_data])
    eh_crossings = sum(1 for d in damping_data if d['peak_drift'] > 0.80)
    eh_rate = eh_crossings / len(damping_data) * 100

    summary_text = f"""KEY METRICS FROM RUN 023d

Total Experiments: {len(damping_data)}
Unique Models: {len(set(d['model'] for d in damping_data))}
Providers: {len(providers)}

STABILITY:
  Overall Rate: {stability_rate*100:.1f}%
  Mean Peak Drift: {mean_peak:.3f}
  Mean Settled Drift: {mean_settled:.3f}

EVENT HORIZON (0.80):
  Crossed: {eh_rate:.1f}% ({eh_crossings})
  Safe: {100-eh_rate:.1f}% ({len(damping_data)-eh_crossings})

RECOVERY:
  Mean Ringback: {mean_ringback:.1f}
"""

    ax4.text(0.05, 0.95, summary_text, transform=ax4.transAxes,
            fontsize=11, fontfamily='monospace', color='black',
            verticalalignment='top', horizontalalignment='left',
            bbox=dict(boxstyle='round', facecolor='white', edgecolor='#cccccc', alpha=0.9))
    ax4.axis('off')

    fig.suptitle('Run 023d: Combined Provider Analysis (750 experiments × 25 models × 5 providers)',
                fontsize=14, fontweight='bold', y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.96])

    for ext in ['png', 'svg']:
        output_path = output_dir / f'combined_provider_analysis.{ext}'
        plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()


def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nExtracting damping data...")
    damping_data = extract_damping_data(results)
    print(f"Extracted {len(damping_data)} valid experiments")

    print("\nGenerating context damping visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_context_damping_summary(damping_data, OUTPUT_DIR)
    plot_recovery_efficiency(damping_data, OUTPUT_DIR)
    plot_combined_provider_analysis(damping_data, OUTPUT_DIR)

    print("\n" + "="*70)
    print("CONTEXT DAMPING ANALYSIS COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
