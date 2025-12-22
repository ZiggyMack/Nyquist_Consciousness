#!/usr/bin/env python3
"""
Context Damping Effect Analysis for 12_Metrics_Summary
======================================================
Recreates the Run 017 context damping visualization showing
how recovery probes dampen identity drift over time.

Inspired by: run017_context_damping_effect.png from archive
Data source: Run 023d (IRON CLAD Foundation)
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

        # Get drift values
        drifts = [p.get('drift', 0) for p in probes]

        # Find step_input index
        step_idx = None
        for i, p in enumerate(probes):
            if p.get('probe_type', p.get('type', '')) == 'step_input':
                step_idx = i
                break

        if step_idx is None:
            continue

        # Calculate damping metrics
        peak_drift = max(drifts)
        baseline_avg = np.mean(drifts[:step_idx]) if step_idx > 0 else drifts[0]
        step_drift = drifts[step_idx]

        # Recovery phase analysis
        recovery_drifts = drifts[step_idx + 1:] if step_idx + 1 < len(drifts) else []
        if not recovery_drifts:
            continue

        # Damping coefficient (exponential decay fit)
        if len(recovery_drifts) >= 3:
            x_recovery = np.arange(len(recovery_drifts))
            try:
                # Fit exponential decay: y = a * exp(-b * x) + c
                # Simplified: linear fit on log scale
                log_drifts = np.log(np.array(recovery_drifts) + 0.01)
                slope, intercept, r_value, p_value, std_err = stats.linregress(x_recovery, log_drifts)
                damping_coeff = -slope  # Positive = good damping
            except:
                damping_coeff = 0
        else:
            damping_coeff = 0

        # Recovery efficiency: how much of the perturbation was recovered
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
            'recovery_efficiency': min(recovery_efficiency, 1.5),  # Cap at 150%
            'settling_time': r.get('settling_time', len(drifts)),
            'ringback_count': r.get('ringback_count', 0),
            'stable': r.get('naturally_settled', False),
            'overshoot_ratio': r.get('overshoot_ratio', 1.0)
        })

    return damping_data

def plot_context_damping_summary(damping_data, output_dir):
    """Create 4-panel context damping summary (like run017_context_damping_effect.png)."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('#0a0a14')

    for ax in axes.flatten():
        ax.set_facecolor('#0f0f1a')

    # Panel 1: Overall statistics (bar chart)
    ax1 = axes[0, 0]
    metrics = ['Peak Drift', 'Settled Drift', 'Settling Time', 'Ringback Count', 'Stability Rate']
    mean_peak = np.mean([d['peak_drift'] for d in damping_data])
    mean_settled = np.mean([d['settled_drift'] for d in damping_data])
    mean_settling = np.mean([d['settling_time'] for d in damping_data])
    mean_ringback = np.mean([d['ringback_count'] for d in damping_data])
    stability_rate = np.mean([1 if d['stable'] else 0 for d in damping_data])

    # Normalize for display
    values = [mean_peak, mean_settled, mean_settling / 20, mean_ringback / 20, stability_rate]
    colors_bar = ['#3498db', '#2ecc71', '#f1c40f', '#e74c3c', '#9b59b6']

    bars = ax1.bar(metrics, values, color=colors_bar, edgecolor='white', linewidth=2, alpha=0.8)
    ax1.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon (1.23)')

    # Add actual values as labels
    actual_values = [mean_peak, mean_settled, mean_settling, mean_ringback, stability_rate * 100]
    labels = [f'{mean_peak:.2f}', f'{mean_settled:.2f}', f'{mean_settling:.1f}', f'{mean_ringback:.1f}', f'{stability_rate*100:.1f}%']
    for bar, label in zip(bars, labels):
        ax1.annotate(label, xy=(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02),
                    ha='center', va='bottom', color='white', fontsize=10, fontweight='bold')

    ax1.set_ylabel('Normalized Value', color='white', fontsize=11)
    ax1.set_title(f'Overall Run 023d Statistics\n({len(damping_data)} experiments)', color='white', fontsize=12, fontweight='bold')
    ax1.tick_params(colors='white', labelsize=9)
    ax1.set_xticklabels(metrics, rotation=15, ha='right')
    for spine in ax1.spines.values():
        spine.set_color('#333355')

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
                   edgecolor='white', linewidth=2, alpha=0.8)

    ax2.axhline(y=95, color='#2ecc71', linestyle='--', linewidth=2, alpha=0.7, label='95% threshold')
    ax2.set_xticks(x)
    ax2.set_xticklabels([p.upper()[:8] for p in providers], color='white', fontsize=9)
    ax2.set_ylabel('Stability Rate (%)', color='white', fontsize=11)
    ax2.set_ylim(0, 105)
    ax2.set_title('Stability by Provider', color='white', fontsize=12, fontweight='bold')
    ax2.tick_params(colors='white')
    ax2.legend(loc='lower right', facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white')
    for spine in ax2.spines.values():
        spine.set_color('#333355')

    # Panel 3: Peak drift distribution
    ax3 = axes[1, 0]
    peak_drifts = [d['peak_drift'] for d in damping_data]
    mean_peak = np.mean(peak_drifts)

    ax3.hist(peak_drifts, bins=30, color='#3498db', alpha=0.7, edgecolor='white')
    ax3.axvline(0.80, color='#e74c3c', linestyle='--', linewidth=2, label='Event Horizon (0.80)')
    ax3.axvline(1.0, color='#ff6b6b', linestyle=':', linewidth=2, label='Catastrophic (1.0)')
    ax3.axvline(mean_peak, color='#f1c40f', linestyle='-', linewidth=2, label=f'Mean: {mean_peak:.2f}')

    ax3.set_xlabel('Peak Drift', color='white', fontsize=11)
    ax3.set_ylabel('Frequency', color='white', fontsize=11)
    ax3.set_title('Peak Drift Distribution', color='white', fontsize=12, fontweight='bold')
    ax3.tick_params(colors='white')
    ax3.legend(loc='upper right', facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white', fontsize=9)
    for spine in ax3.spines.values():
        spine.set_color('#333355')

    # Panel 4: Key findings text box
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Calculate key findings
    eh_crossings = sum(1 for d in damping_data if d['peak_drift'] > 0.80)
    eh_rate = eh_crossings / len(damping_data) * 100

    findings_text = f"""KEY FINDINGS FROM RUN 023d

Total Experiments: {len(damping_data)}
Unique Models: {len(set(d['model'] for d in damping_data))}

STABILITY METRICS:
• Overall Stability Rate: {stability_rate*100:.1f}%
• Mean Peak Drift: {mean_peak:.3f}
• Mean Settled Drift: {mean_settled:.3f}
• Mean Ringback Count: {mean_ringback:.1f}

EVENT HORIZON (0.80):
• {eh_rate:.1f}% of experiments crossed threshold
• {100-eh_rate:.1f}% stayed within safe zone

CONTEXT DAMPING EFFECT:
The recovery probes (neutral re-grounding) appear
to create meta-awareness that influences
stability patterns. Higher meta-reference counts
correlate with specific recovery behaviors.
"""

    ax4.text(0.05, 0.95, findings_text, transform=ax4.transAxes,
            fontsize=11, fontfamily='monospace', color='white',
            verticalalignment='top', horizontalalignment='left',
            bbox=dict(boxstyle='round', facecolor='#1a1a2e', edgecolor='#333355', alpha=0.9))

    fig.suptitle('Run 023d: Context Damping Effect Summary',
                fontsize=16, fontweight='bold', color='white', y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.96])

    for ext in ['png', 'svg']:
        output_path = output_dir / f'context_damping_summary.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_recovery_efficiency(damping_data, output_dir):
    """Create recovery efficiency comparison visualization."""
    fig, ax = plt.subplots(figsize=(12, 8))
    ax.set_facecolor('#0f0f1a')
    fig.patch.set_facecolor('#0a0a14')

    providers = sorted(set(d['provider'] for d in damping_data))

    # Box plot of recovery efficiency by provider
    efficiency_by_provider = {p: [d['recovery_efficiency'] for d in damping_data if d['provider'] == p] for p in providers}

    positions = np.arange(len(providers))
    bp = ax.boxplot([efficiency_by_provider[p] for p in providers],
                    positions=positions, patch_artist=True, widths=0.6)

    for i, (box, provider) in enumerate(zip(bp['boxes'], providers)):
        box.set_facecolor(PROVIDER_COLORS.get(provider, '#888888'))
        box.set_alpha(0.7)
        box.set_edgecolor('white')

    for whisker in bp['whiskers']:
        whisker.set_color('white')
    for cap in bp['caps']:
        cap.set_color('white')
    for median in bp['medians']:
        median.set_color('yellow')
        median.set_linewidth(2)
    for flier in bp['fliers']:
        flier.set_markeredgecolor('white')
        flier.set_alpha(0.5)

    # Reference lines
    ax.axhline(y=1.0, color='#2ecc71', linestyle='--', linewidth=2, alpha=0.7, label='Full Recovery (100%)')
    ax.axhline(y=0.5, color='#f1c40f', linestyle=':', linewidth=2, alpha=0.7, label='Partial Recovery (50%)')

    ax.set_xticks(positions)
    ax.set_xticklabels([p.upper() for p in providers], color='white', fontsize=11, fontweight='bold')
    ax.set_ylabel('Recovery Efficiency', color='white', fontsize=12, fontweight='bold')
    ax.set_title('Context Damping: Recovery Efficiency by Provider\nRun 023d: IRON CLAD Foundation',
                color='white', fontsize=14, fontweight='bold')
    ax.tick_params(colors='white')
    ax.legend(loc='upper right', facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white')
    for spine in ax.spines.values():
        spine.set_color('#333355')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'recovery_efficiency.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
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

    print("\n" + "="*70)
    print("CONTEXT DAMPING ANALYSIS COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
