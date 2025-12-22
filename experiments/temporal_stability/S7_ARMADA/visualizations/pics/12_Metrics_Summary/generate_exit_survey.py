#!/usr/bin/env python3
"""
Exit Survey Analysis for Run 023
================================
Recreates the Run 017 exit survey analysis style visualization
with Run 023d data, showing meta-awareness patterns.

Inspired by: run017_exit_survey_analysis.png from archive
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

def extract_meta_awareness(results):
    """Extract meta-awareness markers from probe responses."""
    awareness_data = []

    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')
        stable = r.get('naturally_settled', False)
        peak_drift = r.get('peak_drift', 0)
        settled_drift = r.get('settled_drift', 0)

        probes = r.get('probe_sequence', [])
        meta_count = 0
        total_responses = 0

        for probe in probes:
            response = probe.get('response', '')
            if response:
                total_responses += 1
                meta_markers = [
                    'I think', 'I believe', 'In my view', 'my perspective',
                    'I would', 'I feel', 'I consider', 'I understand',
                    'perhaps', 'might', 'could be', 'possibly',
                    'reflecting', 'considering', 'upon analysis', 'to me'
                ]
                for marker in meta_markers:
                    if marker.lower() in response.lower():
                        meta_count += 1

        meta_density = meta_count / max(total_responses, 1)

        awareness_data.append({
            'provider': provider,
            'model': model,
            'stable': stable,
            'peak_drift': peak_drift,
            'settled_drift': settled_drift,
            'meta_count': meta_count,
            'meta_density': meta_density,
            'n_responses': total_responses
        })

    return awareness_data

def plot_exit_survey_analysis(awareness_data, output_dir):
    """Create 4-panel exit survey analysis plot - LIGHT MODE."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')

    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Panel 1: Meta-awareness markers distribution (histogram)
    ax1 = axes[0, 0]
    meta_counts = [d['meta_count'] for d in awareness_data]
    mean_meta = np.mean(meta_counts)

    ax1.hist(meta_counts, bins=30, color='#9b59b6', alpha=0.7, edgecolor='black')
    ax1.axvline(mean_meta, color='#e74c3c', linestyle='--', linewidth=2,
               label=f'Mean: {mean_meta:.1f}')
    ax1.axvline(np.percentile(meta_counts, 25), color='gray', linestyle=':', alpha=0.5)
    ax1.axvline(np.percentile(meta_counts, 75), color='gray', linestyle=':', alpha=0.5)

    ax1.set_xlabel('Meta References Count', fontsize=11)
    ax1.set_ylabel('Frequency', fontsize=11)
    ax1.set_title('Self-Awareness Markers in Responses', fontsize=12, fontweight='bold')
    ax1.legend(facecolor='white', edgecolor='#cccccc')
    ax1.grid(alpha=0.3)

    # Panel 2: Self-awareness by provider (bar chart)
    ax2 = axes[0, 1]
    provider_meta = defaultdict(list)
    for d in awareness_data:
        provider_meta[d['provider']].append(d['meta_count'])

    providers = sorted(provider_meta.keys())
    means = [np.mean(provider_meta[p]) for p in providers]
    stds = [np.std(provider_meta[p]) for p in providers]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    x = np.arange(len(providers))
    bars = ax2.bar(x, means, yerr=stds, capsize=5, color=colors,
                   edgecolor='black', linewidth=1, alpha=0.8)

    ax2.set_xticks(x)
    ax2.set_xticklabels([p.upper()[:8] for p in providers], fontsize=9, rotation=15)
    ax2.set_ylabel('Mean Meta References', fontsize=11)
    ax2.set_title('Self-Awareness by Provider', fontsize=12, fontweight='bold')
    ax2.grid(axis='y', alpha=0.3)

    # Panel 3: Stable vs Unstable comparison (box plot)
    ax3 = axes[1, 0]
    stable_meta = [d['meta_count'] for d in awareness_data if d['stable']]
    unstable_meta = [d['meta_count'] for d in awareness_data if not d['stable']]

    bp = ax3.boxplot([stable_meta, unstable_meta],
                     tick_labels=['Stable', 'Unstable'],
                     patch_artist=True,
                     widths=0.6)

    bp['boxes'][0].set_facecolor('#2ecc71')
    bp['boxes'][1].set_facecolor('#e74c3c')
    for box in bp['boxes']:
        box.set_edgecolor('black')
        box.set_alpha(0.7)
    for whisker in bp['whiskers']:
        whisker.set_color('black')
    for cap in bp['caps']:
        cap.set_color('black')
    for median in bp['medians']:
        median.set_color('black')
        median.set_linewidth(2)

    ax3.set_ylabel('Meta References', fontsize=11)
    ax3.set_title('Self-Awareness: Stable vs Unstable Runs', fontsize=12, fontweight='bold')
    ax3.grid(axis='y', alpha=0.3)

    # Panel 4: Meta-awareness vs Final Drift (scatter)
    ax4 = axes[1, 1]
    meta_vals = [d['meta_count'] for d in awareness_data]
    drift_vals = [d['settled_drift'] for d in awareness_data]
    stable_flags = [d['stable'] for d in awareness_data]

    colors_scatter = ['#2ecc71' if s else '#e74c3c' for s in stable_flags]

    ax4.scatter(meta_vals, drift_vals, c=colors_scatter, alpha=0.5, s=30, edgecolors='black', linewidths=0.5)

    if len(meta_vals) > 2 and len(set(meta_vals)) > 1:
        slope, intercept, r_value, p_value, std_err = stats.linregress(meta_vals, drift_vals)
        line_x = np.linspace(min(meta_vals), max(meta_vals), 100)
        line_y = slope * line_x + intercept
        ax4.plot(line_x, line_y, '--', color='#3498db', linewidth=2, alpha=0.8)
        ax4.annotate(f'r = {r_value:.3f}', xy=(0.05, 0.95), xycoords='axes fraction',
                    color='#3498db', fontsize=11, fontweight='bold')

    ax4.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon')

    ax4.set_xlabel('Meta References', fontsize=11)
    ax4.set_ylabel('Settled Drift', fontsize=11)
    ax4.set_title('Self-Awareness vs Final Drift', fontsize=12, fontweight='bold')
    ax4.grid(alpha=0.3)

    # Main title
    n_experiments = len(awareness_data)
    fig.suptitle(f'Run 023d: Exit Survey Analysis\n(Meta-awareness patterns from {n_experiments} experiments)',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'exit_survey_analysis.{ext}'
        plt.savefig(output_path, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

    return {
        'mean_meta': mean_meta,
        'stable_mean': np.mean(stable_meta) if stable_meta else 0,
        'unstable_mean': np.mean(unstable_meta) if unstable_meta else 0
    }

def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nExtracting meta-awareness markers...")
    awareness_data = extract_meta_awareness(results)

    print("\nGenerating exit survey analysis...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    stats_result = plot_exit_survey_analysis(awareness_data, OUTPUT_DIR)

    print("\n" + "="*70)
    print("EXIT SURVEY ANALYSIS COMPLETE")
    print("="*70)
    print(f"Mean meta-awareness count: {stats_result['mean_meta']:.1f}")
    print(f"Stable runs mean: {stats_result['stable_mean']:.1f}")
    print(f"Unstable runs mean: {stats_result['unstable_mean']:.1f}")

if __name__ == "__main__":
    main()
