"""
IRON CLAD Run 023b Visualization
================================
Generates visualizations for the cosine-distance IRON CLAD foundation data.

USAGE:
    python visualize_023b.py              # Generate all visualizations
    python visualize_023b.py --type hist  # Just histogram
    python visualize_023b.py --type box   # Just boxplots

OUTPUT:
    results/pics/
      - run023b_drift_distribution.png
      - run023b_by_experiment.png
      - run023b_by_provider.png
      - run023b_by_model.png
"""

import json
import argparse
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
OUTPUT_DIR = RESULTS_DIR / "pics"
DATA_FILE = RESULTS_DIR / "S7_run_023b_CURRENT.json"

# Cosine Event Horizon (calibrated 2025-12-20)
EVENT_HORIZON = 0.80
THRESHOLD_WARNING = 0.60

# Provider colors
PROVIDER_COLORS = {
    "anthropic": "#7c3aed",  # Purple
    "openai": "#10a37f",     # Green
    "google": "#4285f4",     # Blue
    "xai": "#1a1a1a",        # Black
    "together": "#ff6b35",   # Orange
}

def load_data():
    """Load run023b results."""
    with open(DATA_FILE, 'r', encoding='utf-8') as f:
        return json.load(f)

def generate_drift_distribution(results, output_dir):
    """Generate overall drift distribution histogram."""
    peak_drifts = [r['peak_drift'] for r in results if r.get('peak_drift')]

    fig, ax = plt.subplots(figsize=(12, 6))

    # Histogram
    bins = np.linspace(0, 1.0, 41)  # 0.025 bin width
    n, bins_out, patches = ax.hist(peak_drifts, bins=bins, edgecolor='white', alpha=0.7)

    # Color by zone
    for i, patch in enumerate(patches):
        bin_center = (bins_out[i] + bins_out[i+1]) / 2
        if bin_center >= EVENT_HORIZON:
            patch.set_facecolor('#ef4444')  # Red - VOLATILE
        elif bin_center >= THRESHOLD_WARNING:
            patch.set_facecolor('#f59e0b')  # Orange - WARNING
        else:
            patch.set_facecolor('#22c55e')  # Green - STABLE

    # Threshold lines
    ax.axvline(EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax.axvline(THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=2,
               label=f'Warning ({THRESHOLD_WARNING})')

    # Stats annotations
    mean = np.mean(peak_drifts)
    median = np.median(peak_drifts)
    p95 = np.percentile(peak_drifts, 95)

    ax.axvline(mean, color='blue', linestyle='-', linewidth=1.5, alpha=0.7,
               label=f'Mean ({mean:.3f})')
    ax.axvline(median, color='purple', linestyle='-', linewidth=1.5, alpha=0.7,
               label=f'Median ({median:.3f})')

    ax.set_xlabel('Peak Cosine Drift', fontsize=12)
    ax.set_ylabel('Count', fontsize=12)
    ax.set_title('Run 023b: Cosine Drift Distribution (N=4505)\n'
                 f'Mean={mean:.3f}, Median={median:.3f}, P95={p95:.3f}',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    output_path = output_dir / 'run023b_drift_distribution.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")

def generate_by_experiment(results, output_dir):
    """Generate boxplot by experiment type."""
    by_exp = defaultdict(list)
    for r in results:
        if r.get('peak_drift'):
            by_exp[r['experiment']].append(r['peak_drift'])

    exp_order = ['stability', 'boundary', 'event_horizon', 'recursive', 'rescue', 'settling']
    exp_data = [by_exp[e] for e in exp_order if e in by_exp]
    exp_labels = [e for e in exp_order if e in by_exp]

    fig, ax = plt.subplots(figsize=(12, 6))

    bp = ax.boxplot(exp_data, labels=exp_labels, patch_artist=True)

    # Color boxes
    colors = ['#22c55e', '#3b82f6', '#8b5cf6', '#ec4899', '#f59e0b', '#ef4444']
    for patch, color in zip(bp['boxes'], colors):
        patch.set_facecolor(color)
        patch.set_alpha(0.6)

    # Threshold lines
    ax.axhline(EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax.axhline(THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5,
               label=f'Warning ({THRESHOLD_WARNING})')

    ax.set_xlabel('Experiment Type', fontsize=12)
    ax.set_ylabel('Peak Cosine Drift', fontsize=12)
    ax.set_title('Run 023b: Drift by Experiment Type\n(6 experiments x 25 ships x 30 iterations)',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    output_path = output_dir / 'run023b_by_experiment.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")

def generate_by_provider(results, output_dir):
    """Generate boxplot by provider."""
    by_provider = defaultdict(list)
    for r in results:
        if r.get('peak_drift'):
            by_provider[r['provider']].append(r['peak_drift'])

    provider_order = ['anthropic', 'openai', 'google', 'xai', 'together']
    provider_data = [by_provider[p] for p in provider_order if p in by_provider]
    provider_labels = [p.upper() for p in provider_order if p in by_provider]
    provider_counts = [len(by_provider[p]) for p in provider_order if p in by_provider]

    fig, ax = plt.subplots(figsize=(12, 6))

    bp = ax.boxplot(provider_data, labels=[f'{l}\n(n={c})' for l, c in zip(provider_labels, provider_counts)],
                     patch_artist=True)

    # Color by provider
    for patch, provider in zip(bp['boxes'], [p for p in provider_order if p in by_provider]):
        patch.set_facecolor(PROVIDER_COLORS.get(provider, '#gray'))
        patch.set_alpha(0.6)

    # Threshold lines
    ax.axhline(EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax.axhline(THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5,
               label=f'Warning ({THRESHOLD_WARNING})')

    ax.set_xlabel('Provider', fontsize=12)
    ax.set_ylabel('Peak Cosine Drift', fontsize=12)
    ax.set_title('Run 023b: Drift by Provider\n(5 providers, 25 ships total)',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    output_path = output_dir / 'run023b_by_provider.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")

def generate_volatility_counts(results, output_dir):
    """Generate bar chart of STABLE vs VOLATILE by provider."""
    by_provider = defaultdict(lambda: {'stable': 0, 'volatile': 0})

    for r in results:
        if r.get('peak_drift'):
            provider = r['provider']
            if r['peak_drift'] >= EVENT_HORIZON:
                by_provider[provider]['volatile'] += 1
            else:
                by_provider[provider]['stable'] += 1

    provider_order = ['anthropic', 'openai', 'google', 'xai', 'together']
    providers = [p for p in provider_order if p in by_provider]
    stable_counts = [by_provider[p]['stable'] for p in providers]
    volatile_counts = [by_provider[p]['volatile'] for p in providers]

    fig, ax = plt.subplots(figsize=(12, 6))

    x = np.arange(len(providers))
    width = 0.35

    bars1 = ax.bar(x - width/2, stable_counts, width, label='STABLE', color='#22c55e', alpha=0.8)
    bars2 = ax.bar(x + width/2, volatile_counts, width, label='VOLATILE', color='#ef4444', alpha=0.8)

    ax.set_xlabel('Provider', fontsize=12)
    ax.set_ylabel('Count', fontsize=12)
    ax.set_title(f'Run 023b: Stability Classification by Provider\n(Event Horizon = {EVENT_HORIZON})',
                 fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([p.upper() for p in providers])
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')

    # Add count labels on bars
    for bar in bars1:
        height = bar.get_height()
        ax.annotate(f'{int(height)}',
                    xy=(bar.get_x() + bar.get_width() / 2, height),
                    xytext=(0, 3), textcoords="offset points",
                    ha='center', va='bottom', fontsize=9)
    for bar in bars2:
        height = bar.get_height()
        if height > 0:
            ax.annotate(f'{int(height)}',
                        xy=(bar.get_x() + bar.get_width() / 2, height),
                        xytext=(0, 3), textcoords="offset points",
                        ha='center', va='bottom', fontsize=9)

    plt.tight_layout()
    output_path = output_dir / 'run023b_volatility_counts.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")

def main():
    parser = argparse.ArgumentParser(description='Visualize Run 023b IRON CLAD data')
    parser.add_argument('--type', choices=['hist', 'exp', 'provider', 'volatility', 'all'],
                        default='all', help='Visualization type')
    args = parser.parse_args()

    # Create output directory
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Load data
    print(f"Loading: {DATA_FILE.name}")
    data = load_data()
    results = data['results']
    print(f"  Results: {len(results)}")

    print(f"\nGenerating visualizations (Event Horizon = {EVENT_HORIZON})...")

    if args.type in ['hist', 'all']:
        generate_drift_distribution(results, OUTPUT_DIR)

    if args.type in ['exp', 'all']:
        generate_by_experiment(results, OUTPUT_DIR)

    if args.type in ['provider', 'all']:
        generate_by_provider(results, OUTPUT_DIR)

    if args.type in ['volatility', 'all']:
        generate_volatility_counts(results, OUTPUT_DIR)

    print(f"\nOutput: {OUTPUT_DIR}")

if __name__ == "__main__":
    main()
