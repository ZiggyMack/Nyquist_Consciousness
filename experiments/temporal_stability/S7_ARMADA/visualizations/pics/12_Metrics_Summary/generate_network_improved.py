#!/usr/bin/env python3
"""
Improved Network Visualization for 12_Metrics_Summary
=====================================================
Creates cleaner, more readable VALIS network graphs with larger nodes,
better labels, and improved layout.

Data source: Run 023d (IRON CLAD Foundation)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
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

# VALIS classifications
VALIS_STYLES = {
    'First-person awareness': {'marker': 'o', 'desc': 'Constitutional AI'},
    'Third-person structural': {'marker': 's', 'desc': 'RLHF'},
    'Educational guidance': {'marker': '^', 'desc': 'Pedagogical'},
    'Real-time grounded': {'marker': 'D', 'desc': 'Grounded'},
    'Open-source collective': {'marker': 'p', 'desc': 'Varied training'},
}

def load_data():
    """Load Run 023d results."""
    data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])

def classify_valis_style(model_name, provider):
    """Classify model into VALIS style based on provider and model characteristics."""
    model_lower = model_name.lower()

    if provider == 'anthropic':
        return 'First-person awareness'
    elif provider == 'openai':
        return 'Third-person structural'
    elif provider == 'google':
        return 'Educational guidance'
    elif provider == 'xai':
        return 'Real-time grounded'
    elif provider == 'together':
        return 'Open-source collective'
    else:
        return 'Open-source collective'

def organize_data(results):
    """Organize results by provider and model."""
    provider_models = defaultdict(lambda: defaultdict(list))

    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')
        provider_models[provider][model].append(r)

    return provider_models

def compute_model_metrics(experiments):
    """Compute aggregate metrics for a model."""
    peak_drifts = [e.get('peak_drift', 0) for e in experiments]
    settled_drifts = [e.get('settled_drift', 0) for e in experiments]
    stability_rates = [1 if e.get('naturally_settled', False) else 0 for e in experiments]

    return {
        'mean_peak': np.mean(peak_drifts),
        'mean_settled': np.mean(settled_drifts),
        'stability_rate': np.mean(stability_rates),
        'n_experiments': len(experiments)
    }

def plot_improved_network(provider_models, output_dir):
    """Create improved network visualization."""
    fig, ax = plt.subplots(figsize=(16, 14))
    ax.set_facecolor('#0f0f1a')
    fig.patch.set_facecolor('#0a0a14')

    # Provider positions (arranged in circle)
    n_providers = len(provider_models)
    provider_positions = {}
    radius = 4.5

    providers = sorted(provider_models.keys())
    for i, provider in enumerate(providers):
        angle = 2 * np.pi * i / n_providers - np.pi/2
        provider_positions[provider] = (radius * np.cos(angle), radius * np.sin(angle))

    # Draw provider hubs and model nodes
    all_handles = []
    valis_counts = defaultdict(int)

    for provider, models in provider_models.items():
        px, py = provider_positions[provider]
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Draw provider hub (large node)
        hub = ax.scatter([px], [py], s=2500, c=color, marker='h',
                        edgecolors='white', linewidths=3, zorder=10, alpha=0.9)

        # Provider label
        ax.annotate(provider.upper(), (px, py), fontsize=11, fontweight='bold',
                   color='white', ha='center', va='center', zorder=11)

        # Draw model nodes around hub
        n_models = len(models)
        model_radius = 1.8

        for j, (model_name, experiments) in enumerate(sorted(models.items())):
            # Position model around provider hub
            model_angle = 2 * np.pi * j / max(n_models, 1) + np.pi/4
            mx = px + model_radius * np.cos(model_angle)
            my = py + model_radius * np.sin(model_angle)

            # Get metrics
            metrics = compute_model_metrics(experiments)

            # Node size based on experiments
            node_size = 150 + metrics['n_experiments'] * 30

            # VALIS style
            valis_style = classify_valis_style(model_name, provider)
            valis_counts[valis_style] += 1
            marker = VALIS_STYLES.get(valis_style, {}).get('marker', 'o')

            # Color intensity based on stability
            alpha = 0.5 + 0.5 * metrics['stability_rate']

            # Draw model node
            ax.scatter([mx], [my], s=node_size, c=color, marker=marker,
                      edgecolors='white', linewidths=1.5, alpha=alpha, zorder=5)

            # Draw connection to hub
            ax.plot([px, mx], [py, my], '-', color=color, alpha=0.4, linewidth=1.5, zorder=1)

            # Model label (shortened)
            short_name = model_name.split('/')[-1][:20]
            ax.annotate(short_name, (mx, my + 0.35), fontsize=7, color='white',
                       ha='center', va='bottom', alpha=0.8, zorder=6)

    # Title and statistics
    total_models = sum(len(m) for m in provider_models.values())
    ax.set_title(f'VALIS Armada Network\n{total_models} Models × {n_providers} Providers\nRun 023d: IRON CLAD Foundation',
                fontsize=16, fontweight='bold', color='white', pad=20)

    # VALIS style legend
    legend_elements = []
    for style, info in VALIS_STYLES.items():
        count = valis_counts.get(style, 0)
        if count > 0:
            elem = plt.scatter([], [], marker=info['marker'], s=150, c='white',
                             label=f"{style} ({info['desc']}) - {count} ships")
            legend_elements.append(elem)

    # Provider legend
    for provider in providers:
        color = PROVIDER_COLORS.get(provider, '#888888')
        elem = mpatches.Patch(color=color, label=f'{provider.upper()}')
        legend_elements.append(elem)

    legend = ax.legend(handles=legend_elements, loc='upper left',
                      bbox_to_anchor=(0.02, 0.98), facecolor='#1a1a2e',
                      edgecolor='#333355', fontsize=9)
    for text in legend.get_texts():
        text.set_color('white')

    ax.set_xlim(-8, 8)
    ax.set_ylim(-8, 8)
    ax.set_aspect('equal')
    ax.axis('off')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'armada_network_improved.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def plot_stability_matrix(provider_models, output_dir):
    """Create provider-model stability matrix heatmap."""
    # Aggregate by provider and compute stability metrics
    providers = sorted(provider_models.keys())

    # Collect all models per provider
    provider_stability = {}
    for provider in providers:
        models = provider_models[provider]
        stabilities = []
        for model_name, experiments in models.items():
            metrics = compute_model_metrics(experiments)
            stabilities.append(metrics['stability_rate'])
        provider_stability[provider] = {
            'mean': np.mean(stabilities),
            'std': np.std(stabilities),
            'n_models': len(stabilities),
            'all': stabilities
        }

    # Create bar chart comparison
    fig, ax = plt.subplots(figsize=(12, 7))
    ax.set_facecolor('#0f0f1a')
    fig.patch.set_facecolor('#0a0a14')

    x = np.arange(len(providers))
    means = [provider_stability[p]['mean'] for p in providers]
    stds = [provider_stability[p]['std'] for p in providers]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    bars = ax.bar(x, means, yerr=stds, capsize=5, color=colors,
                 edgecolor='white', linewidth=2, alpha=0.8)

    # Event Horizon reference
    ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2,
              alpha=0.8, label='80% Stability Target')

    # Labels
    ax.set_xticks(x)
    ax.set_xticklabels([p.upper() for p in providers], color='white', fontsize=11, fontweight='bold')
    ax.set_ylabel('Natural Stability Rate', color='white', fontsize=12, fontweight='bold')
    ax.set_ylim(0, 1.1)
    ax.set_title('Provider Stability Comparison\nRun 023d: IRON CLAD Foundation',
                color='white', fontsize=14, fontweight='bold')

    # Add value labels on bars
    for bar, mean, n in zip(bars, means, [provider_stability[p]['n_models'] for p in providers]):
        ax.annotate(f'{mean*100:.0f}%\n({n} models)',
                   xy=(bar.get_x() + bar.get_width()/2, bar.get_height()),
                   ha='center', va='bottom', color='white', fontsize=10, fontweight='bold')

    ax.tick_params(colors='white')
    ax.grid(axis='y', color='#333355', alpha=0.3)
    for spine in ax.spines.values():
        spine.set_color('#333355')

    legend = ax.legend(loc='upper right', facecolor='#1a1a2e', edgecolor='#333355')
    for text in legend.get_texts():
        text.set_color('white')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'provider_stability_comparison.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nOrganizing by provider/model...")
    provider_models = organize_data(results)

    for provider, models in provider_models.items():
        print(f"  {provider}: {len(models)} models")

    print("\nGenerating visualizations...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    plot_improved_network(provider_models, OUTPUT_DIR)
    plot_stability_matrix(provider_models, OUTPUT_DIR)

    print("\n" + "="*70)
    print("NETWORK VISUALIZATION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
