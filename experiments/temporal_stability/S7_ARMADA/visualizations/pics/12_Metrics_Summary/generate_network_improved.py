#!/usr/bin/env python3
"""
Improved Network Visualization for 12_Metrics_Summary
=====================================================
Creates cleaner, more readable VALIS network graphs with larger nodes,
better labels, and improved layout.

Data sources:
- Run 023d (IRON CLAD Foundation) - 25 models
- Run 023 COMBINED (Full Fleet) - 51 models
"""

import json
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import matplotlib.patheffects as patheffects
from pathlib import Path
from collections import defaultdict

# Paths
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
OUTPUT_DIR = Path(__file__).parent

# Provider colors (including nvidia for full fleet)
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
    'nvidia': '#76B900',
}

# VALIS classifications
VALIS_STYLES = {
    'First-person awareness': {'marker': 'o', 'desc': 'Constitutional AI'},
    'Third-person structural': {'marker': 's', 'desc': 'RLHF'},
    'Educational guidance': {'marker': '^', 'desc': 'Pedagogical'},
    'Real-time grounded': {'marker': 'D', 'desc': 'Grounded'},
    'Open-source collective': {'marker': 'p', 'desc': 'Varied training'},
}

def load_data(combined=False):
    """Load Run 023d or combined results."""
    if combined:
        data_file = RESULTS_DIR / "S7_run_023_COMBINED.json"
    else:
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
    elif provider == 'nvidia':
        return 'Third-person structural'  # Enterprise-focused like OpenAI
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
    ax.set_facecolor('#f5f5f5')
    fig.patch.set_facecolor('white')

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

        # Draw provider hub (larger node for readability)
        hub = ax.scatter([px], [py], s=3500, c=color, marker='h',
                        edgecolors='black', linewidths=2, zorder=10, alpha=0.9)

        # Provider label - ensure contrast with background color
        # Use white text with black outline for readability on all colors
        ax.annotate(provider.upper(), (px, py), fontsize=12, fontweight='bold',
                   color='white', ha='center', va='center', zorder=11,
                   path_effects=[patheffects.withStroke(linewidth=3, foreground='black')])

        # Draw model nodes around hub
        n_models = len(models)

        # Dynamic radius and font size based on number of models
        # More models = larger radius to spread them out, smaller font
        if n_models <= 3:
            model_radius = 1.8
            label_font = 8
            label_offset = 0.4
        elif n_models <= 6:
            model_radius = 2.2
            label_font = 7
            label_offset = 0.35
        else:
            # Many models (like Together with 11) - spread wider, smaller labels
            model_radius = 2.8
            label_font = 6
            label_offset = 0.3

        for j, (model_name, experiments) in enumerate(sorted(models.items())):
            # Position model around provider hub
            model_angle = 2 * np.pi * j / max(n_models, 1) + np.pi/4
            mx = px + model_radius * np.cos(model_angle)
            my = py + model_radius * np.sin(model_angle)

            # Get metrics
            metrics = compute_model_metrics(experiments)

            # Node size based on experiments (smaller for crowded providers)
            base_size = 120 if n_models > 6 else 150
            node_size = base_size + metrics['n_experiments'] * 25

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

            # Model label (shortened) - stagger radially for crowded providers
            short_name = model_name.split('/')[-1][:15]  # Shorter for crowded

            # Stagger label position: alternating inside/outside for crowded providers
            if n_models > 6:
                # Radial label placement - labels point outward from hub
                label_dist = label_offset + (0.15 if j % 2 == 0 else 0)
                lx = mx + label_dist * np.cos(model_angle)
                ly = my + label_dist * np.sin(model_angle)
                # Align based on quadrant
                ha = 'left' if np.cos(model_angle) > 0 else 'right'
                va = 'bottom' if np.sin(model_angle) > 0 else 'top'
            else:
                lx, ly = mx, my + label_offset
                ha, va = 'center', 'bottom'

            ax.annotate(short_name, (lx, ly), fontsize=label_font, color='#333333',
                       ha=ha, va=va, alpha=0.9, zorder=6,
                       fontweight='bold')

    # Title and statistics
    total_models = sum(len(m) for m in provider_models.values())
    ax.set_title(f'VALIS Armada Network\n{total_models} Models × {n_providers} Providers\nRun 023d: IRON CLAD Foundation',
                fontsize=16, fontweight='bold', color='black', pad=20)

    # VALIS style legend
    legend_elements = []
    for style, info in VALIS_STYLES.items():
        count = valis_counts.get(style, 0)
        if count > 0:
            elem = plt.scatter([], [], marker=info['marker'], s=150, c='gray',
                             label=f"{style} ({info['desc']}) - {count} ships")
            legend_elements.append(elem)

    # Provider legend
    for provider in providers:
        color = PROVIDER_COLORS.get(provider, '#888888')
        elem = mpatches.Patch(color=color, label=f'{provider.upper()}')
        legend_elements.append(elem)

    # Move legend to bottom-right to avoid overlapping network nodes
    legend = ax.legend(handles=legend_elements, loc='lower right',
                      bbox_to_anchor=(0.98, 0.02), facecolor='white',
                      edgecolor='#cccccc', fontsize=9)
    for text in legend.get_texts():
        text.set_color('black')

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

def plot_full_fleet_network(provider_models, output_dir):
    """Create full fleet network visualization (51 models) with improved layout."""
    fig, ax = plt.subplots(figsize=(20, 18))
    ax.set_facecolor('#f5f5f5')
    fig.patch.set_facecolor('white')

    # Provider positions (arranged in circle) - larger radius for more models
    n_providers = len(provider_models)
    provider_positions = {}
    radius = 6.0  # Larger radius for full fleet

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

        # Draw provider hub (larger node for readability)
        hub = ax.scatter([px], [py], s=4500, c=color, marker='h',
                        edgecolors='black', linewidths=2, zorder=10, alpha=0.9)

        # Provider label with count
        n_models = len(models)
        ax.annotate(f"{provider.upper()}\n({n_models})", (px, py), fontsize=11, fontweight='bold',
                   color='white', ha='center', va='center', zorder=11,
                   path_effects=[patheffects.withStroke(linewidth=3, foreground='black')])

        # Draw model nodes around hub with adaptive layout
        # Calculate optimal radius based on number of models
        if n_models <= 4:
            model_radius = 2.2
            label_font = 8
            node_size_base = 180
        elif n_models <= 8:
            model_radius = 2.8
            label_font = 7
            node_size_base = 150
        elif n_models <= 15:
            model_radius = 3.5
            label_font = 6
            node_size_base = 120
        else:
            # Very crowded (Together has many models)
            model_radius = 4.2
            label_font = 5
            node_size_base = 100

        for j, (model_name, experiments) in enumerate(sorted(models.items())):
            # Position model around provider hub with slight randomization for crowded areas
            base_angle = 2 * np.pi * j / max(n_models, 1)
            # Add small offset to prevent overlap
            angle_offset = 0.05 * (j % 2 - 0.5)
            model_angle = base_angle + angle_offset

            # Stagger radius for very crowded providers
            if n_models > 10:
                radius_offset = 0.3 * (j % 3 - 1)
            else:
                radius_offset = 0

            mx = px + (model_radius + radius_offset) * np.cos(model_angle)
            my = py + (model_radius + radius_offset) * np.sin(model_angle)

            # Get metrics
            metrics = compute_model_metrics(experiments)

            # Node size based on experiments
            node_size = node_size_base + metrics['n_experiments'] * 15

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
            ax.plot([px, mx], [py, my], '-', color=color, alpha=0.3, linewidth=1, zorder=1)

            # Model label (shortened) - radial placement
            short_name = model_name.split('/')[-1]
            if len(short_name) > 12:
                short_name = short_name[:10] + '..'

            # Radial label placement
            label_dist = 0.35
            lx = mx + label_dist * np.cos(model_angle)
            ly = my + label_dist * np.sin(model_angle)

            # Align based on quadrant
            ha = 'left' if np.cos(model_angle) > 0 else 'right'
            va = 'bottom' if np.sin(model_angle) > 0 else 'top'

            ax.annotate(short_name, (lx, ly), fontsize=label_font, color='#333333',
                       ha=ha, va=va, alpha=0.9, zorder=6,
                       fontweight='bold',
                       path_effects=[patheffects.withStroke(linewidth=2, foreground='white')])

    # Title and statistics
    total_models = sum(len(m) for m in provider_models.values())
    total_experiments = sum(
        sum(len(exps) for exps in models.values())
        for models in provider_models.values()
    )
    ax.set_title(f'VALIS Armada Network - Full Fleet\n{total_models} Models × {n_providers} Providers × {total_experiments} Experiments\nRun 023 Combined: IRON CLAD Foundation',
                fontsize=18, fontweight='bold', color='black', pad=20)

    # VALIS style legend
    legend_elements = []
    for style, info in VALIS_STYLES.items():
        count = valis_counts.get(style, 0)
        if count > 0:
            elem = plt.scatter([], [], marker=info['marker'], s=150, c='gray',
                             label=f"{style} ({info['desc']}) - {count} ships")
            legend_elements.append(elem)

    # Provider legend
    for provider in providers:
        color = PROVIDER_COLORS.get(provider, '#888888')
        n = len(provider_models[provider])
        elem = mpatches.Patch(color=color, label=f'{provider.upper()} ({n} models)')
        legend_elements.append(elem)

    # Move legend to bottom-right
    legend = ax.legend(handles=legend_elements, loc='lower right',
                      bbox_to_anchor=(0.98, 0.02), facecolor='white',
                      edgecolor='#cccccc', fontsize=10)
    for text in legend.get_texts():
        text.set_color('black')

    ax.set_xlim(-12, 12)
    ax.set_ylim(-12, 12)
    ax.set_aspect('equal')
    ax.axis('off')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'armada_network_full_fleet.{ext}'
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
    ax.set_facecolor('white')
    fig.patch.set_facecolor('white')

    x = np.arange(len(providers))
    means = [provider_stability[p]['mean'] for p in providers]
    stds = [provider_stability[p]['std'] for p in providers]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    bars = ax.bar(x, means, yerr=stds, capsize=5, color=colors,
                 edgecolor='black', linewidth=1, alpha=0.8)

    # Event Horizon reference
    ax.axhline(y=0.80, color='#ff4444', linestyle='--', linewidth=2,
              alpha=0.8, label='80% Stability Target')

    # Labels
    ax.set_xticks(x)
    ax.set_xticklabels([p.upper() for p in providers], color='black', fontsize=11, fontweight='bold')
    ax.set_ylabel('Natural Stability Rate', color='black', fontsize=12, fontweight='bold')
    ax.set_ylim(0, 1.1)
    ax.set_title('Provider Stability Comparison\nRun 023d: IRON CLAD Foundation',
                color='black', fontsize=14, fontweight='bold')

    # Add value labels on bars
    for bar, mean, n in zip(bars, means, [provider_stability[p]['n_models'] for p in providers]):
        ax.annotate(f'{mean*100:.0f}%\n({n} models)',
                   xy=(bar.get_x() + bar.get_width()/2, bar.get_height()),
                   ha='center', va='bottom', color='black', fontsize=10, fontweight='bold')

    ax.tick_params(colors='black')
    ax.grid(axis='y', color='#cccccc', alpha=0.5)
    for spine in ax.spines.values():
        spine.set_color('#cccccc')

    legend = ax.legend(loc='upper right', facecolor='white', edgecolor='#cccccc')
    for text in legend.get_texts():
        text.set_color('black')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        output_path = output_dir / f'provider_stability_comparison.{ext}'
        plt.savefig(output_path, dpi=150, facecolor=fig.get_facecolor(),
                   edgecolor='none', bbox_inches='tight')
        print(f"Saved: {output_path}")

    plt.close()

def main():
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Generate Run 023d visualizations (original 25 models)
    print("Loading Run 023d data...")
    results_023d = load_data(combined=False)
    print(f"Loaded {len(results_023d)} results")

    print("\nOrganizing by provider/model...")
    provider_models_023d = organize_data(results_023d)

    for provider, models in provider_models_023d.items():
        print(f"  {provider}: {len(models)} models")

    print("\nGenerating Run 023d visualizations...")
    plot_improved_network(provider_models_023d, OUTPUT_DIR)
    plot_stability_matrix(provider_models_023d, OUTPUT_DIR)

    # Generate Full Fleet visualization (combined 51 models)
    print("\n" + "="*70)
    print("Loading Run 023 COMBINED data (Full Fleet)...")
    results_combined = load_data(combined=True)
    print(f"Loaded {len(results_combined)} results")

    print("\nOrganizing Full Fleet by provider/model...")
    provider_models_full = organize_data(results_combined)

    total_models = sum(len(m) for m in provider_models_full.values())
    for provider, models in provider_models_full.items():
        print(f"  {provider}: {len(models)} models")
    print(f"  TOTAL: {total_models} models")

    print("\nGenerating Full Fleet network visualization...")
    plot_full_fleet_network(provider_models_full, OUTPUT_DIR)

    print("\n" + "="*70)
    print("NETWORK VISUALIZATION COMPLETE")
    print("="*70)

if __name__ == "__main__":
    main()
