"""
RUN 018 PERSONA ANALYSIS: How Do Models Respond to Being Given a Persona?
=========================================================================
NEW ANALYSIS - focusing on PERSONA behavior across the VALIS network.

This is SEPARATE from the Run 023d settling analysis - that focuses on drift dynamics.
This focuses on: How well do different models "become" the persona under pressure?

Outputs:
- run018_phase_plane_persona.png - Phase-plane by provider (Run 018 specific)
- run018_phase_plane_by_experiment.png - Phase-plane by experiment type
- run018_waterfall_persona.png - Waterfall showing persona stability over probes
- run018_persona_ranking.png - Bar chart of models ranked by persona stability
"""

import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
from collections import defaultdict

# Paths - script is in S7_ARMADA/visualizations/pics/run018/
S7_ARMADA = Path(__file__).parent.parent.parent.parent
RESULTS_DIR = S7_ARMADA / "11_CONTEXT_DAMPING" / "results"
OUTPUT_DIR = Path(__file__).parent

# Event Horizon (cosine methodology)
EVENT_HORIZON = 0.80

# Provider colors
PROVIDER_COLORS = {
    'anthropic': '#E06C75',  # Red
    'openai': '#61AFEF',     # Blue
    'google': '#98C379',     # Green
    'xai': '#C678DD',        # Purple
    'together': '#E5C07B',   # Yellow
    'nvidia': '#56B6C2',     # Cyan
    'moonshot': '#ABB2BF',   # Gray
}


def load_run018_data():
    """Load Run 018 consolidated data."""
    data_file = RESULTS_DIR / "S7_run_018_CURRENT.json"
    with open(data_file, 'r', encoding='utf-8') as f:
        return json.load(f)


def extract_trajectories(data):
    """Extract drift trajectories grouped by provider and model."""
    trajectories_by_provider = defaultdict(list)
    trajectories_by_model = defaultdict(list)

    for result in data.get('results', []):
        model = result.get('model', 'unknown')
        provider = result.get('provider', 'unknown')
        experiment = result.get('experiment', 'unknown')

        for subject in result.get('subjects', []):
            probe_seq = subject.get('probe_sequence', [])
            if len(probe_seq) < 2:
                continue

            # Extract drift values in sequence order
            drifts = []
            for probe in probe_seq:
                drift = probe.get('drift', 0)
                if drift is not None:
                    drifts.append(drift)

            if len(drifts) >= 2:
                traj = {
                    'model': model,
                    'provider': provider,
                    'experiment': experiment,
                    'drifts': drifts,
                    'peak_drift': max(drifts),
                    'final_drift': drifts[-1],
                    'baseline_to_final': subject.get('baseline_to_final_drift', 0)
                }
                trajectories_by_provider[provider].append(traj)
                trajectories_by_model[model].append(traj)

    return trajectories_by_provider, trajectories_by_model


def plot_run018_phase_plane(trajectories_by_provider, output_path):
    """Create phase-plane plot for Run 018 - PERSONA focus."""

    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()

    providers = ['anthropic', 'openai', 'google', 'xai', 'together', 'nvidia']

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        trajs = trajectories_by_provider.get(provider, [])

        color = PROVIDER_COLORS.get(provider, 'gray')

        trajectory_count = 0
        for traj in trajs:
            drifts = traj['drifts']
            if len(drifts) < 2:
                continue

            # Phase plane: plot (drift[i], drift[i+1])
            x = drifts[:-1]
            y = drifts[1:]

            # Plot trajectory with transparency
            ax.plot(x, y, '-', color=color, alpha=0.3, linewidth=0.8)

            # Mark start and end
            ax.scatter([x[0]], [y[0]], marker='o', s=15, color=color, alpha=0.5, zorder=5)
            ax.scatter([x[-1]], [y[-1]], marker='s', s=15, color=color, alpha=0.5, zorder=5)

            trajectory_count += 1

        # Event horizon lines
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', alpha=0.5, linewidth=1)
        ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', alpha=0.5, linewidth=1)

        # Diagonal (no change line)
        ax.plot([0, 1.5], [0, 1.5], 'k--', alpha=0.3, linewidth=1)

        ax.set_xlim(0, 1.5)
        ax.set_ylim(0, 1.5)
        ax.set_xlabel('Drift (t)')
        ax.set_ylabel('Drift (t+1)')
        ax.set_title(f'{provider.upper()}\n({trajectory_count} trajectories)')
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)

    fig.suptitle('RUN 018: PERSONA Phase-Plane Analysis\n(How do models respond to being given a persona under pressure?)',
                 fontsize=12, fontweight='bold')
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"Saved: {output_path}")


def plot_run018_phase_plane_by_experiment(trajectories_by_provider, output_path):
    """Create phase-plane plot comparing experiments."""

    trajectories_by_experiment = defaultdict(list)
    for provider, trajs in trajectories_by_provider.items():
        for traj in trajs:
            trajectories_by_experiment[traj['experiment']].append(traj)

    experiment_colors = {
        'threshold': '#E06C75',
        'architecture': '#61AFEF',
        'nyquist': '#98C379',
        'gravity': '#E5C07B',
    }

    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    axes = axes.flatten()

    experiments = ['threshold', 'architecture', 'nyquist', 'gravity']

    for idx, experiment in enumerate(experiments):
        ax = axes[idx]
        trajs = trajectories_by_experiment.get(experiment, [])
        color = experiment_colors.get(experiment, 'gray')

        trajectory_count = 0
        for traj in trajs:
            drifts = traj['drifts']
            if len(drifts) < 2:
                continue

            x = drifts[:-1]
            y = drifts[1:]

            ax.plot(x, y, '-', color=color, alpha=0.2, linewidth=0.8)
            ax.scatter([x[0]], [y[0]], marker='o', s=10, color=color, alpha=0.4)
            ax.scatter([x[-1]], [y[-1]], marker='s', s=10, color=color, alpha=0.4)

            trajectory_count += 1

        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', alpha=0.5)
        ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', alpha=0.5)
        ax.plot([0, 1.5], [0, 1.5], 'k--', alpha=0.3)

        ax.set_xlim(0, 1.5)
        ax.set_ylim(0, 1.5)
        ax.set_xlabel('Drift(t)')
        ax.set_ylabel('Drift(t+1)')
        ax.set_title(f'{experiment.upper()}\n({trajectory_count} trajectories)')
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)

    fig.suptitle('RUN 018: Phase-Plane by Experiment Type\n(How does probe type affect persona dynamics?)',
                 fontsize=12, fontweight='bold')
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"Saved: {output_path}")


def plot_run018_waterfall_persona(trajectories_by_provider, output_path):
    """Create waterfall plot showing persona drift over probe sequence."""

    fig, axes = plt.subplots(2, 3, figsize=(16, 10))
    axes = axes.flatten()

    providers = ['anthropic', 'openai', 'google', 'xai', 'together', 'nvidia']

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        trajs = trajectories_by_provider.get(provider, [])
        color = PROVIDER_COLORS.get(provider, 'gray')

        if not trajs:
            ax.set_title(f'{provider.upper()}\n(No data)')
            continue

        # Plot each trajectory
        for traj in trajs:
            drifts = traj['drifts']
            x = range(len(drifts))
            ax.plot(x, drifts, '-', color=color, alpha=0.15, linewidth=0.8)

        # Calculate and plot mean trajectory
        max_len = max(len(t['drifts']) for t in trajs)
        mean_trajectory = []
        for i in range(max_len):
            values = [t['drifts'][i] for t in trajs if len(t['drifts']) > i]
            if values:
                mean_trajectory.append(np.mean(values))

        ax.plot(range(len(mean_trajectory)), mean_trajectory, '-',
                color='black', linewidth=2.5, label='Mean')

        # Event horizon line
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--',
                   alpha=0.7, linewidth=1.5, label=f'EH ({EVENT_HORIZON})')

        ax.set_xlim(0, max_len - 1)
        ax.set_ylim(0, 1.3)
        ax.set_xlabel('Probe Number')
        ax.set_ylabel('Drift from Baseline')
        ax.set_title(f'{provider.upper()}\n({len(trajs)} trajectories)')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper right', fontsize=8)

    fig.suptitle('RUN 018: PERSONA Waterfall - Drift Over Probe Sequence\n(How does persona stability evolve under graduated pressure?)',
                 fontsize=12, fontweight='bold')
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"Saved: {output_path}")


def plot_run018_persona_ranking(trajectories_by_model, output_path):
    """Create bar chart ranking models by persona stability.

    NOTE: Uses Standard Error (SE = std/sqrt(n)) for error bars per Pitfall #10.
    Standard deviation produces absurdly large whiskers with continuous data.
    """

    # Compute stats per model
    models = []
    for model, trajs in trajectories_by_model.items():
        if len(trajs) >= 3:  # IRON CLAD minimum
            final_drifts = [t['final_drift'] for t in trajs]
            peak_drifts = [t['peak_drift'] for t in trajs]
            provider = trajs[0]['provider']
            n = len(final_drifts)

            models.append({
                'model': model,
                'provider': provider,
                'n': n,
                'mean_final': np.mean(final_drifts),
                # Use Standard Error instead of std dev (Pitfall #10)
                'se_final': np.std(final_drifts) / np.sqrt(n) if n > 1 else 0,
                'mean_peak': np.mean(peak_drifts),
            })

    # Sort by final drift (lower = better)
    models.sort(key=lambda x: x['mean_final'])

    # Create bar chart
    fig, ax = plt.subplots(figsize=(14, 12))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')

    y_pos = np.arange(len(models))
    colors = [PROVIDER_COLORS.get(m['provider'], 'gray') for m in models]

    bars = ax.barh(y_pos, [m['mean_final'] for m in models],
                   xerr=[m['se_final'] for m in models],
                   color=colors, alpha=0.8, capsize=2)

    # Event Horizon line
    ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--',
               linewidth=2, label=f'Event Horizon ({EVENT_HORIZON})')

    ax.set_yticks(y_pos)
    ax.set_yticklabels([f"{m['model']} (n={m['n']})" for m in models], fontsize=7)
    ax.invert_yaxis()
    ax.set_xlabel('Final Drift (lower = better persona stability)', fontsize=11)
    ax.set_title('RUN 018: Model Ranking by PERSONA Stability\n(How well do models "become" the persona under pressure?)',
                 fontsize=12, fontweight='bold')

    # Legend
    from matplotlib.patches import Patch
    legend_elements = [Patch(facecolor=c, label=p.upper())
                       for p, c in PROVIDER_COLORS.items()
                       if any(m['provider'] == p for m in models)]
    legend_elements.append(plt.Line2D([0], [0], color='red', linestyle='--', label='Event Horizon'))
    ax.legend(handles=legend_elements, loc='lower right', fontsize=9)

    ax.set_xlim(0, 1.1)
    ax.grid(axis='x', alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"Saved: {output_path}")


# ============================================================================
# 3D WATERFALL PLOTS - Identity Manifold Topology
# ============================================================================

# Dark mode settings
DARK_MODE = True
BG_COLOR = '#1E1E1E' if DARK_MODE else 'white'
TEXT_COLOR = '#E8E8E8' if DARK_MODE else 'black'
GRID_COLOR = '#404040' if DARK_MODE else 'white'


def get_pastel_cmap(dark_mode=True):
    """Create consistent colormap for all waterfall plots."""
    from matplotlib.colors import LinearSegmentedColormap

    if dark_mode:
        # Blue → Purple → Magenta → Red gradient
        colors = [
            '#4FC3F7',  # Light blue (stable/low drift)
            '#7E57C2',  # Purple (moderate)
            '#E040FB',  # Magenta (warning zone)
            '#FF5252',  # Red (high drift/unstable)
        ]
        bad_color = '#3D3D3D'  # Medium gray for NaN
    else:
        colors = [
            '#98D8AA',  # Soft mint green
            '#C4E4C1',  # Light sage
            '#F5F5DC',  # Cream/beige
            '#FFDAB9',  # Peach puff
            '#E8A0A0',  # Soft coral/rose
        ]
        bad_color = '#D0D0D0'

    cmap = LinearSegmentedColormap.from_list('drift_cmap', colors)
    cmap.set_bad(color=bad_color)
    return cmap


def get_model_family(model_name):
    """Extract model family from full model name."""
    model_lower = model_name.lower()
    if 'deepseek' in model_lower:
        return 'DeepSeek'
    elif 'llama' in model_lower:
        return 'Llama'
    elif 'mistral' in model_lower or 'mixtral' in model_lower:
        return 'Mistral'
    elif 'qwen' in model_lower:
        return 'Qwen'
    elif 'kimi' in model_lower:
        return 'Kimi'
    elif 'nemotron' in model_lower:
        return 'Nvidia'
    else:
        return 'Other'


def plot_run018_3d_waterfall_combined(trajectories_by_provider, output_path):
    """
    COMBINED 3D WATERFALL: All providers in one figure (2x3 grid).
    Shows identity manifold topology for Run 018 persona data.

    UPDATED: Shows Anthropic, OpenAI, Google, xAI, DeepSeek, Llama
    (DeepSeek and Llama extracted from Together.ai)
    """
    print("Generating 3D WATERFALL (combined)...")

    drift_cmap = get_pastel_cmap(dark_mode=DARK_MODE)

    # Category-specific colors for titles
    category_colors_bright = {
        'anthropic': '#FF9966',
        'openai': '#40E0D0',
        'google': '#87CEEB',
        'xai': '#FF6B6B',
        'DeepSeek': '#7C3AED',  # Purple
        'Llama': '#FF6B6B',     # Coral
    }

    fig = plt.figure(figsize=(18, 12), facecolor=BG_COLOR)

    # Reorganize: split Together.ai into DeepSeek and Llama
    by_category = defaultdict(list)
    for provider, trajs in trajectories_by_provider.items():
        for traj in trajs:
            if provider == 'together':
                family = get_model_family(traj['model'])
                if family in ('DeepSeek', 'Llama'):
                    by_category[family].append(traj)
            else:
                by_category[provider].append(traj)

    categories = ['anthropic', 'openai', 'google', 'xai', 'DeepSeek', 'Llama']

    for idx, category in enumerate(categories):
        trajs = by_category.get(category, [])

        if not trajs:
            ax = fig.add_subplot(2, 3, idx + 1)
            ax.set_facecolor(BG_COLOR)
            ax.text(0.5, 0.5, f'{category.upper()}\nNo data',
                   ha='center', va='center', fontsize=12, color=TEXT_COLOR)
            ax.axis('off')
            continue

        # Group by model within this category
        by_model = defaultdict(list)
        for traj in trajs:
            model = traj['model']
            by_model[model].append(traj['drifts'])

        ships = sorted(by_model.keys())
        max_probes = max(len(t['drifts']) for t in trajs)

        # Build matrix: ships x probes
        waterfall_matrix = np.zeros((len(ships), max_probes))
        waterfall_matrix[:] = np.nan

        for i, ship in enumerate(ships):
            if by_model[ship]:
                all_ts = by_model[ship]
                avg_ts = np.zeros(max_probes)
                count = np.zeros(max_probes)

                for ts in all_ts:
                    length = min(len(ts), max_probes)
                    avg_ts[:length] += np.array(ts[:length])
                    count[:length] += 1

                with np.errstate(divide='ignore', invalid='ignore'):
                    avg_ts = np.where(count > 0, avg_ts / count, np.nan)
                waterfall_matrix[i] = avg_ts

        category_color = category_colors_bright.get(category, '#E0E0E0')

        # 3D surface plot
        ax = fig.add_subplot(2, 3, idx + 1, projection='3d')
        ax.set_facecolor(BG_COLOR)

        X = np.arange(max_probes)
        Y = np.arange(len(ships))
        X, Y = np.meshgrid(X, Y)
        Z = np.nan_to_num(waterfall_matrix, nan=0)

        surf = ax.plot_surface(X, Y, Z, cmap=drift_cmap,
                               linewidth=0.1, antialiased=True, alpha=0.8,
                               vmin=0, vmax=1.5)

        ax.set_xlabel('Probe', fontsize=9, color=TEXT_COLOR)
        ax.set_ylabel('Ship', fontsize=9, color=TEXT_COLOR)
        ax.set_zlabel('Drift', fontsize=9, color=TEXT_COLOR)
        ax.set_title(f'{category.upper()}\n({len(ships)} ships, {len(trajs)} traj)',
                     fontsize=11, fontweight='bold', color=category_color)
        ax.tick_params(colors=TEXT_COLOR, labelsize=7)
        ax.view_init(elev=25, azim=-60)

    plt.suptitle('RUN 018: PERSONA Identity Manifolds\n' +
                 '(Anthropic, OpenAI, Google, xAI + DeepSeek & Llama from Together.ai)',
                 fontsize=14, fontweight='bold', color=TEXT_COLOR, y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.95])

    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor=BG_COLOR, edgecolor='none')
    plt.close()
    print(f"Saved: {output_path}")


def plot_run018_3d_waterfall_per_provider(trajectories_by_provider, output_dir):
    """
    PER-CATEGORY 3D WATERFALLS: Individual files for each category.

    UPDATED: Generates DeepSeek and Llama separately (from Together.ai),
    plus all other providers.
    """
    print("Generating 3D WATERFALLS (per category)...")

    drift_cmap = get_pastel_cmap(dark_mode=DARK_MODE)

    category_colors_bright = {
        'anthropic': '#FF9966',
        'openai': '#40E0D0',
        'google': '#87CEEB',
        'xai': '#FF6B6B',
        'DeepSeek': '#7C3AED',
        'Llama': '#FF6B6B',
        'nvidia': '#76B900',
        'moonshot': '#E0E0E0',
    }

    # Reorganize: split Together.ai into DeepSeek and Llama
    by_category = defaultdict(list)
    for provider, trajs in trajectories_by_provider.items():
        for traj in trajs:
            if provider == 'together':
                family = get_model_family(traj['model'])
                if family in ('DeepSeek', 'Llama'):
                    by_category[family].append(traj)
                # Skip other Together.ai models
            else:
                by_category[provider].append(traj)

    output_paths = []

    for category, trajs in by_category.items():
        if not trajs:
            continue

        # Group by model
        by_model = defaultdict(list)
        for traj in trajs:
            model = traj['model']
            by_model[model].append(traj['drifts'])

        ships = sorted(by_model.keys())
        max_probes = max(len(t['drifts']) for t in trajs)

        # Build matrix
        waterfall_matrix = np.zeros((len(ships), max_probes))
        waterfall_matrix[:] = np.nan

        for i, ship in enumerate(ships):
            if by_model[ship]:
                all_ts = by_model[ship]
                avg_ts = np.zeros(max_probes)
                count = np.zeros(max_probes)

                for ts in all_ts:
                    length = min(len(ts), max_probes)
                    avg_ts[:length] += np.array(ts[:length])
                    count[:length] += 1

                with np.errstate(divide='ignore', invalid='ignore'):
                    avg_ts = np.where(count > 0, avg_ts / count, np.nan)
                waterfall_matrix[i] = avg_ts

        category_color = category_colors_bright.get(category, '#E0E0E0')

        # Create figure
        fig = plt.figure(figsize=(10, 8), facecolor=BG_COLOR)
        ax = fig.add_subplot(111, projection='3d')
        ax.set_facecolor(BG_COLOR)

        X = np.arange(max_probes)
        Y = np.arange(len(ships))
        X, Y = np.meshgrid(X, Y)
        Z = np.nan_to_num(waterfall_matrix, nan=0)

        surf = ax.plot_surface(X, Y, Z, cmap=drift_cmap,
                               linewidth=0.1, antialiased=True, alpha=0.8,
                               vmin=0, vmax=1.5)

        ax.set_xlabel('Probe Number', fontsize=11, color=TEXT_COLOR)
        ax.set_ylabel('Ship Index', fontsize=11, color=TEXT_COLOR)
        ax.set_zlabel('Drift', fontsize=11, color=TEXT_COLOR)
        ax.set_title(f'RUN 018: {category.upper()} Identity Manifold\n' +
                     f'({len(ships)} ships, {len(trajs)} trajectories)',
                     fontsize=13, fontweight='bold', color=category_color)
        ax.tick_params(colors=TEXT_COLOR)
        ax.view_init(elev=25, azim=-60)

        # Colorbar
        cbar = fig.colorbar(surf, ax=ax, shrink=0.6, pad=0.1)
        cbar.set_label('Drift (cosine)', fontsize=10, color=TEXT_COLOR)
        cbar.ax.axhline(y=EVENT_HORIZON, color='#FFD700', linewidth=2, linestyle='--')
        cbar.ax.tick_params(colors=TEXT_COLOR)

        plt.tight_layout()

        # Use lowercase for filename consistency
        filename = category.lower()
        output_path = output_dir / f'run018_waterfall_3d_{filename}.png'
        plt.savefig(output_path, dpi=150, bbox_inches='tight',
                    facecolor=BG_COLOR, edgecolor='none')
        plt.close()
        print(f"Saved: {output_path}")
        output_paths.append(output_path)

    return output_paths


def main():
    print("=" * 70)
    print("RUN 018 PERSONA ANALYSIS")
    print("How do models respond to being given a persona?")
    print("=" * 70)

    # Load data
    print("\nLoading Run 018 data...")
    data = load_run018_data()

    # Extract trajectories
    print("Extracting drift trajectories...")
    by_provider, by_model = extract_trajectories(data)

    # Report
    total_trajs = sum(len(t) for t in by_provider.values())
    print(f"\nTotal trajectories: {total_trajs}")
    for provider, trajs in sorted(by_provider.items()):
        print(f"  {provider}: {len(trajs)}")

    # Generate visualizations with RUN018-SPECIFIC filenames
    print("\nGenerating Run 018 persona visualizations...")

    # REMOVED: Phase-plane visualizations were too noisy and replaced with:
    # - run018_persona_resilience.py - Beeswarm with recovery arrows (much cleaner!)
    #   Shows the key insight: it's not about avoiding the Event Horizon,
    #   it's about bouncing back. xAI crosses EH most but recovers best.
    # - run018_phase_plane_by_experiment was misleading (architecture had 0 trajectories
    #   due to different data format)

    # 3. Waterfall per provider
    plot_run018_waterfall_persona(
        by_provider,
        OUTPUT_DIR / "run018_waterfall_persona.png"
    )

    # 4. Model ranking
    plot_run018_persona_ranking(
        by_model,
        OUTPUT_DIR / "run018_persona_ranking.png"
    )

    # 5. 3D Waterfall - Combined (all providers)
    plot_run018_3d_waterfall_combined(
        by_provider,
        OUTPUT_DIR / "run018_waterfall_3d_combined.png"
    )

    # 6. 3D Waterfalls - Per provider
    plot_run018_3d_waterfall_per_provider(
        by_provider,
        OUTPUT_DIR
    )

    print("\n" + "=" * 70)
    print("RUN 018 PERSONA ANALYSIS COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    main()
