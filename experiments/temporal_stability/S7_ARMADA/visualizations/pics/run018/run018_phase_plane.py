"""
RUN 018 PHASE-PLANE ANALYSIS: Persona Response Dynamics
========================================================
How do different models respond to being given a persona?

QUESTION: When we give a model an I_AM persona and apply existential pressure,
how does its identity drift evolve? The phase-plane reveals attractor dynamics.

Phase-plane coordinates:
- X-axis: drift(t) - current drift from baseline
- Y-axis: drift(t+1) - drift at next probe

Patterns to look for:
- Stable spiral: converging to attractor (strong identity)
- Limit cycle: oscillating (unstable but bounded)
- Divergent: drifting away (identity collapse)
- Fixed point: staying near origin (rock-solid identity)
"""

import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
from collections import defaultdict

# Paths
S7_ARMADA = Path(__file__).parent.parent.parent.parent.parent
RESULTS_DIR = S7_ARMADA / "11_CONTEXT_DAMPING" / "results"
OUTPUT_DIR = Path(__file__).parent

# Event Horizon (cosine methodology)
EVENT_HORIZON = 0.80

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

def plot_phase_plane_by_provider(trajectories_by_provider, output_path):
    """Create phase-plane plot colored by provider."""

    # Provider colors
    provider_colors = {
        'anthropic': '#E06C75',  # Red
        'openai': '#61AFEF',     # Blue
        'google': '#98C379',     # Green
        'xai': '#C678DD',        # Purple
        'together': '#E5C07B',   # Yellow
        'nvidia': '#56B6C2',     # Cyan
    }

    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()

    providers = ['anthropic', 'openai', 'google', 'xai', 'together', 'nvidia']

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        trajs = trajectories_by_provider.get(provider, [])

        color = provider_colors.get(provider, 'gray')

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
        ax.set_xlabel('Drift (position)')
        ax.set_ylabel('Drift (velocity)')
        ax.set_title(f'{provider.upper()}\n({trajectory_count} trajectories)')
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)

    fig.suptitle('PHASE-PLANE ANALYSIS: Identity Attractor Dynamics\n(Circle = start, Square = settled | Limited to 6 probes - Run 023d: 20 probes)',
                 fontsize=12, fontweight='bold')
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"Saved: {output_path}")

def plot_phase_plane_by_experiment(trajectories_by_provider, output_path):
    """Create phase-plane plot comparing experiments."""

    # Collect all trajectories by experiment
    trajectories_by_experiment = defaultdict(list)
    for provider, trajs in trajectories_by_provider.items():
        for traj in trajs:
            trajectories_by_experiment[traj['experiment']].append(traj)

    experiment_colors = {
        'threshold': '#E06C75',    # Red
        'architecture': '#61AFEF', # Blue
        'nyquist': '#98C379',      # Green
        'gravity': '#E5C07B',      # Yellow
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

        # Event horizon
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

    fig.suptitle('RUN 018: Phase-Plane by Experiment Type\n(How does probe type affect identity dynamics?)',
                 fontsize=12, fontweight='bold')
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.close()
    print(f"Saved: {output_path}")

def compute_attractor_statistics(trajectories_by_provider):
    """Compute statistics about attractor behavior."""
    stats = {}

    for provider, trajs in trajectories_by_provider.items():
        if not trajs:
            continue

        # Collect final drifts
        final_drifts = [t['final_drift'] for t in trajs if t['final_drift'] is not None]
        peak_drifts = [t['peak_drift'] for t in trajs if t['peak_drift'] is not None]

        if final_drifts:
            stats[provider] = {
                'count': len(trajs),
                'mean_final_drift': np.mean(final_drifts),
                'std_final_drift': np.std(final_drifts),
                'mean_peak_drift': np.mean(peak_drifts),
                'crossed_eh_rate': sum(1 for d in peak_drifts if d > EVENT_HORIZON) / len(peak_drifts),
                'recovered_rate': sum(1 for i, t in enumerate(trajs)
                                     if t['final_drift'] < t['peak_drift'] * 0.8) / len(trajs)
            }

    return stats

def main():
    print("=" * 60)
    print("RUN 018 PHASE-PLANE ANALYSIS")
    print("How do models respond to persona pressure?")
    print("=" * 60)

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

    # Create visualizations
    print("\nGenerating phase-plane plots...")

    # By provider
    output1 = OUTPUT_DIR / "phase_plane_attractor.png"
    plot_phase_plane_by_provider(by_provider, output1)

    # By experiment
    output2 = OUTPUT_DIR / "phase_plane_by_experiment.png"
    plot_phase_plane_by_experiment(by_provider, output2)

    # Statistics
    print("\n" + "=" * 60)
    print("ATTRACTOR STATISTICS BY PROVIDER")
    print("=" * 60)
    stats = compute_attractor_statistics(by_provider)

    for provider, s in sorted(stats.items()):
        print(f"\n{provider.upper()} (n={s['count']}):")
        print(f"  Mean final drift: {s['mean_final_drift']:.3f} ± {s['std_final_drift']:.3f}")
        print(f"  Mean peak drift:  {s['mean_peak_drift']:.3f}")
        print(f"  Crossed EH rate:  {s['crossed_eh_rate']:.1%}")
        print(f"  Recovery rate:    {s['recovered_rate']:.1%}")

    print("\n" + "=" * 60)
    print("PHASE-PLANE ANALYSIS COMPLETE")
    print("=" * 60)

if __name__ == "__main__":
    main()
