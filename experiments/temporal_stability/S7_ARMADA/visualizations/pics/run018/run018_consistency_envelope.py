#!/usr/bin/env python3
"""
RUN 018 CONSISTENCY ENVELOPE: Trajectory Bundle Analysis
=========================================================
Shows how consistent/coherent each provider's identity trajectories are over time.

This visualization complements the beeswarm arrows:
- Beeswarm: Shows individual peak→final recovery vectors
- Envelope: Shows the temporal evolution and "bundle" coherence

The envelope shows:
- Envelope Width = amplitude variability (tighter = more consistent response)
- Mean Trajectory = average temporal evolution under persona pressure
- Shaded Band = ±1 SE showing statistical uncertainty (using SE, not SD per Pitfall #10)

Author: Claude (VALIS Network)
Date: December 24, 2025
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict

# Paths
S7_ARMADA = Path(__file__).parent.parent.parent.parent
RESULTS_DIR = S7_ARMADA / "11_CONTEXT_DAMPING" / "results"
OUTPUT_DIR = Path(__file__).parent

# Thresholds
EVENT_HORIZON = 0.80
WARNING_THRESHOLD = 0.60

# Provider colors (consistent with other visualizations)
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


def extract_trajectories_by_provider(data):
    """Extract drift time series grouped by provider."""
    by_provider = defaultdict(list)

    for result in data.get('results', []):
        provider = result.get('provider', 'unknown')

        for subject in result.get('subjects', []):
            probe_seq = subject.get('probe_sequence', [])
            if len(probe_seq) < 3:
                continue

            # Extract drift values in sequence order
            drifts = []
            for probe in probe_seq:
                drift = probe.get('drift', 0)
                if drift is not None:
                    drifts.append(drift)

            if len(drifts) >= 3:
                by_provider[provider].append(drifts)

    return by_provider


def generate_consistency_envelope(by_provider, output_path):
    """
    CONSISTENCY ENVELOPE: All trajectories overlaid, showing trajectory bundle coherence.

    Shows:
    - Light lines: individual experiment trajectories
    - Bold line: mean trajectory
    - Shaded area: ±1 Standard Error (SE = std/√n)
    - Event Horizon threshold
    """
    # Sort providers by sample count for consistent layout
    providers = sorted(by_provider.keys(), key=lambda p: len(by_provider[p]), reverse=True)

    # Limit to 6 providers for 2x3 grid
    providers = providers[:6]

    fig, axes = plt.subplots(2, 3, figsize=(16, 10))
    axes = axes.flatten()

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        trajectories = by_provider[provider]
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Normalize all trajectories to same length (max 15 for Run 018's 6 probes)
        max_len = 15
        normalized = []

        for drifts in trajectories:
            if len(drifts) >= 2:
                x_orig = np.linspace(0, 1, len(drifts))
                x_new = np.linspace(0, 1, max_len)
                interp = np.interp(x_new, x_orig, drifts)
                normalized.append(interp)

        if not normalized:
            ax.text(0.5, 0.5, 'No data', ha='center', va='center')
            ax.set_title(f'{provider.upper()}', fontsize=11)
            continue

        normalized = np.array(normalized)
        n_trajectories = len(normalized)

        # Plot all trajectories (the "bundle")
        for traj in normalized:
            ax.plot(range(max_len), traj, color=color, alpha=0.12, linewidth=0.8)

        # Calculate mean and SE (Standard Error, not SD - Pitfall #10!)
        mean_traj = np.mean(normalized, axis=0)
        std_traj = np.std(normalized, axis=0)
        se_traj = std_traj / np.sqrt(n_trajectories)  # SE = std/√n

        # Plot mean trajectory
        ax.plot(range(max_len), mean_traj, color=color, linewidth=2.5,
               label='Mean trajectory')

        # Plot SE band (not SD!)
        ax.fill_between(range(max_len), mean_traj - se_traj, mean_traj + se_traj,
                       color=color, alpha=0.3, label='±1 SE')

        # Event Horizon
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--',
                  linewidth=1.5, alpha=0.7, label=f'EH={EVENT_HORIZON}')
        ax.axhline(y=WARNING_THRESHOLD, color='orange', linestyle=':',
                  linewidth=1, alpha=0.5)

        # Calculate envelope metrics
        envelope_width = np.mean(std_traj)  # Average spread
        final_drift = mean_traj[-1]
        peak_drift = np.max(mean_traj)
        recovery = peak_drift - final_drift

        ax.set_xlabel('Normalized Time →', fontsize=10)
        ax.set_ylabel('Drift', fontsize=10)
        ax.set_title(f'{provider.upper()} (n={n_trajectories})\n'
                    f'Peak: {peak_drift:.2f} → Final: {final_drift:.2f} (Δ={recovery:.2f})',
                    fontsize=11, fontweight='bold')
        ax.set_ylim(-0.05, 1.4)
        ax.set_xlim(0, max_len-1)
        ax.grid(True, alpha=0.3)

        if idx == 0:
            ax.legend(loc='upper right', fontsize=8)

    # Hide unused axes
    for idx in range(len(providers), 6):
        axes[idx].set_visible(False)

    plt.suptitle('RUN 018: CONSISTENCY ENVELOPE - Persona Response Dynamics\n'
                 '(How coherently does each provider respond to persona pressure over time?)',
                 fontsize=13, fontweight='bold', y=1.02)
    plt.tight_layout()

    plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_path.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"Saved: {output_path}")
    return output_path


def print_envelope_stats(by_provider):
    """Print envelope statistics."""
    print("\n" + "=" * 70)
    print("CONSISTENCY ENVELOPE STATISTICS")
    print("=" * 70)

    rows = []
    for provider, trajectories in by_provider.items():
        if len(trajectories) < 3:
            continue

        # Normalize to same length
        max_len = 15
        normalized = []
        for drifts in trajectories:
            if len(drifts) >= 2:
                x_orig = np.linspace(0, 1, len(drifts))
                x_new = np.linspace(0, 1, max_len)
                interp = np.interp(x_new, x_orig, drifts)
                normalized.append(interp)

        if not normalized:
            continue

        normalized = np.array(normalized)
        mean_traj = np.mean(normalized, axis=0)
        std_traj = np.std(normalized, axis=0)

        rows.append({
            'provider': provider,
            'n': len(normalized),
            'envelope_width': np.mean(std_traj),
            'peak': np.max(mean_traj),
            'final': mean_traj[-1],
            'recovery': np.max(mean_traj) - mean_traj[-1]
        })

    # Sort by final drift (best recovery first)
    rows.sort(key=lambda r: r['final'])

    print(f"\n{'Provider':<12} {'N':>6} {'Envelope':>10} {'Peak':>8} {'Final':>8} {'Recovery':>10}")
    print("-" * 70)

    for r in rows:
        print(f"{r['provider']:<12} {r['n']:>6} {r['envelope_width']:>10.3f} "
              f"{r['peak']:>8.3f} {r['final']:>8.3f} {r['recovery']:>10.3f}")

    print("\n" + "=" * 70)
    print("NOTE: Envelope Width = average std across trajectory (lower = more consistent)")
    print("      Recovery = Peak - Final (higher = better bounce-back)")
    print("=" * 70)


def main():
    print("=" * 60)
    print("RUN 018: CONSISTENCY ENVELOPE ANALYSIS")
    print("How coherently does each provider respond to persona pressure?")
    print("=" * 60)

    # Load data
    print("\nLoading Run 018 data...")
    data = load_run018_data()

    # Extract trajectories
    print("Extracting drift trajectories...")
    by_provider = extract_trajectories_by_provider(data)

    total = sum(len(t) for t in by_provider.values())
    print(f"\nTotal trajectories: {total}")
    for provider, trajs in sorted(by_provider.items()):
        print(f"  {provider}: {len(trajs)}")

    # Print statistics
    print_envelope_stats(by_provider)

    # Generate visualization
    print("\nGenerating consistency envelope visualization...")
    output_path = OUTPUT_DIR / "run018_consistency_envelope.png"
    generate_consistency_envelope(by_provider, output_path)

    print("\nDone!")


if __name__ == "__main__":
    main()
