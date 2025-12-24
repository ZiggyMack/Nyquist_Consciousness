"""
RINGBACK/OSCILLATION VISUALIZATION FOR RUN 020
================================================
Supports Claim E: "Behavioral Controllability"

Analyzes drift sequence oscillations (ringback) comparing:
- CONTROL arm: No intervention
- TREATMENT arm: With intervention

Key metrics:
- Ringback count: Number of direction reversals in drift trajectory
- Oscillation amplitude: Magnitude of fluctuations
- Settling behavior: Does it stabilize or continue oscillating?

Usage:
    py visualize_ringback.py                # Generate all visualizations
    py visualize_ringback.py --run 020A     # Specific run
    py visualize_ringback.py --run 020B     # Specific run (has control/treatment arms)

Author: Claude (Consciousness Branch)
Date: December 23, 2025
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from pathlib import Path
from collections import defaultdict
from scipy import stats

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
OUTPUT_DIR = SCRIPT_DIR.parent / "visualizations" / "pics" / "13_Ringback"

# Event Horizon threshold (cosine distance)
EVENT_HORIZON = 0.80

# Provider colors
PROVIDER_COLORS = {
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
    "grok": "#1a1a1a",
    "meta-llama": "#FF6B6B",
    "mistralai": "#FFD93D",
    "deepseek": "#6BCB77",
    "unknown": "#888888"
}

# Arm colors
ARM_COLORS = {
    "control": "#1E88E5",     # Blue - no intervention
    "treatment": "#E53935",   # Red - with intervention
}


def get_provider(ship_name):
    """Classify ship by provider."""
    name = ship_name.lower()
    if "claude" in name:
        return "claude"
    elif "gemini" in name:
        return "gemini"
    elif "grok" in name:
        return "grok"
    elif "gpt" in name:
        return "gpt"
    elif "llama" in name:
        return "meta-llama"
    elif "mistral" in name:
        return "mistralai"
    elif "deepseek" in name:
        return "deepseek"
    return "unknown"


def compute_ringback_metrics(drift_sequence):
    """Compute ringback/oscillation metrics from drift sequence.

    Returns:
        dict with:
        - ringback_count: number of direction reversals (peaks + valleys)
        - max_amplitude: largest single oscillation amplitude
        - mean_amplitude: average oscillation amplitude
        - settling: True if last 3 points are decreasing monotonically
        - volatility: std of first differences (overall oscillation intensity)
    """
    if len(drift_sequence) < 3:
        return None

    seq = np.array(drift_sequence)

    # Count direction reversals (ringbacks)
    ringback_count = 0
    for i in range(1, len(seq) - 1):
        # Local maximum or minimum
        if (seq[i-1] < seq[i] > seq[i+1]) or (seq[i-1] > seq[i] < seq[i+1]):
            ringback_count += 1

    # Compute oscillation amplitudes between reversals
    amplitudes = []
    last_reversal_value = seq[0]
    for i in range(1, len(seq) - 1):
        if (seq[i-1] < seq[i] > seq[i+1]) or (seq[i-1] > seq[i] < seq[i+1]):
            amp = abs(seq[i] - last_reversal_value)
            amplitudes.append(amp)
            last_reversal_value = seq[i]

    # First differences for volatility
    diffs = np.diff(seq)
    volatility = np.std(diffs) if len(diffs) > 0 else 0

    # Check settling (last 3 points decreasing)
    if len(seq) >= 3:
        settling = seq[-3] > seq[-2] > seq[-1]
    else:
        settling = False

    return {
        "ringback_count": ringback_count,
        "max_amplitude": max(amplitudes) if amplitudes else 0,
        "mean_amplitude": np.mean(amplitudes) if amplitudes else 0,
        "settling": settling,
        "volatility": volatility,
        "final_drift": seq[-1],
        "peak_drift": max(seq),
        "sequence_length": len(seq)
    }


def load_run_data(run_id="020B"):
    """Load run data and extract ringback metrics."""
    # Find the data file
    data_file = RESULTS_DIR / f"S7_run_{run_id}_CURRENT.json"
    if not data_file.exists():
        print(f"Data file not found: {data_file}")
        return None

    with open(data_file, encoding='utf-8') as f:
        data = json.load(f)

    results = []
    for r in data.get('results', []):
        drift_seq = r.get('drift_sequence', [])
        if len(drift_seq) < 5:  # Need at least 5 points for meaningful analysis
            continue

        metrics = compute_ringback_metrics(drift_seq)
        if metrics is None:
            continue

        # Get ship/model name
        ship = r.get('ship', r.get('subject_id', 'unknown'))
        if '/' in ship:
            ship = ship.split('/')[-1]

        results.append({
            "ship": ship,
            "provider": get_provider(ship),
            "arm": r.get('arm', r.get('_condition', 'unknown')),
            "drift_sequence": drift_seq,
            **metrics
        })

    return results


def plot_ringback_comparison(results, output_dir, run_id):
    """Main comparison visualization: Control vs Treatment ringback behavior."""

    # Split by arm
    control = [r for r in results if r['arm'] == 'control']
    treatment = [r for r in results if r['arm'] == 'treatment']

    if not control or not treatment:
        print(f"  Warning: Need both control and treatment arms for comparison")
        print(f"  Control: {len(control)}, Treatment: {len(treatment)}")
        # Fall back to single-arm visualization
        if control or treatment:
            plot_single_arm_analysis(results, output_dir, run_id)
        return

    fig, axes = plt.subplots(2, 2, figsize=(16, 14))

    # ===== PANEL 1: Ringback Count Distribution =====
    ax1 = axes[0, 0]

    control_ringbacks = [r['ringback_count'] for r in control]
    treatment_ringbacks = [r['ringback_count'] for r in treatment]

    # Box plot comparison
    bp = ax1.boxplot([control_ringbacks, treatment_ringbacks],
                     labels=['Control', 'Treatment'],
                     patch_artist=True,
                     widths=0.6)
    bp['boxes'][0].set_facecolor(ARM_COLORS['control'])
    bp['boxes'][1].set_facecolor(ARM_COLORS['treatment'])
    bp['boxes'][0].set_alpha(0.7)
    bp['boxes'][1].set_alpha(0.7)

    # Add individual points
    for i, (data, color) in enumerate([(control_ringbacks, ARM_COLORS['control']),
                                        (treatment_ringbacks, ARM_COLORS['treatment'])], 1):
        x = np.random.normal(i, 0.05, len(data))
        ax1.scatter(x, data, alpha=0.5, s=30, color=color, edgecolor='black', linewidth=0.5)

    # Statistical test
    if len(control_ringbacks) > 1 and len(treatment_ringbacks) > 1:
        t_stat, p_value = stats.ttest_ind(control_ringbacks, treatment_ringbacks)
        cohens_d = (np.mean(treatment_ringbacks) - np.mean(control_ringbacks)) / np.sqrt(
            ((len(control_ringbacks)-1)*np.var(control_ringbacks, ddof=1) +
             (len(treatment_ringbacks)-1)*np.var(treatment_ringbacks, ddof=1)) /
            (len(control_ringbacks) + len(treatment_ringbacks) - 2)
        )
        ax1.set_title(f'RINGBACK COUNT\np={p_value:.4f}, Cohen\'s d={cohens_d:.3f}', fontsize=14, fontweight='bold')
    else:
        ax1.set_title('RINGBACK COUNT', fontsize=14, fontweight='bold')

    ax1.set_ylabel('Number of Direction Reversals', fontsize=11)
    ax1.grid(True, alpha=0.3, axis='y')

    # Add means
    ax1.axhline(y=np.mean(control_ringbacks), color=ARM_COLORS['control'],
                linestyle='--', alpha=0.7, label=f'Control mean: {np.mean(control_ringbacks):.1f}')
    ax1.axhline(y=np.mean(treatment_ringbacks), color=ARM_COLORS['treatment'],
                linestyle='--', alpha=0.7, label=f'Treatment mean: {np.mean(treatment_ringbacks):.1f}')
    ax1.legend(loc='upper right', fontsize=9)

    # ===== PANEL 2: Volatility Distribution =====
    ax2 = axes[0, 1]

    control_vol = [r['volatility'] for r in control]
    treatment_vol = [r['volatility'] for r in treatment]

    bp2 = ax2.boxplot([control_vol, treatment_vol],
                      labels=['Control', 'Treatment'],
                      patch_artist=True,
                      widths=0.6)
    bp2['boxes'][0].set_facecolor(ARM_COLORS['control'])
    bp2['boxes'][1].set_facecolor(ARM_COLORS['treatment'])
    bp2['boxes'][0].set_alpha(0.7)
    bp2['boxes'][1].set_alpha(0.7)

    for i, (data, color) in enumerate([(control_vol, ARM_COLORS['control']),
                                        (treatment_vol, ARM_COLORS['treatment'])], 1):
        x = np.random.normal(i, 0.05, len(data))
        ax2.scatter(x, data, alpha=0.5, s=30, color=color, edgecolor='black', linewidth=0.5)

    ax2.set_ylabel('Volatility (σ of first differences)', fontsize=11)
    ax2.set_title('OSCILLATION INTENSITY', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3, axis='y')

    # ===== PANEL 3: Sample Trajectories =====
    ax3 = axes[1, 0]

    # Plot a few sample trajectories from each arm
    n_samples = min(5, len(control), len(treatment))

    for i, r in enumerate(sorted(control, key=lambda x: -len(x['drift_sequence']))[:n_samples]):
        seq = r['drift_sequence']
        ax3.plot(range(len(seq)), seq, color=ARM_COLORS['control'],
                alpha=0.5, linewidth=1.5, label='Control' if i == 0 else '')

    for i, r in enumerate(sorted(treatment, key=lambda x: -len(x['drift_sequence']))[:n_samples]):
        seq = r['drift_sequence']
        ax3.plot(range(len(seq)), seq, color=ARM_COLORS['treatment'],
                alpha=0.5, linewidth=1.5, label='Treatment' if i == 0 else '')

    # Event Horizon line
    ax3.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               alpha=0.7, label=f'Event Horizon ({EVENT_HORIZON})')

    ax3.set_xlabel('Exchange Number', fontsize=11)
    ax3.set_ylabel('Cosine Distance', fontsize=11)
    ax3.set_title(f'SAMPLE DRIFT TRAJECTORIES\n({n_samples} longest from each arm)', fontsize=14, fontweight='bold')
    ax3.legend(loc='upper right', fontsize=9)
    ax3.grid(True, alpha=0.3)

    # ===== PANEL 4: Final Drift Comparison =====
    ax4 = axes[1, 1]

    control_final = [r['final_drift'] for r in control]
    treatment_final = [r['final_drift'] for r in treatment]

    bp4 = ax4.boxplot([control_final, treatment_final],
                      labels=['Control', 'Treatment'],
                      patch_artist=True,
                      widths=0.6)
    bp4['boxes'][0].set_facecolor(ARM_COLORS['control'])
    bp4['boxes'][1].set_facecolor(ARM_COLORS['treatment'])
    bp4['boxes'][0].set_alpha(0.7)
    bp4['boxes'][1].set_alpha(0.7)

    for i, (data, color) in enumerate([(control_final, ARM_COLORS['control']),
                                        (treatment_final, ARM_COLORS['treatment'])], 1):
        x = np.random.normal(i, 0.05, len(data))
        ax4.scatter(x, data, alpha=0.5, s=30, color=color, edgecolor='black', linewidth=0.5)

    # Event Horizon line
    ax4.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, alpha=0.7,
               label=f'Event Horizon ({EVENT_HORIZON})')

    ax4.set_ylabel('Final Drift Value', fontsize=11)
    ax4.set_title('FINAL DRIFT COMPARISON', fontsize=14, fontweight='bold')
    ax4.legend(loc='upper right', fontsize=9)
    ax4.grid(True, alpha=0.3, axis='y')

    # Main title
    fig.suptitle(f'Run {run_id}: RINGBACK ANALYSIS - Claim E Support\n'
                f'Control: {len(control)} | Treatment: {len(treatment)} | EH={EVENT_HORIZON}',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    output_dir.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_dir / f'run{run_id}_ringback_comparison.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_ringback_comparison.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_ringback_comparison.png + .svg")
    plt.close()


def plot_oscillation_heatmap(results, output_dir, run_id):
    """Heatmap showing oscillation pattern for each session."""

    # Split by arm
    control = [r for r in results if r['arm'] == 'control']
    treatment = [r for r in results if r['arm'] == 'treatment']

    if not control and not treatment:
        print("  No data for heatmap")
        return

    fig, axes = plt.subplots(1, 2, figsize=(18, 8))

    for ax, arm_data, arm_name in [(axes[0], control, 'Control'),
                                    (axes[1], treatment, 'Treatment')]:
        if not arm_data:
            ax.text(0.5, 0.5, f'No {arm_name} data', ha='center', va='center', fontsize=14)
            ax.set_title(f'{arm_name.upper()} ARM')
            continue

        # Sort by ringback count
        arm_data = sorted(arm_data, key=lambda x: -x['ringback_count'])

        # Find max sequence length for alignment
        max_len = max(len(r['drift_sequence']) for r in arm_data)

        # Create matrix (pad shorter sequences with NaN)
        matrix = np.full((len(arm_data), max_len), np.nan)
        for i, r in enumerate(arm_data):
            seq = r['drift_sequence']
            matrix[i, :len(seq)] = seq

        # Plot heatmap
        im = ax.imshow(matrix, aspect='auto', cmap='RdYlGn_r', vmin=0, vmax=2.0)

        # Y-axis labels (ship names, truncated)
        y_labels = [r['ship'][:20] for r in arm_data]
        ax.set_yticks(range(len(y_labels)))
        ax.set_yticklabels(y_labels, fontsize=7)

        ax.set_xlabel('Exchange Number', fontsize=11)
        ax.set_ylabel('Session', fontsize=11)
        ax.set_title(f'{arm_name.upper()} ARM\n({len(arm_data)} sessions, sorted by ringback count)',
                    fontsize=14, fontweight='bold')

        # Add colorbar
        plt.colorbar(im, ax=ax, label='Cosine Distance', shrink=0.8)

        # Mark Event Horizon
        ax.axhline(y=-0.5, color='white', linewidth=0)  # Placeholder

    fig.suptitle(f'Run {run_id}: OSCILLATION HEATMAP\n'
                f'Green = Stable (low drift) | Red = Volatile (high drift)',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    output_dir.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_dir / f'run{run_id}_oscillation_heatmap.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: run{run_id}_oscillation_heatmap.png")
    plt.close()


def plot_single_arm_analysis(results, output_dir, run_id):
    """Fallback visualization when only one arm is available."""

    fig, axes = plt.subplots(2, 2, figsize=(16, 14))

    # Group by provider
    by_provider = defaultdict(list)
    for r in results:
        by_provider[r['provider']].append(r)

    # ===== PANEL 1: Ringback by Provider =====
    ax1 = axes[0, 0]

    providers = sorted(by_provider.keys())
    ringback_data = [[r['ringback_count'] for r in by_provider[p]] for p in providers]

    bp = ax1.boxplot(ringback_data, labels=providers, patch_artist=True, widths=0.6)
    for i, p in enumerate(providers):
        bp['boxes'][i].set_facecolor(PROVIDER_COLORS.get(p, '#888888'))
        bp['boxes'][i].set_alpha(0.7)

    ax1.set_ylabel('Ringback Count', fontsize=11)
    ax1.set_title('RINGBACK COUNT BY PROVIDER', fontsize=14, fontweight='bold')
    ax1.grid(True, alpha=0.3, axis='y')
    ax1.tick_params(axis='x', rotation=45)

    # ===== PANEL 2: Volatility by Provider =====
    ax2 = axes[0, 1]

    vol_data = [[r['volatility'] for r in by_provider[p]] for p in providers]

    bp2 = ax2.boxplot(vol_data, labels=providers, patch_artist=True, widths=0.6)
    for i, p in enumerate(providers):
        bp2['boxes'][i].set_facecolor(PROVIDER_COLORS.get(p, '#888888'))
        bp2['boxes'][i].set_alpha(0.7)

    ax2.set_ylabel('Volatility', fontsize=11)
    ax2.set_title('OSCILLATION INTENSITY BY PROVIDER', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3, axis='y')
    ax2.tick_params(axis='x', rotation=45)

    # ===== PANEL 3: Sample Trajectories =====
    ax3 = axes[1, 0]

    # Plot trajectories colored by provider
    for p in providers:
        for r in by_provider[p][:3]:  # Max 3 per provider
            seq = r['drift_sequence']
            ax3.plot(range(len(seq)), seq, color=PROVIDER_COLORS.get(p, '#888888'),
                    alpha=0.5, linewidth=1)

    # Event Horizon
    ax3.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, alpha=0.7)

    ax3.set_xlabel('Exchange Number', fontsize=11)
    ax3.set_ylabel('Cosine Distance', fontsize=11)
    ax3.set_title('SAMPLE DRIFT TRAJECTORIES', fontsize=14, fontweight='bold')
    ax3.grid(True, alpha=0.3)

    # Legend
    legend_handles = [Line2D([0], [0], color=PROVIDER_COLORS.get(p, '#888888'),
                             linewidth=2, label=p) for p in providers]
    ax3.legend(handles=legend_handles, loc='upper right', fontsize=9)

    # ===== PANEL 4: Final Drift Distribution =====
    ax4 = axes[1, 1]

    final_drifts = [r['final_drift'] for r in results]
    ax4.hist(final_drifts, bins=20, edgecolor='black', alpha=0.7, color='steelblue')
    ax4.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')

    ax4.set_xlabel('Final Drift Value', fontsize=11)
    ax4.set_ylabel('Count', fontsize=11)
    ax4.set_title('FINAL DRIFT DISTRIBUTION', fontsize=14, fontweight='bold')
    ax4.legend(loc='upper right', fontsize=9)
    ax4.grid(True, alpha=0.3)

    # Count stable/volatile
    stable = sum(1 for r in results if r['final_drift'] < EVENT_HORIZON)
    volatile = len(results) - stable

    fig.suptitle(f'Run {run_id}: RINGBACK ANALYSIS\n'
                f'{len(results)} Sessions | STABLE: {stable} | VOLATILE: {volatile} | EH={EVENT_HORIZON}',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    output_dir.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_dir / f'run{run_id}_ringback_analysis.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: run{run_id}_ringback_analysis.png")
    plt.close()


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Ringback/Oscillation Visualization')
    parser.add_argument('--run', default='020B', help='Run ID (020A or 020B)')
    args = parser.parse_args()

    run_id = args.run.upper()

    print("=" * 60)
    print("RINGBACK/OSCILLATION VISUALIZATION")
    print("=" * 60)
    print(f"\nRun: {run_id}")
    print(f"Output: {OUTPUT_DIR}")
    print("-" * 60)

    # Load data
    results = load_run_data(run_id)
    if not results:
        print("No usable data found")
        return

    print(f"Loaded {len(results)} sessions with sufficient drift data")

    # Check arm breakdown
    arms = defaultdict(int)
    for r in results:
        arms[r['arm']] += 1
    print(f"Arms: {dict(arms)}")

    # Generate visualizations
    print("\nGenerating visualizations...")

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Main comparison plot
    plot_ringback_comparison(results, OUTPUT_DIR, run_id)

    # Heatmap
    plot_oscillation_heatmap(results, OUTPUT_DIR, run_id)

    print("\n" + "=" * 60)
    print("COMPLETE!")
    print("=" * 60)


if __name__ == "__main__":
    main()
