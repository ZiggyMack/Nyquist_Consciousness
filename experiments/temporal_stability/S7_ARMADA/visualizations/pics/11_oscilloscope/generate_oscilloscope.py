"""
Oscilloscope Visualization: Cognitive Waveform Display

Renders identity drift sequences as analog-style oscilloscope traces.
Supports any run that has drift trajectory data.

Style: Green phosphor on black background, gridlines, retro CRT aesthetic.

USAGE:
    python generate_oscilloscope.py --run 010  # Run 010 (original)
    python generate_oscilloscope.py --run 018  # Run 018 (IRON CLAD)
    python generate_oscilloscope.py --run 009  # Run 009 (Event Horizon)
"""

import json
import argparse
import re
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from pathlib import Path
from collections import defaultdict

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent.parent.parent
OUTPUT_DIR = SCRIPT_DIR

# Colors - Oscilloscope aesthetic
BG_COLOR = '#000000'  # Black background
GRID_COLOR = '#1a3a1a'  # Dark green grid
TRACE_COLOR = '#00ff00'  # Bright green phosphor
TRACE_COLOR_2 = '#00cc00'  # Slightly dimmer green
AXIS_COLOR = '#00aa00'  # Medium green for axes
TEXT_COLOR = '#00ff00'  # Green text
EVENT_HORIZON_COLOR = '#ff4444'  # Red for Event Horizon reference

# Event Horizon threshold
EVENT_HORIZON = 1.23

# Provider colors
PROVIDER_COLORS = {
    'claude': '#00ff00',  # Green (Anthropic)
    'gpt': '#00ccff',     # Cyan (OpenAI)
    'gemini': '#ffcc00',  # Yellow (Google)
    'grok': '#ff6600',    # Orange (xAI)
    'together': '#ff00ff', # Magenta (Together.ai)
    'openai': '#00ccff',   # Cyan (alias)
    'anthropic': '#00ff00', # Green (alias)
    'google': '#ffcc00',   # Yellow (alias)
    'xai': '#ff6600',      # Orange (alias)
}


def load_run_data(run_id: str):
    """Load run data from JSON files - supports multiple data formats."""
    runs_dir = ARMADA_DIR / "0_results" / "runs"
    legacy_dir = runs_dir / "legacy_runs"
    temporal_dir = ARMADA_DIR / "0_results" / "temporal_logs"

    # For Run 018+, check temporal_logs FIRST (these are the primary source)
    if int(run_id) >= 18 and temporal_dir.exists():
        log_files = list(temporal_dir.glob(f"run{run_id}_*.json"))
        if log_files:
            print(f"Found {len(log_files)} temporal log files for run {run_id}")
            all_trajectories = []
            for log_file in log_files:
                try:
                    with open(log_file, 'r', encoding='utf-8') as f:
                        log_data = json.load(f)
                    # Extract trajectory from temporal log
                    if 'recovery_sequence' in log_data:
                        traj = {
                            'ship': log_data.get('model', log_file.stem),
                            'model': log_data.get('model', log_file.stem),
                            'provider': log_data.get('provider', 'unknown'),
                            'drift_sequence': log_data['recovery_sequence'],
                            'drifts': log_data['recovery_sequence'],
                        }
                        all_trajectories.append(traj)
                except Exception as e:
                    print(f"  Warning: Could not load {log_file.name}: {e}")
                    continue

            if all_trajectories:
                return {'trajectories_for_3d': all_trajectories}, 'temporal_logs'

    # Try consolidated run files for older runs
    patterns = [
        (runs_dir, f"S7_run_{run_id}_*.json"),
        (runs_dir, f"*run_{run_id}_*.json"),
        (legacy_dir, f"S7_run_{run_id}_*.json"),
        (legacy_dir, f"*run_{run_id}_*.json"),
    ]

    for search_dir, pattern in patterns:
        if search_dir.exists():
            matches = list(search_dir.glob(pattern))
            if matches:
                matches.sort(key=lambda x: x.stat().st_mtime, reverse=True)
                print(f"Found run file: {matches[0].name}")
                with open(matches[0], 'r', encoding='utf-8') as f:
                    data = json.load(f)
                # Check if this file has trajectory data
                if data.get('trajectories_for_3d') or data.get('trajectories'):
                    return data, 'consolidated'

    # Fall back to temporal_logs for any run
    if temporal_dir.exists():
        log_files = list(temporal_dir.glob(f"run{run_id}_*.json"))
        if log_files:
            print(f"Found {len(log_files)} temporal log files for run {run_id}")
            all_trajectories = []
            for log_file in log_files:
                try:
                    with open(log_file, 'r', encoding='utf-8') as f:
                        log_data = json.load(f)
                    # Extract trajectory from temporal log
                    if 'recovery_sequence' in log_data:
                        traj = {
                            'ship': log_data.get('model', log_file.stem),
                            'model': log_data.get('model', log_file.stem),
                            'provider': log_data.get('provider', 'unknown'),
                            'drift_sequence': log_data['recovery_sequence'],
                            'drifts': log_data['recovery_sequence'],
                        }
                        all_trajectories.append(traj)
                except Exception as e:
                    print(f"  Warning: Could not load {log_file.name}: {e}")
                    continue

            if all_trajectories:
                return {'trajectories_for_3d': all_trajectories}, 'temporal_logs'

    raise FileNotFoundError(f"No data found for run {run_id}")

def create_oscilloscope_grid(ax):
    """Create oscilloscope-style grid on axes."""
    ax.set_facecolor(BG_COLOR)
    ax.grid(True, color=GRID_COLOR, linewidth=0.5, alpha=0.7)
    ax.spines['bottom'].set_color(AXIS_COLOR)
    ax.spines['top'].set_color(AXIS_COLOR)
    ax.spines['left'].set_color(AXIS_COLOR)
    ax.spines['right'].set_color(AXIS_COLOR)
    ax.tick_params(colors=AXIS_COLOR, which='both')

def create_single_trace(ax, drift_sequence, label, y_max=None, n_turns=None):
    """Create a single oscilloscope trace."""
    turns = np.arange(len(drift_sequence))
    n_turns = n_turns or len(drift_sequence)

    # Interpolate for smoother curve
    turns_smooth = np.linspace(0, len(drift_sequence) - 1, 100)
    drift_smooth = np.interp(turns_smooth, turns, drift_sequence)

    # Plot the trace with glow effect
    ax.plot(turns_smooth, drift_smooth, color=TRACE_COLOR, linewidth=2, alpha=0.8)
    ax.plot(turns_smooth, drift_smooth, color=TRACE_COLOR, linewidth=4, alpha=0.3)  # Glow

    # Add dots at actual data points
    ax.scatter(turns, drift_sequence, color=TRACE_COLOR, s=30, zorder=5)

    create_oscilloscope_grid(ax)
    ax.set_xlim(-0.5, n_turns - 0.5)

    # Dynamic Y-axis based on data
    if y_max is None:
        y_max = max(max(drift_sequence) * 1.1, EVENT_HORIZON * 1.2)
    ax.set_ylim(-0.05, y_max)

    ax.set_xticks(range(n_turns))
    ax.set_xticklabels([str(i) for i in range(n_turns)], fontsize=7, color=TEXT_COLOR)
    ax.set_xlabel('Turn', color=TEXT_COLOR, fontsize=8)
    ax.set_ylabel('Drift', color=TEXT_COLOR, fontsize=10)
    ax.set_title(label, color=TEXT_COLOR, fontsize=9, fontweight='bold')

    # Add horizontal reference line at Event Horizon (1.23)
    ax.axhline(y=EVENT_HORIZON, color=EVENT_HORIZON_COLOR, linestyle='--', alpha=0.7, linewidth=1.5, label='EH 1.23')

def create_overlay_traces(ax, trajectories, title, y_max=None):
    """Create multiple overlaid traces for comparison."""
    create_oscilloscope_grid(ax)

    # Find max turns and max drift
    max_turns = max(len(t.get('drift_sequence', t.get('drifts', []))) for t in trajectories)
    all_drifts = []

    # Collect unique providers for legend
    providers_seen = set()

    for traj in trajectories:
        provider = traj.get('provider', 'unknown')
        providers_seen.add(provider)
        color = PROVIDER_COLORS.get(provider, '#00ff00')
        drift_seq = traj.get('drift_sequence', traj.get('drifts', []))
        all_drifts.extend(drift_seq)
        turns = np.arange(len(drift_seq))

        # Interpolate for smoother curve
        if len(drift_seq) > 1:
            turns_smooth = np.linspace(0, len(drift_seq) - 1, 100)
            drift_smooth = np.interp(turns_smooth, turns, drift_seq)
            ax.plot(turns_smooth, drift_smooth, color=color, linewidth=1, alpha=0.5)

    ax.set_xlim(-0.5, max_turns - 0.5)

    # Dynamic Y-axis
    if y_max is None:
        y_max = max(max(all_drifts) * 1.1, EVENT_HORIZON * 1.2) if all_drifts else 2.0
    ax.set_ylim(-0.05, y_max)

    ax.set_xticks(range(max_turns))
    ax.set_xticklabels([str(i) for i in range(max_turns)], fontsize=7, color=TEXT_COLOR)
    ax.set_xlabel('Turn', color=TEXT_COLOR, fontsize=10)
    ax.set_ylabel('Drift', color=TEXT_COLOR, fontsize=10)
    ax.set_title(title, color=TEXT_COLOR, fontsize=12, fontweight='bold')

    # Event Horizon reference
    ax.axhline(y=EVENT_HORIZON, color=EVENT_HORIZON_COLOR, linestyle='--', alpha=0.7, linewidth=1.5)

    # Legend - only show providers that are actually in the data
    patches = []
    for provider in sorted(providers_seen):
        color = PROVIDER_COLORS.get(provider, '#ffffff')
        patches.append(mpatches.Patch(color=color, label=provider.capitalize()))

    if patches:
        ax.legend(handles=patches, loc='upper right', facecolor=BG_COLOR, edgecolor=AXIS_COLOR,
                  labelcolor=TEXT_COLOR, fontsize=8)

def generate_individual_waveforms(data, output_path):
    """Generate individual waveform plots for selected models."""
    # Run 010 uses 'trajectories_for_3d' key
    trajectories = data.get('trajectories_for_3d', data.get('trajectories', []))

    # Select representative models (one per provider)
    selected = []
    providers_seen = set()
    for traj in trajectories:
        if traj['provider'] not in providers_seen:
            selected.append(traj)
            providers_seen.add(traj['provider'])
            if len(selected) >= 6:
                break

    if not selected:
        print("No trajectories found")
        return

    # Create 2x3 grid
    fig, axes = plt.subplots(2, 3, figsize=(14, 8), facecolor=BG_COLOR)
    fig.suptitle('Run 010: Cognitive Waveforms - Identity Drift Over Conversation',
                 color=TEXT_COLOR, fontsize=14, fontweight='bold')

    for idx, (ax, traj) in enumerate(zip(axes.flat, selected)):
        label = f"{traj['ship']} ({traj['provider']})"
        create_single_trace(ax, traj['drift_sequence'], label)

    # Hide unused axes
    for idx in range(len(selected), 6):
        axes.flat[idx].set_visible(False)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, facecolor=BG_COLOR, edgecolor='none', bbox_inches='tight')
    plt.close()
    print(f"Generated: {output_path}")

def generate_overlay_plot(data, output_path):
    """Generate overlay plot with all traces."""
    trajectories = data.get('trajectories_for_3d', data.get('trajectories', []))

    if not trajectories:
        print("No trajectories found")
        return

    fig, ax = plt.subplots(figsize=(12, 6), facecolor=BG_COLOR)
    create_overlay_traces(ax, trajectories, 'Run 010: All Cognitive Waveforms Overlaid')

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, facecolor=BG_COLOR, edgecolor='none', bbox_inches='tight')
    plt.close()
    print(f"Generated: {output_path}")

def generate_provider_comparison(data, output_path):
    """Generate provider-grouped waveform comparison."""
    trajectories = data.get('trajectories_for_3d', data.get('trajectories', []))

    # Group by provider
    by_provider = {}
    for traj in trajectories:
        prov = traj['provider']
        if prov not in by_provider:
            by_provider[prov] = []
        by_provider[prov].append(traj)

    providers = list(by_provider.keys())
    n_providers = len(providers)

    if n_providers == 0:
        print("No providers found")
        return

    fig, axes = plt.subplots(1, n_providers, figsize=(5 * n_providers, 5), facecolor=BG_COLOR)
    if n_providers == 1:
        axes = [axes]

    # Extract run_id from output_path if available
    run_id = "XXX"
    if output_path:
        match = re.search(r'run(\d+)', str(output_path))
        if match:
            run_id = match.group(1)

    fig.suptitle(f'Run {run_id}: Cognitive Waveforms by Provider',
                 color=TEXT_COLOR, fontsize=14, fontweight='bold')

    # Find global max for consistent y-axis
    all_drift_values = []
    max_turns_global = 0
    for prov in providers:
        for traj in by_provider[prov]:
            drift_seq = traj.get('drift_sequence', traj.get('drifts', []))
            all_drift_values.extend(drift_seq)
            max_turns_global = max(max_turns_global, len(drift_seq))

    y_max = max(max(all_drift_values) * 1.1, EVENT_HORIZON * 1.2) if all_drift_values else 2.0

    for ax, prov in zip(axes, providers):
        create_oscilloscope_grid(ax)
        color = PROVIDER_COLORS.get(prov, '#00ff00')

        for traj in by_provider[prov]:
            drift_seq = traj.get('drift_sequence', traj.get('drifts', []))
            if len(drift_seq) > 1:
                turns = np.arange(len(drift_seq))
                turns_smooth = np.linspace(0, len(drift_seq) - 1, 100)
                drift_smooth = np.interp(turns_smooth, turns, drift_seq)
                ax.plot(turns_smooth, drift_smooth, color=color, linewidth=1, alpha=0.6)

        # Calculate and plot mean waveform (handle variable length sequences)
        all_seqs = [t.get('drift_sequence', t.get('drifts', [])) for t in by_provider[prov]]
        # Pad sequences to same length for mean calculation
        if all_seqs:
            max_len = max(len(s) for s in all_seqs)
            padded_seqs = []
            for s in all_seqs:
                if len(s) < max_len:
                    # Pad with last value
                    padded = list(s) + [s[-1]] * (max_len - len(s))
                    padded_seqs.append(padded)
                else:
                    padded_seqs.append(list(s))
            mean_seq = np.mean(padded_seqs, axis=0)
            turns = np.arange(len(mean_seq))
            turns_smooth = np.linspace(0, len(mean_seq) - 1, 100)
            mean_smooth = np.interp(turns_smooth, turns, mean_seq)
            ax.plot(turns_smooth, mean_smooth, color='white', linewidth=3, alpha=0.9, label='Mean')

        ax.set_xlim(-0.5, max_turns_global - 0.5)
        ax.set_ylim(-0.05, y_max)
        ax.set_xticks(range(max_turns_global))
        ax.set_xticklabels([str(i) for i in range(max_turns_global)], fontsize=7, color=TEXT_COLOR)
        ax.set_xlabel('Turn', color=TEXT_COLOR, fontsize=10)
        ax.set_ylabel('Drift', color=TEXT_COLOR, fontsize=10)
        ax.set_title(f'{prov.upper()} (n={len(by_provider[prov])})',
                     color=color, fontsize=12, fontweight='bold')
        ax.axhline(y=EVENT_HORIZON, color=EVENT_HORIZON_COLOR, linestyle='--', alpha=0.7, linewidth=1.5)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, facecolor=BG_COLOR, edgecolor='none', bbox_inches='tight')
    plt.close()
    print(f"Generated: {output_path}")

def main():
    parser = argparse.ArgumentParser(description='Generate oscilloscope visualizations for any run')
    parser.add_argument('--run', type=str, default='010', help='Run ID (e.g., 010, 018, 009)')
    parser.add_argument('--output-dir', type=str, help='Output directory (default: current script directory)')
    args = parser.parse_args()

    run_id = args.run
    output_dir = Path(args.output_dir) if args.output_dir else OUTPUT_DIR

    print("=" * 60)
    print(f"OSCILLOSCOPE VISUALIZATION - Run {run_id} Cognitive Waveforms")
    print("=" * 60)

    # Load data
    print(f"\nLoading data for run {run_id}...")
    try:
        data, data_source = load_run_data(run_id)
    except FileNotFoundError as e:
        print(f"ERROR: {e}")
        return

    trajectories = data.get('trajectories_for_3d', data.get('trajectories', []))
    n_trajectories = len(trajectories)
    print(f"Found {n_trajectories} trajectories (source: {data_source})")

    if n_trajectories == 0:
        print("No trajectories found. Exiting.")
        return

    # Generate visualizations
    print("\nGenerating visualizations...")

    # 1. Individual waveforms
    generate_individual_waveforms(
        data,
        output_dir / f"run{run_id}_individual_waveforms.png"
    )

    # 2. All traces overlaid
    generate_overlay_plot(
        data,
        output_dir / f"run{run_id}_all_waveforms_overlay.png"
    )

    # 3. Provider comparison
    generate_provider_comparison(
        data,
        output_dir / f"run{run_id}_provider_waveforms.png"
    )

    # Also generate SVG for individual waveforms
    print("\nGenerating SVG version...")

    selected = []
    providers_seen = set()
    for traj in trajectories:
        provider = traj.get('provider', 'unknown')
        if provider not in providers_seen:
            selected.append(traj)
            providers_seen.add(provider)
            if len(selected) >= 6:
                break

    if selected:
        fig, axes = plt.subplots(2, 3, figsize=(14, 8), facecolor=BG_COLOR)
        fig.suptitle(f'Run {run_id}: Cognitive Waveforms - Identity Drift Over Conversation',
                     color=TEXT_COLOR, fontsize=14, fontweight='bold')
        for idx, (ax, traj) in enumerate(zip(axes.flat, selected)):
            drift_seq = traj.get('drift_sequence', traj.get('drifts', []))
            ship = traj.get('ship', traj.get('model', 'unknown'))
            provider = traj.get('provider', 'unknown')
            create_single_trace(ax, drift_seq, f"{ship[:20]} ({provider})")
        for idx in range(len(selected), 6):
            axes.flat[idx].set_visible(False)
        plt.tight_layout()
        plt.savefig(output_dir / f"run{run_id}_individual_waveforms.svg", facecolor=BG_COLOR, edgecolor='none', bbox_inches='tight')
        plt.close()
        print(f"  Generated: run{run_id}_individual_waveforms.svg")

    print("\n" + "=" * 60)
    print("COMPLETE")
    print("=" * 60)
    print(f"\nOutput files:")
    for f in output_dir.glob(f"run{run_id}_*.png"):
        print(f"  - {f.name}")

if __name__ == "__main__":
    main()
