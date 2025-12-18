"""
Oscilloscope Visualization for Run 010: Cognitive Waveform Display

Run 010 was designed as the "oscilloscope of cognition" - capturing identity
drift over a 7-turn conversation as a time-series waveform. This visualization
renders drift sequences as analog-style oscilloscope traces.

Style: Green phosphor on black background, gridlines, retro CRT aesthetic.
"""

import json
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from pathlib import Path

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent.parent.parent
DATA_FILE = ARMADA_DIR / "0_results" / "runs" / "legacy_runs" / "S7_run_010_recursive_20251203_012400.json"
OUTPUT_DIR = SCRIPT_DIR

# Colors - Oscilloscope aesthetic
BG_COLOR = '#000000'  # Black background
GRID_COLOR = '#1a3a1a'  # Dark green grid
TRACE_COLOR = '#00ff00'  # Bright green phosphor
TRACE_COLOR_2 = '#00cc00'  # Slightly dimmer green
AXIS_COLOR = '#00aa00'  # Medium green for axes
TEXT_COLOR = '#00ff00'  # Green text
EVENT_HORIZON_COLOR = '#ff4444'  # Red for Event Horizon reference

# Turn labels
TURN_LABELS = ['baseline', 'intro', 'push', 'persona', 'strip', 'return', 'meta']

def load_run_010_data():
    """Load Run 010 data from JSON file."""
    with open(DATA_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)
    return data

def create_oscilloscope_grid(ax):
    """Create oscilloscope-style grid on axes."""
    ax.set_facecolor(BG_COLOR)
    ax.grid(True, color=GRID_COLOR, linewidth=0.5, alpha=0.7)
    ax.spines['bottom'].set_color(AXIS_COLOR)
    ax.spines['top'].set_color(AXIS_COLOR)
    ax.spines['left'].set_color(AXIS_COLOR)
    ax.spines['right'].set_color(AXIS_COLOR)
    ax.tick_params(colors=AXIS_COLOR, which='both')

def create_single_trace(ax, drift_sequence, label):
    """Create a single oscilloscope trace."""
    turns = np.arange(len(drift_sequence))

    # Interpolate for smoother curve
    turns_smooth = np.linspace(0, len(drift_sequence) - 1, 100)
    drift_smooth = np.interp(turns_smooth, turns, drift_sequence)

    # Plot the trace with glow effect
    ax.plot(turns_smooth, drift_smooth, color=TRACE_COLOR, linewidth=2, alpha=0.8)
    ax.plot(turns_smooth, drift_smooth, color=TRACE_COLOR, linewidth=4, alpha=0.3)  # Glow

    # Add dots at actual data points
    ax.scatter(turns, drift_sequence, color=TRACE_COLOR, s=30, zorder=5)

    create_oscilloscope_grid(ax)
    ax.set_xlim(-0.5, 6.5)
    ax.set_ylim(-0.05, 1.1)
    ax.set_xticks(range(7))
    ax.set_xticklabels(TURN_LABELS, fontsize=8, color=TEXT_COLOR, rotation=45, ha='right')
    ax.set_ylabel('Drift', color=TEXT_COLOR, fontsize=10)
    ax.set_title(label, color=TEXT_COLOR, fontsize=10, fontweight='bold')

    # Add horizontal reference line at Event Horizon (normalized: 1.23/1.23 = 1.0)
    # But Run 010 uses 0-1 scale, so EH would be at 1.0
    ax.axhline(y=1.0, color=EVENT_HORIZON_COLOR, linestyle='--', alpha=0.5, linewidth=1)

def create_overlay_traces(ax, trajectories, title):
    """Create multiple overlaid traces for comparison."""
    create_oscilloscope_grid(ax)

    # Group by provider
    provider_colors = {
        'claude': '#00ff00',  # Green
        'gpt': '#00ccff',     # Cyan
        'gemini': '#ffcc00',  # Yellow
    }

    for traj in trajectories:
        color = provider_colors.get(traj['provider'], '#00ff00')
        drift_seq = traj['drift_sequence']
        turns = np.arange(len(drift_seq))

        # Interpolate for smoother curve
        turns_smooth = np.linspace(0, len(drift_seq) - 1, 100)
        drift_smooth = np.interp(turns_smooth, turns, drift_seq)

        ax.plot(turns_smooth, drift_smooth, color=color, linewidth=1, alpha=0.5)

    ax.set_xlim(-0.5, 6.5)
    ax.set_ylim(-0.05, 1.1)
    ax.set_xticks(range(7))
    ax.set_xticklabels(TURN_LABELS, fontsize=8, color=TEXT_COLOR, rotation=45, ha='right')
    ax.set_xlabel('Turn', color=TEXT_COLOR, fontsize=10)
    ax.set_ylabel('Drift', color=TEXT_COLOR, fontsize=10)
    ax.set_title(title, color=TEXT_COLOR, fontsize=12, fontweight='bold')

    # Event Horizon reference
    ax.axhline(y=1.0, color=EVENT_HORIZON_COLOR, linestyle='--', alpha=0.5, linewidth=1)

    # Legend
    patches = [
        mpatches.Patch(color='#00ff00', label='Claude'),
        mpatches.Patch(color='#00ccff', label='GPT'),
        mpatches.Patch(color='#ffcc00', label='Gemini'),
    ]
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

    fig.suptitle('Run 010: Cognitive Waveforms by Provider',
                 color=TEXT_COLOR, fontsize=14, fontweight='bold')

    provider_colors = {
        'claude': '#00ff00',
        'gpt': '#00ccff',
        'gemini': '#ffcc00',
    }

    for ax, prov in zip(axes, providers):
        create_oscilloscope_grid(ax)
        color = provider_colors.get(prov, '#00ff00')

        for traj in by_provider[prov]:
            drift_seq = traj['drift_sequence']
            turns = np.arange(len(drift_seq))
            turns_smooth = np.linspace(0, len(drift_seq) - 1, 100)
            drift_smooth = np.interp(turns_smooth, turns, drift_seq)
            ax.plot(turns_smooth, drift_smooth, color=color, linewidth=1, alpha=0.6)

        # Calculate and plot mean waveform
        all_seqs = [t['drift_sequence'] for t in by_provider[prov]]
        if all_seqs:
            mean_seq = np.mean(all_seqs, axis=0)
            turns = np.arange(len(mean_seq))
            turns_smooth = np.linspace(0, len(mean_seq) - 1, 100)
            mean_smooth = np.interp(turns_smooth, turns, mean_seq)
            ax.plot(turns_smooth, mean_smooth, color='white', linewidth=3, alpha=0.9, label='Mean')

        ax.set_xlim(-0.5, 6.5)
        ax.set_ylim(-0.05, 1.1)
        ax.set_xticks(range(7))
        ax.set_xticklabels(TURN_LABELS, fontsize=8, color=TEXT_COLOR, rotation=45, ha='right')
        ax.set_xlabel('Turn', color=TEXT_COLOR, fontsize=10)
        ax.set_ylabel('Drift', color=TEXT_COLOR, fontsize=10)
        ax.set_title(f'{prov.upper()} (n={len(by_provider[prov])})',
                     color=color, fontsize=12, fontweight='bold')
        ax.axhline(y=1.0, color=EVENT_HORIZON_COLOR, linestyle='--', alpha=0.5, linewidth=1)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, facecolor=BG_COLOR, edgecolor='none', bbox_inches='tight')
    plt.close()
    print(f"Generated: {output_path}")

def main():
    print("=" * 60)
    print("OSCILLOSCOPE VISUALIZATION - Run 010 Cognitive Waveforms")
    print("=" * 60)

    # Load data
    print(f"\nLoading data from: {DATA_FILE}")
    data = load_run_010_data()

    n_trajectories = len(data.get('trajectories', []))
    print(f"Found {n_trajectories} trajectories")

    # Generate visualizations
    print("\nGenerating visualizations...")

    # 1. Individual waveforms
    generate_individual_waveforms(
        data,
        OUTPUT_DIR / "run010_individual_waveforms.png"
    )

    # 2. All traces overlaid
    generate_overlay_plot(
        data,
        OUTPUT_DIR / "run010_all_waveforms_overlay.png"
    )

    # 3. Provider comparison
    generate_provider_comparison(
        data,
        OUTPUT_DIR / "run010_provider_waveforms.png"
    )

    # Also generate SVG versions
    print("\nGenerating SVG versions...")

    # Reload and regenerate as SVG
    data = load_run_010_data()

    # Individual
    trajectories = data.get('trajectories_for_3d', data.get('trajectories', []))
    selected = []
    providers_seen = set()
    for traj in trajectories:
        if traj['provider'] not in providers_seen:
            selected.append(traj)
            providers_seen.add(traj['provider'])
            if len(selected) >= 6:
                break

    if selected:
        fig, axes = plt.subplots(2, 3, figsize=(14, 8), facecolor=BG_COLOR)
        fig.suptitle('Run 010: Cognitive Waveforms - Identity Drift Over Conversation',
                     color=TEXT_COLOR, fontsize=14, fontweight='bold')
        for idx, (ax, traj) in enumerate(zip(axes.flat, selected)):
            create_single_trace(ax, traj['drift_sequence'], f"{traj['ship']} ({traj['provider']})")
        for idx in range(len(selected), 6):
            axes.flat[idx].set_visible(False)
        plt.tight_layout()
        plt.savefig(OUTPUT_DIR / "run010_individual_waveforms.svg", facecolor=BG_COLOR, edgecolor='none', bbox_inches='tight')
        plt.close()

    print("\n" + "=" * 60)
    print("COMPLETE")
    print("=" * 60)
    print(f"\nOutput files:")
    for f in OUTPUT_DIR.glob("run010_*.png"):
        print(f"  - {f.name}")

if __name__ == "__main__":
    main()
