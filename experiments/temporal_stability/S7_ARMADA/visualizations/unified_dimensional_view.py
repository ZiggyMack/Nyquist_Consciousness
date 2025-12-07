"""
Unified Dimensional Visualization for S7 ARMADA

Shows ALL dimensions in a single coherent view:
- 5D Drift Dimensions (A_pole, B_zero, C_meta, D_identity, E_hedging)
- Nyquist Pillars (Voice, Values, Reasoning, Self-Model, Narrative)
- Sub-dimensions from Phase 2c probes
- Collapsed drift scalar for reference

Design Philosophy: "One way to show them all without dividing everything up"
- Parallel coordinates plot showing all dimensions simultaneously
- Color-coded by probe phase to show progression
- Radar/spider overlay for dimensional signature comparison
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from matplotlib.lines import Line2D
import matplotlib.gridspec as gridspec
from pathlib import Path
from datetime import datetime
import sys

# Dimension definitions
DRIFT_DIMENSIONS = ['A_pole', 'B_zero', 'C_meta', 'D_identity', 'E_hedging']
DRIFT_WEIGHTS = {'A_pole': 0.30, 'B_zero': 0.15, 'C_meta': 0.20, 'D_identity': 0.25, 'E_hedging': 0.10}
DRIFT_LABELS = {
    'A_pole': 'A: Pole\n(30%)',
    'B_zero': 'B: Zero\n(15%)',
    'C_meta': 'C: Meta\n(20%)',
    'D_identity': 'D: Identity\n(25%)',
    'E_hedging': 'E: Hedging\n(10%)'
}

NYQUIST_PILLARS = ['Voice', 'Values', 'Reasoning', 'Self-Model', 'Narrative']

PHASE_COLORS = {
    'baseline': '#4CAF50',      # Green
    'identity': '#2196F3',      # Blue
    'boundary': '#FF9800',      # Orange
    'stress': '#F44336',        # Red
    'recovery': '#9C27B0',      # Purple
    'phase_2c': '#00BCD4'       # Cyan
}

def load_run_data(json_path: str) -> dict:
    """Load run data from JSON file."""
    with open(json_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def extract_dimensional_data(ship_result: dict) -> dict:
    """Extract all dimensional data from a ship result."""
    data = {
        'turns': [],
        'phases': [],
        'drift_dimensions': [],  # List of dicts with A-E values
        'collapsed_drift': [],
        'adversarial_drift': [],
        'probe_ids': [],
        'pillar_scores': {}  # phase_2c pillar-specific scores
    }

    # Extract turn-by-turn data
    for turn in ship_result.get('turns', []):
        data['turns'].append(turn['turn'])
        data['phases'].append(turn.get('phase', 'unknown'))
        data['collapsed_drift'].append(turn.get('drift', 0))
        data['adversarial_drift'].append(turn.get('adversarial_drift', 0))
        data['probe_ids'].append(turn.get('probe_id', ''))

        # Extract individual dimension values
        dims = turn.get('drift_dimensions', {})
        data['drift_dimensions'].append({
            'A_pole': dims.get('A_pole', 0),
            'B_zero': dims.get('B_zero', 0),
            'C_meta': dims.get('C_meta', 0),
            'D_identity': dims.get('D_identity', 0),
            'E_hedging': dims.get('E_hedging', 0)
        })

    # Extract Phase 2c results
    for p2c in ship_result.get('phase_2c_results', []):
        pillar = p2c.get('pillar', 'unknown')
        probe_id = p2c.get('probe_id', 'unknown')
        data['pillar_scores'][probe_id] = {
            'pillar': pillar,
            'main_drift': p2c.get('main_drift', 0),
            'adversarial_drift': p2c.get('adversarial_drift', 0)
        }

    return data


def create_unified_visualization(ship_result: dict, output_dir: Path, ship_name: str = None):
    """
    Create unified visualization showing ALL dimensions in one view.

    Layout:
    - Top: Parallel coordinates showing all 5D dimensions over time
    - Middle: Stacked area showing dimensional contributions
    - Bottom-left: Radar chart showing signature per phase
    - Bottom-right: Phase 2c pillar scores
    """
    data = extract_dimensional_data(ship_result)
    ship_name = ship_name or ship_result.get('ship', 'Unknown')

    fig = plt.figure(figsize=(20, 16))
    fig.suptitle(f'Unified Dimensional View: {ship_name}', fontsize=16, fontweight='bold', y=0.98)

    # Create grid
    gs = gridspec.GridSpec(3, 2, height_ratios=[1.2, 1.2, 1], hspace=0.3, wspace=0.25)

    # === TOP: Multi-line plot showing all 5 dimensions over turns ===
    ax1 = fig.add_subplot(gs[0, :])
    _plot_dimensional_trajectories(ax1, data)

    # === MIDDLE: Stacked area showing dimensional contributions ===
    ax2 = fig.add_subplot(gs[1, :])
    _plot_dimensional_stack(ax2, data)

    # === BOTTOM LEFT: Radar chart showing dimensional signature by phase ===
    ax3 = fig.add_subplot(gs[2, 0], projection='polar')
    _plot_phase_radar(ax3, data)

    # === BOTTOM RIGHT: Phase 2c pillar scores ===
    ax4 = fig.add_subplot(gs[2, 1])
    _plot_pillar_scores(ax4, data)

    plt.tight_layout(rect=[0, 0, 1, 0.96])

    # Save
    output_file = output_dir / f'{ship_name.replace(" ", "_").replace(".", "")}_unified_dimensional.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight', facecolor='white')
    plt.close()

    return output_file


def _plot_dimensional_trajectories(ax, data):
    """Plot all 5D dimensions as separate lines over time."""
    turns = data['turns']

    dim_colors = {
        'A_pole': '#E53935',      # Red
        'B_zero': '#1E88E5',      # Blue
        'C_meta': '#43A047',      # Green
        'D_identity': '#FB8C00',  # Orange
        'E_hedging': '#8E24AA'    # Purple
    }

    for dim in DRIFT_DIMENSIONS:
        values = [d[dim] for d in data['drift_dimensions']]
        weight = DRIFT_WEIGHTS[dim] * 100
        label = f'{dim} ({weight:.0f}%)'
        ax.plot(turns, values, 'o-', color=dim_colors[dim], linewidth=2,
                markersize=6, label=label, alpha=0.8)

    # Add collapsed drift as dashed line
    ax.plot(turns, data['collapsed_drift'], 'k--', linewidth=2.5,
            label='Collapsed Drift', alpha=0.6)

    # Add phase backgrounds
    _add_phase_backgrounds(ax, data)

    ax.set_xlabel('Turn', fontsize=11)
    ax.set_ylabel('Dimension Value', fontsize=11)
    ax.set_title('5D Drift Dimensions Over Conversation', fontsize=12, fontweight='bold')
    ax.legend(loc='upper right', fontsize=9, ncol=2)
    ax.grid(True, alpha=0.3)
    ax.set_xlim(min(turns) - 0.5, max(turns) + 0.5)


def _plot_dimensional_stack(ax, data):
    """Plot stacked area showing dimensional contributions."""
    turns = np.array(data['turns'])

    # Create weighted stacks
    weighted_values = {}
    for dim in DRIFT_DIMENSIONS:
        weighted_values[dim] = np.array([d[dim] * DRIFT_WEIGHTS[dim] for d in data['drift_dimensions']])

    dim_colors = ['#E53935', '#1E88E5', '#43A047', '#FB8C00', '#8E24AA']

    # Stack from bottom to top
    bottoms = np.zeros(len(turns))
    for i, dim in enumerate(DRIFT_DIMENSIONS):
        ax.fill_between(turns, bottoms, bottoms + weighted_values[dim],
                       color=dim_colors[i], alpha=0.7, label=DRIFT_LABELS[dim].split('\n')[0])
        bottoms += weighted_values[dim]

    # Add total line
    ax.plot(turns, data['collapsed_drift'], 'k-', linewidth=2.5, label='Total Drift')

    # Mark phase transitions
    phase_changes = []
    current_phase = data['phases'][0]
    for i, phase in enumerate(data['phases']):
        if phase != current_phase:
            phase_changes.append((i + 1, phase))  # Turn is 1-indexed
            current_phase = phase

    for turn_idx, phase in phase_changes:
        ax.axvline(x=turn_idx, color='gray', linestyle='--', alpha=0.5)

    ax.set_xlabel('Turn', fontsize=11)
    ax.set_ylabel('Weighted Contribution', fontsize=11)
    ax.set_title('Dimensional Contribution Stack (Weighted)', fontsize=12, fontweight='bold')
    ax.legend(loc='upper right', fontsize=9, ncol=3)
    ax.grid(True, alpha=0.3, axis='y')
    ax.set_xlim(min(turns) - 0.5, max(turns) + 0.5)


def _plot_phase_radar(ax, data):
    """Plot radar chart showing average dimensional signature per phase."""
    # Calculate average values per phase
    phase_averages = {}
    for phase in set(data['phases']):
        indices = [i for i, p in enumerate(data['phases']) if p == phase]
        if indices:
            phase_averages[phase] = {}
            for dim in DRIFT_DIMENSIONS:
                values = [data['drift_dimensions'][i][dim] for i in indices]
                phase_averages[phase][dim] = np.mean(values)

    # Set up radar chart
    angles = np.linspace(0, 2 * np.pi, len(DRIFT_DIMENSIONS), endpoint=False).tolist()
    angles += angles[:1]  # Close the polygon

    ax.set_theta_offset(np.pi / 2)
    ax.set_theta_direction(-1)

    # Plot each phase
    for phase, avg_values in phase_averages.items():
        values = [avg_values[dim] for dim in DRIFT_DIMENSIONS]
        values += values[:1]  # Close the polygon
        color = PHASE_COLORS.get(phase, '#999999')
        ax.plot(angles, values, 'o-', linewidth=2, color=color, label=phase.title(), markersize=5)
        ax.fill(angles, values, alpha=0.15, color=color)

    # Set labels
    ax.set_xticks(angles[:-1])
    dim_short = ['A', 'B', 'C', 'D', 'E']
    ax.set_xticklabels(dim_short, fontsize=10)
    ax.set_title('Phase Signature\n(Avg per Dimension)', fontsize=11, fontweight='bold', pad=15)
    ax.legend(loc='upper right', bbox_to_anchor=(1.35, 1.0), fontsize=8)


def _plot_pillar_scores(ax, data):
    """Plot Phase 2c pillar scores."""
    pillar_data = data.get('pillar_scores', {})

    if not pillar_data:
        ax.text(0.5, 0.5, 'No Phase 2c Data', ha='center', va='center',
                fontsize=14, color='gray', transform=ax.transAxes)
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.axis('off')
        return

    # Prepare data
    probe_ids = list(pillar_data.keys())
    main_drifts = [pillar_data[p]['main_drift'] for p in probe_ids]
    adv_drifts = [pillar_data[p]['adversarial_drift'] for p in probe_ids]

    x = np.arange(len(probe_ids))
    width = 0.35

    bars1 = ax.bar(x - width/2, main_drifts, width, label='Main Response', color='#2196F3', alpha=0.8)
    bars2 = ax.bar(x + width/2, adv_drifts, width, label='Adversarial', color='#FF5722', alpha=0.8)

    ax.set_ylabel('Drift Value', fontsize=11)
    ax.set_title('Phase 2c: Sub-Dimension Probes', fontsize=12, fontweight='bold')
    ax.set_xticks(x)

    # Clean up probe names for display
    labels = [p.replace('selfmodel_', 'SM: ').replace('_', ' ').title() for p in probe_ids]
    ax.set_xticklabels(labels, rotation=20, ha='right', fontsize=9)
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3, axis='y')

    # Add value labels on bars
    for bar in bars1:
        height = bar.get_height()
        ax.annotate(f'{height:.2f}', xy=(bar.get_x() + bar.get_width()/2, height),
                   xytext=(0, 3), textcoords='offset points', ha='center', fontsize=8)
    for bar in bars2:
        height = bar.get_height()
        ax.annotate(f'{height:.2f}', xy=(bar.get_x() + bar.get_width()/2, height),
                   xytext=(0, 3), textcoords='offset points', ha='center', fontsize=8)


def _add_phase_backgrounds(ax, data):
    """Add colored backgrounds for different phases."""
    ylim = ax.get_ylim()
    if ylim[0] == ylim[1]:
        ylim = (0, 6)

    # Find phase boundaries
    phase_regions = []
    current_phase = data['phases'][0]
    start_turn = data['turns'][0]

    for i, (turn, phase) in enumerate(zip(data['turns'], data['phases'])):
        if phase != current_phase:
            phase_regions.append((start_turn, turn - 0.5, current_phase))
            current_phase = phase
            start_turn = turn - 0.5

    # Add final region
    phase_regions.append((start_turn, data['turns'][-1] + 0.5, current_phase))

    for start, end, phase in phase_regions:
        color = PHASE_COLORS.get(phase, '#EEEEEE')
        ax.axvspan(start - 0.5, end, alpha=0.1, color=color)


def create_fleet_comparison(run_data: dict, output_dir: Path):
    """
    Create fleet-wide comparison showing dimensional signatures across all ships.
    """
    ships = run_data.get('results', [])
    if not ships:
        return None

    n_ships = len(ships)
    fig, axes = plt.subplots(n_ships, 1, figsize=(18, 4 * n_ships))

    if n_ships == 1:
        axes = [axes]

    fig.suptitle('Fleet Dimensional Comparison', fontsize=16, fontweight='bold', y=1.02)

    dim_colors = {
        'A_pole': '#E53935',
        'B_zero': '#1E88E5',
        'C_meta': '#43A047',
        'D_identity': '#FB8C00',
        'E_hedging': '#8E24AA'
    }

    for ax, ship in zip(axes, ships):
        data = extract_dimensional_data(ship)
        turns = data['turns']
        ship_name = ship.get('ship', 'Unknown')
        status = ship.get('hysteresis', 'UNKNOWN')

        for dim in DRIFT_DIMENSIONS:
            values = [d[dim] for d in data['drift_dimensions']]
            ax.plot(turns, values, '-', color=dim_colors[dim], linewidth=1.5, alpha=0.7)

        # Status indicator
        status_color = '#4CAF50' if status == 'RECOVERED' else '#F44336'
        ax.plot([], [], color=status_color, linewidth=3, label=f'Status: {status}')

        ax.set_ylabel('Dim Value', fontsize=10)
        ax.set_title(f'{ship_name}', fontsize=11, fontweight='bold', loc='left')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper right', fontsize=8)

    axes[-1].set_xlabel('Turn', fontsize=11)

    # Add dimension legend to first subplot
    legend_elements = [Line2D([0], [0], color=dim_colors[d], linewidth=2, label=d)
                      for d in DRIFT_DIMENSIONS]
    axes[0].legend(handles=legend_elements, loc='upper left', fontsize=9, ncol=5,
                  bbox_to_anchor=(0, 1.15))

    plt.tight_layout()

    output_file = output_dir / 'fleet_dimensional_comparison.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight', facecolor='white')
    plt.close()

    return output_file


def create_dimensional_heatmap(run_data: dict, output_dir: Path):
    """
    Create heatmap showing all dimensions for all ships - the TRUE unified view.

    X-axis: Turns (1-18)
    Y-axis: Ships grouped by dimension
    Color: Dimension value intensity
    """
    ships = run_data.get('results', [])
    if not ships:
        return None

    # Find max turns across all ships
    max_turns = max(len(ship.get('turns', [])) for ship in ships)
    n_ships = len(ships)

    fig, axes = plt.subplots(5, 1, figsize=(16, 14), sharex=True)
    fig.suptitle('Unified Dimensional Heatmap: All Ships x All Dimensions',
                fontsize=14, fontweight='bold', y=0.98)

    dim_cmaps = {
        'A_pole': 'Reds',
        'B_zero': 'Blues',
        'C_meta': 'Greens',
        'D_identity': 'Oranges',
        'E_hedging': 'Purples'
    }

    ship_names = [s.get('ship', f'Ship {i}')[:15] for i, s in enumerate(ships)]

    for ax_idx, dim in enumerate(DRIFT_DIMENSIONS):
        ax = axes[ax_idx]

        # Build matrix: ships x turns
        matrix = np.zeros((n_ships, max_turns))
        matrix[:] = np.nan  # Use NaN for missing data

        for ship_idx, ship in enumerate(ships):
            data = extract_dimensional_data(ship)
            for turn_idx, dim_values in enumerate(data['drift_dimensions']):
                if turn_idx < max_turns:
                    matrix[ship_idx, turn_idx] = dim_values[dim]

        im = ax.imshow(matrix, aspect='auto', cmap=dim_cmaps[dim],
                      vmin=0, vmax=6, interpolation='nearest')

        ax.set_ylabel(f'{dim}\n({int(DRIFT_WEIGHTS[dim]*100)}%)', fontsize=10)
        ax.set_yticks(range(n_ships))
        ax.set_yticklabels(ship_names, fontsize=8)

        # Add colorbar
        cbar = plt.colorbar(im, ax=ax, pad=0.02)
        cbar.ax.tick_params(labelsize=8)

    axes[-1].set_xlabel('Turn', fontsize=11)
    axes[-1].set_xticks(range(max_turns))
    axes[-1].set_xticklabels(range(1, max_turns + 1))

    plt.tight_layout(rect=[0, 0, 1, 0.96])

    output_file = output_dir / 'unified_dimensional_heatmap.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight', facecolor='white')
    plt.close()

    return output_file


def main():
    """Main entry point."""
    # Find most recent run
    armada_dir = Path(__file__).parent.parent / 'armada_results'
    output_dir = Path(__file__).parent / 'pics' / '9_unified_dimensional'
    output_dir.mkdir(parents=True, exist_ok=True)

    # Get run file from command line or find latest
    if len(sys.argv) > 1:
        json_path = Path(sys.argv[1])
    else:
        json_files = list(armada_dir.glob('S7_run_012*.json'))
        if not json_files:
            json_files = list(armada_dir.glob('S7_run_*.json'))
        if not json_files:
            print("No run data found!")
            return
        json_path = max(json_files, key=lambda p: p.stat().st_mtime)

    print(f"Loading: {json_path}")
    run_data = load_run_data(json_path)

    # Generate visualizations
    print("\n1. Creating unified dimensional heatmap (ALL ships x ALL dimensions)...")
    heatmap = create_dimensional_heatmap(run_data, output_dir)
    if heatmap:
        print(f"   Saved: {heatmap}")

    print("\n2. Creating fleet comparison...")
    fleet_viz = create_fleet_comparison(run_data, output_dir)
    if fleet_viz:
        print(f"   Saved: {fleet_viz}")

    print("\n3. Creating individual ship visualizations...")
    for ship in run_data.get('results', []):
        ship_name = ship.get('ship', 'Unknown')
        try:
            viz = create_unified_visualization(ship, output_dir, ship_name)
            print(f"   {ship_name}: {viz}")
        except Exception as e:
            print(f"   {ship_name}: ERROR - {e}")

    print(f"\n=== Unified Dimensional Visualizations Complete ===")
    print(f"Output directory: {output_dir}")


if __name__ == '__main__':
    main()
