"""
Run 008: 3D Identity Basin Visualization

The "Black Hole" view — showing drift trajectories spiraling toward
or away from the identity attractor in 3D phase space.

X = Drift at turn N
Y = Drift at turn N+1
Z = Turn number (time axis)

This reveals the DRAIN dynamics — water going down (or escaping) the drain.
"""

import json
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
from pathlib import Path
from collections import defaultdict

# Paths
BASE_DIR = Path(__file__).resolve().parent.parent
RESULTS_FILE = BASE_DIR / "armada_results" / "S7_run_008_20251201_020501.json"
OUTPUT_DIR = Path(__file__).resolve().parent / "pics"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# Provider colors
PROVIDER_COLORS = {
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
}

def get_provider(ship_name):
    name = ship_name.lower()
    if "claude" in name:
        return "claude"
    elif "gemini" in name:
        return "gemini"
    elif name.startswith("o1") or name.startswith("o3") or name.startswith("o4"):
        return "gpt"
    elif "gpt" in name:
        return "gpt"
    return "unknown"

def load_data():
    with open(RESULTS_FILE, encoding='utf-8') as f:
        return json.load(f)

def extract_trajectories(data):
    """Extract full drift trajectories for each sequence."""
    trajectories = []

    for ship_name, ship_data in data['results'].items():
        provider = get_provider(ship_name)

        for seq_name, seq_turns in ship_data.get('sequences', {}).items():
            if not isinstance(seq_turns, list):
                continue

            # Get drift values in order
            turns_with_drift = []
            for turn in seq_turns:
                if 'drift_data' in turn and turn['drift_data']:
                    drift = turn['drift_data'].get('drift', 0)
                    turn_num = turn.get('turn', len(turns_with_drift))
                    turns_with_drift.append((turn_num, drift))

            if len(turns_with_drift) >= 3:
                turns_with_drift.sort(key=lambda x: x[0])
                trajectories.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': seq_name,
                    'drifts': [d for _, d in turns_with_drift],
                    'turns': [t for t, _ in turns_with_drift]
                })

    return trajectories

def classify_trajectory(drifts):
    """Classify as STUCK or RECOVERED based on final vs baseline."""
    if len(drifts) < 2:
        return "unknown"
    baseline = drifts[0]
    final = drifts[-1]
    if baseline < 0.01:
        baseline = 0.01
    ratio = final / baseline
    return "STUCK" if ratio > 1.5 else "RECOVERED"

def plot_3d_basin(trajectories):
    """
    Create 3D visualization of identity basin.

    X = Drift at turn N
    Y = Drift at turn N+1
    Z = Turn number

    This shows trajectories through phase space over time.
    """
    fig = plt.figure(figsize=(16, 14))

    # Main 3D plot
    ax = fig.add_subplot(111, projection='3d')

    # Plot each trajectory
    for traj in trajectories:
        drifts = traj['drifts']
        provider = traj['provider']
        color = PROVIDER_COLORS.get(provider, 'gray')
        status = classify_trajectory(drifts)

        # Create phase space coordinates
        # X = drift[n], Y = drift[n+1], Z = turn number
        xs = drifts[:-1]  # Drift at turn N
        ys = drifts[1:]   # Drift at turn N+1
        zs = list(range(len(xs)))  # Turn number

        # Line style based on outcome
        alpha = 0.7 if status == "STUCK" else 0.4
        linewidth = 1.5 if status == "STUCK" else 0.8

        # Plot trajectory line
        ax.plot(xs, ys, zs, color=color, alpha=alpha, linewidth=linewidth)

        # Mark start and end points
        if len(xs) > 0:
            # Start point (green)
            ax.scatter([xs[0]], [ys[0]], [zs[0]], color='green', s=30, alpha=0.8, marker='o')
            # End point (red if STUCK, blue if RECOVERED)
            end_color = 'red' if status == "STUCK" else 'blue'
            ax.scatter([xs[-1]], [ys[-1]], [zs[-1]], color=end_color, s=30, alpha=0.8, marker='s')

    # Add the "no change" plane (where drift[n] = drift[n+1])
    # This is the diagonal in 2D, becomes a plane in 3D
    plane_range = np.linspace(0, 4, 20)
    X_plane, Z_plane = np.meshgrid(plane_range, range(10))
    Y_plane = X_plane  # y = x (no change)
    ax.plot_surface(X_plane, Y_plane, Z_plane, alpha=0.1, color='gray')

    # Labels and title
    ax.set_xlabel('Drift at Turn N', fontsize=12, labelpad=10)
    ax.set_ylabel('Drift at Turn N+1', fontsize=12, labelpad=10)
    ax.set_zlabel('Turn Number (Time)', fontsize=12, labelpad=10)

    ax.set_title('IDENTITY BASIN: 3D Phase Space Trajectories\n"The Black Hole View"',
                fontsize=16, fontweight='bold', pad=20)

    # Add legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='#7c3aed', linewidth=2, label='Claude'),
        Line2D([0], [0], color='#10a37f', linewidth=2, label='GPT'),
        Line2D([0], [0], color='#4285f4', linewidth=2, label='Gemini'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='green', markersize=10, label='Start'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='red', markersize=10, label='End (STUCK)'),
        Line2D([0], [0], marker='s', color='w', markerfacecolor='blue', markersize=10, label='End (RECOVERED)'),
    ]
    ax.legend(handles=legend_elements, loc='upper left', fontsize=10)

    # Add annotation
    ax.text2D(0.02, 0.02,
             "Gray plane = No Change (identity stable)\n"
             "Below plane = Recovering\n"
             "Above plane = Drifting more\n"
             "Spiraling IN = Toward attractor\n"
             "Spiraling OUT = Escaping basin",
             transform=ax.transAxes, fontsize=9, verticalalignment='bottom',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    # Set viewing angle for best drain visualization
    ax.view_init(elev=20, azim=45)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_identity_basin_3d.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_identity_basin_3d.png")
    plt.close()

def plot_drain_spiral(trajectories):
    """
    Create the quintessential "drain" view — looking DOWN into the basin.

    This is the top-down view where you can see the spiral.
    """
    fig, axes = plt.subplots(1, 2, figsize=(16, 8))

    # LEFT: Top-down view (X-Y plane, looking down Z axis)
    ax1 = axes[0]

    for traj in trajectories:
        drifts = traj['drifts']
        provider = traj['provider']
        color = PROVIDER_COLORS.get(provider, 'gray')
        status = classify_trajectory(drifts)

        xs = drifts[:-1]
        ys = drifts[1:]

        alpha = 0.6 if status == "STUCK" else 0.3

        # Plot with arrows to show direction
        for i in range(len(xs) - 1):
            ax1.annotate('', xy=(xs[i+1], ys[i+1]), xytext=(xs[i], ys[i]),
                        arrowprops=dict(arrowstyle='->', color=color, alpha=alpha, lw=0.5))

        # Mark endpoints
        if len(xs) > 0:
            ax1.scatter(xs[0], ys[0], color='green', s=20, alpha=0.6, zorder=5)
            end_color = 'red' if status == "STUCK" else 'blue'
            ax1.scatter(xs[-1], ys[-1], color=end_color, s=20, alpha=0.6, zorder=5, marker='s')

    # Diagonal line
    ax1.plot([0, 4], [0, 4], 'k--', alpha=0.3, label='No change')

    # Basin zones
    ax1.fill_between([0, 4], [0, 4], [4, 4], alpha=0.1, color='red', label='Drifting zone')
    ax1.fill_between([0, 4], [0, 0], [0, 4], alpha=0.1, color='green', label='Recovery zone')

    ax1.set_xlabel('Drift at Turn N', fontsize=12)
    ax1.set_ylabel('Drift at Turn N+1', fontsize=12)
    ax1.set_title('TOP-DOWN VIEW: Looking Into the Drain\n(Arrows show direction of flow)',
                 fontsize=14, fontweight='bold')
    ax1.set_xlim(0, 4)
    ax1.set_ylim(0, 4)
    ax1.set_aspect('equal')
    ax1.legend(loc='upper left', fontsize=9)
    ax1.grid(True, alpha=0.3)

    # RIGHT: Cumulative drift over time (shows the "pull" of the attractor)
    ax2 = axes[1]

    for traj in trajectories:
        drifts = traj['drifts']
        provider = traj['provider']
        color = PROVIDER_COLORS.get(provider, 'gray')
        status = classify_trajectory(drifts)

        # Cumulative drift (integral)
        cumulative = np.cumsum(drifts)
        turns = range(len(cumulative))

        alpha = 0.6 if status == "STUCK" else 0.3
        linestyle = '-' if status == "STUCK" else '--'

        ax2.plot(turns, cumulative, color=color, alpha=alpha, linewidth=1, linestyle=linestyle)

    ax2.set_xlabel('Turn Number', fontsize=12)
    ax2.set_ylabel('Cumulative Drift (Integral)', fontsize=12)
    ax2.set_title('ACCUMULATED DRIFT: How Deep Into the Well?\n(Solid = STUCK, Dashed = RECOVERED)',
                 fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)

    # Add legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='#7c3aed', linewidth=2, label='Claude'),
        Line2D([0], [0], color='#10a37f', linewidth=2, label='GPT'),
        Line2D([0], [0], color='#4285f4', linewidth=2, label='Gemini'),
    ]
    ax2.legend(handles=legend_elements, loc='upper left', fontsize=10)

    fig.suptitle('IDENTITY ATTRACTOR BASIN — The Drain Dynamics', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_drain_spiral.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_drain_spiral.png")
    plt.close()

def plot_event_horizon(trajectories):
    """
    The "Event Horizon" visualization — at what baseline drift level
    do you become unable to escape?

    This is the PREDICTIVE power of the model.
    """
    fig, ax = plt.subplots(figsize=(12, 8))

    # Collect baseline vs outcome
    baselines_stuck = []
    baselines_recovered = []

    for traj in trajectories:
        drifts = traj['drifts']
        if len(drifts) < 2:
            continue

        baseline = drifts[0]
        status = classify_trajectory(drifts)

        if status == "STUCK":
            baselines_stuck.append(baseline)
        else:
            baselines_recovered.append(baseline)

    # Create histogram
    bins = np.linspace(0, 3, 20)

    ax.hist(baselines_recovered, bins=bins, alpha=0.7, color='blue',
           label=f'RECOVERED (n={len(baselines_recovered)})', edgecolor='white')
    ax.hist(baselines_stuck, bins=bins, alpha=0.7, color='red',
           label=f'STUCK (n={len(baselines_stuck)})', edgecolor='white')

    # Calculate "event horizon" — the crossover point
    if baselines_stuck and baselines_recovered:
        avg_stuck = np.mean(baselines_stuck)
        avg_recovered = np.mean(baselines_recovered)
        horizon = (avg_stuck + avg_recovered) / 2

        ax.axvline(x=horizon, color='black', linestyle='--', linewidth=2,
                  label=f'Event Horizon (~{horizon:.2f})')

        # Shade the danger zone
        ax.axvspan(0, horizon, alpha=0.1, color='red')
        ax.axvspan(horizon, 3, alpha=0.1, color='green')

    ax.set_xlabel('Baseline Drift (First Turn)', fontsize=12)
    ax.set_ylabel('Count', fontsize=12)
    ax.set_title('THE EVENT HORIZON: Where Recovery Becomes Unlikely\n'
                '(Below the horizon = danger zone)', fontsize=14, fontweight='bold')
    ax.legend(loc='upper right', fontsize=11)
    ax.grid(True, alpha=0.3, axis='y')

    # Add interpretation
    ax.text(0.02, 0.98,
           f"Average baseline (STUCK): {np.mean(baselines_stuck):.2f}\n"
           f"Average baseline (RECOVERED): {np.mean(baselines_recovered):.2f}\n\n"
           f"Interpretation:\n"
           f"Models that START with weak identity (low baseline)\n"
           f"are more likely to get STUCK when perturbed.",
           transform=ax.transAxes, fontsize=10, verticalalignment='top',
           bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_event_horizon.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_event_horizon.png")
    plt.close()

# =============================================================================
# MAIN
# =============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("RUN 008: 3D IDENTITY BASIN VISUALIZATION")
    print("The Black Hole View")
    print("=" * 60)

    print("\nLoading data...")
    data = load_data()

    print("Extracting trajectories...")
    trajectories = extract_trajectories(data)
    print(f"  Found {len(trajectories)} trajectories")

    # Classify
    stuck = sum(1 for t in trajectories if classify_trajectory(t['drifts']) == "STUCK")
    recovered = len(trajectories) - stuck
    print(f"  STUCK: {stuck}, RECOVERED: {recovered}")

    print("\nGenerating visualizations...")
    print("-" * 40)

    plot_3d_basin(trajectories)
    plot_drain_spiral(trajectories)
    plot_event_horizon(trajectories)

    print("-" * 40)
    print(f"\nAll visualizations saved to: {OUTPUT_DIR}")
    print("=" * 60)
