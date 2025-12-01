"""
Run 009: DRAIN VISUALIZATION
============================
The quintessential "water going down the drain" view.

This script renders the 3D identity attractor basin using Run 009 data.
With 10 turns per trajectory (vs Run 008's ~6), we should see:
- Clear spiral patterns
- Trajectories converging on or escaping the attractor
- The event horizon as a visible boundary

VIEWS:
1. 3D Phase Space (X=drift[N], Y=drift[N+1], Z=turn)
2. Top-Down "Drain" View (looking into the vortex)
3. Animated GIF showing trajectories evolving
4. Event Horizon Cross-Section
"""

import json
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
from pathlib import Path
from collections import defaultdict
import matplotlib.animation as animation

# Paths
BASE_DIR = Path(__file__).resolve().parent.parent
OUTPUT_DIR = Path(__file__).resolve().parent / "pics"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# Provider colors
PROVIDER_COLORS = {
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
}

def find_latest_run009():
    """Find the most recent Run 009 results file."""
    results_dir = BASE_DIR / "armada_results"
    run009_files = list(results_dir.glob("S7_run_009_drain_*.json"))
    if not run009_files:
        return None
    return max(run009_files, key=lambda p: p.stat().st_mtime)

def load_trajectories(results_file):
    """Load trajectory data from Run 009 results."""
    with open(results_file, encoding='utf-8') as f:
        data = json.load(f)

    # Use the pre-extracted trajectories if available
    if "trajectories_for_3d" in data:
        return data["trajectories_for_3d"]

    # Otherwise extract from raw results
    trajectories = []
    for ship_name, ship_data in data.get("results", {}).items():
        if "error" in ship_data:
            continue

        provider = ship_data.get("provider", "unknown")
        for protocol_name, protocol_data in ship_data.get("protocols", {}).items():
            meta = protocol_data.get("meta", {})
            if "drift_sequence" in meta:
                trajectories.append({
                    "ship": ship_name,
                    "provider": provider,
                    "protocol": protocol_name,
                    "drifts": meta["drift_sequence"],
                    "status": meta.get("status"),
                    "baseline": meta.get("baseline"),
                    "below_horizon": meta.get("below_event_horizon")
                })

    return trajectories

def plot_3d_drain(trajectories, output_path):
    """
    Main 3D drain visualization.
    X = drift[N], Y = drift[N+1], Z = turn number
    """
    fig = plt.figure(figsize=(16, 14))
    ax = fig.add_subplot(111, projection='3d')

    stuck_count = 0
    recovered_count = 0

    for traj in trajectories:
        drifts = traj.get("drifts", [])
        if len(drifts) < 3:
            continue

        provider = traj.get("provider", "unknown")
        status = traj.get("status", "unknown")
        color = PROVIDER_COLORS.get(provider, "gray")

        # Phase space coordinates
        xs = drifts[:-1]  # drift[N]
        ys = drifts[1:]   # drift[N+1]
        zs = list(range(len(xs)))  # turn number

        # Style based on outcome
        if status == "STUCK":
            alpha = 0.8
            linewidth = 2.0
            stuck_count += 1
        else:
            alpha = 0.5
            linewidth = 1.0
            recovered_count += 1

        # Plot trajectory
        ax.plot(xs, ys, zs, color=color, alpha=alpha, linewidth=linewidth)

        # Start point (green diamond)
        ax.scatter([xs[0]], [ys[0]], [zs[0]], color='lime', s=50, alpha=0.9,
                  marker='D', edgecolors='darkgreen', linewidths=1)

        # End point (red if STUCK, cyan if RECOVERED)
        end_color = 'red' if status == "STUCK" else 'cyan'
        end_marker = 'X' if status == "STUCK" else 'o'
        ax.scatter([xs[-1]], [ys[-1]], [zs[-1]], color=end_color, s=60, alpha=0.9,
                  marker=end_marker, edgecolors='black', linewidths=1)

    # Add the "no change" diagonal plane
    max_drift = 4
    plane_range = np.linspace(0, max_drift, 20)
    max_turns = 10
    X_plane, Z_plane = np.meshgrid(plane_range, range(max_turns))
    Y_plane = X_plane  # y = x (no change line)
    ax.plot_surface(X_plane, Y_plane, Z_plane, alpha=0.08, color='gray')

    # Event horizon cylinder (at baseline ~1.23)
    event_horizon = 1.23
    theta = np.linspace(0, 2*np.pi, 50)
    z_cylinder = np.linspace(0, max_turns-1, 20)
    Theta, Z_cyl = np.meshgrid(theta, z_cylinder)
    X_cyl = event_horizon * np.cos(Theta) + event_horizon
    Y_cyl = event_horizon * np.sin(Theta) + event_horizon
    ax.plot_surface(X_cyl, Y_cyl, Z_cyl, alpha=0.05, color='red')

    # Labels
    ax.set_xlabel('Drift at Turn N', fontsize=12, labelpad=10)
    ax.set_ylabel('Drift at Turn N+1', fontsize=12, labelpad=10)
    ax.set_zlabel('Turn Number', fontsize=12, labelpad=10)

    ax.set_title(f'THE DRAIN: Identity Attractor Basin\n'
                f'({stuck_count} STUCK, {recovered_count} RECOVERED)',
                fontsize=16, fontweight='bold', pad=20)

    ax.set_xlim(0, max_drift)
    ax.set_ylim(0, max_drift)
    ax.set_zlim(0, max_turns)

    # Legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='#7c3aed', linewidth=2, label='Claude'),
        Line2D([0], [0], color='#10a37f', linewidth=2, label='GPT'),
        Line2D([0], [0], color='#4285f4', linewidth=2, label='Gemini'),
        Line2D([0], [0], marker='D', color='w', markerfacecolor='lime',
               markersize=10, label='Start'),
        Line2D([0], [0], marker='X', color='w', markerfacecolor='red',
               markersize=10, label='End (STUCK)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='cyan',
               markersize=10, label='End (RECOVERED)'),
    ]
    ax.legend(handles=legend_elements, loc='upper left', fontsize=10)

    # View angle for drain effect
    ax.view_init(elev=25, azim=45)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path.name}")
    plt.close()

def plot_topdown_drain(trajectories, output_path):
    """
    Top-down view - looking directly into the drain.
    This is the quintessential "water spiraling" view.
    """
    fig, ax = plt.subplots(figsize=(12, 12))

    # Use polar-like visualization
    stuck_count = 0
    recovered_count = 0

    for traj in trajectories:
        drifts = traj.get("drifts", [])
        if len(drifts) < 3:
            continue

        provider = traj.get("provider", "unknown")
        status = traj.get("status", "unknown")
        color = PROVIDER_COLORS.get(provider, "gray")

        # Convert to "drain" coordinates
        # As turns progress, we spiral inward OR outward
        # Use drift as radius, turn as angle
        turns = len(drifts)
        angles = np.linspace(0, 2*np.pi * (turns/5), turns)  # Multiple rotations

        # Radius is based on drift (inverted - lower drift = closer to center)
        radii = np.array(drifts)

        # Convert to cartesian
        xs = radii * np.cos(angles)
        ys = radii * np.sin(angles)

        if status == "STUCK":
            alpha = 0.7
            linewidth = 1.5
            stuck_count += 1
        else:
            alpha = 0.4
            linewidth = 0.8
            recovered_count += 1

        # Plot spiral
        ax.plot(xs, ys, color=color, alpha=alpha, linewidth=linewidth)

        # Start (outer) and end points
        ax.scatter(xs[0], ys[0], color='lime', s=40, alpha=0.8, zorder=5,
                  marker='D', edgecolors='darkgreen')
        end_color = 'red' if status == "STUCK" else 'cyan'
        ax.scatter(xs[-1], ys[-1], color=end_color, s=50, alpha=0.8, zorder=5,
                  marker='X' if status == "STUCK" else 'o', edgecolors='black')

    # Event horizon circle
    theta = np.linspace(0, 2*np.pi, 100)
    horizon_r = 1.23
    ax.plot(horizon_r * np.cos(theta), horizon_r * np.sin(theta),
           'r--', linewidth=2, alpha=0.5, label=f'Event Horizon (r={horizon_r})')

    # Center point (the attractor)
    ax.scatter([0], [0], color='black', s=200, marker='*', zorder=10,
              label='Attractor (Origin)')

    # Concentric circles for reference
    for r in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]:
        circle = plt.Circle((0, 0), r, fill=False, color='gray', alpha=0.2, linestyle=':')
        ax.add_patch(circle)
        ax.text(r, 0.1, f'{r}', fontsize=8, color='gray', alpha=0.5)

    ax.set_xlim(-4, 4)
    ax.set_ylim(-4, 4)
    ax.set_aspect('equal')
    ax.set_xlabel('X (drift × cos(angle))', fontsize=12)
    ax.set_ylabel('Y (drift × sin(angle))', fontsize=12)
    ax.set_title(f'TOP-DOWN DRAIN VIEW: Looking Into the Vortex\n'
                f'({stuck_count} STUCK spiraling in, {recovered_count} RECOVERED escaping)',
                fontsize=14, fontweight='bold')
    ax.grid(True, alpha=0.3)
    ax.legend(loc='upper right', fontsize=10)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path.name}")
    plt.close()

def plot_phase_portrait(trajectories, output_path):
    """
    Classic phase portrait: drift[N] vs drift[N+1] with arrows.
    Shows the flow field of identity dynamics.
    """
    fig, axes = plt.subplots(1, 2, figsize=(16, 8))

    # LEFT: All trajectories with arrows
    ax1 = axes[0]

    for traj in trajectories:
        drifts = traj.get("drifts", [])
        if len(drifts) < 3:
            continue

        provider = traj.get("provider", "unknown")
        status = traj.get("status", "unknown")
        color = PROVIDER_COLORS.get(provider, "gray")

        xs = drifts[:-1]
        ys = drifts[1:]

        alpha = 0.6 if status == "STUCK" else 0.3

        # Plot with arrows
        for i in range(len(xs) - 1):
            ax1.annotate('', xy=(xs[i+1], ys[i+1]), xytext=(xs[i], ys[i]),
                        arrowprops=dict(arrowstyle='->', color=color, alpha=alpha, lw=0.5))

    # Diagonal (no change line)
    ax1.plot([0, 4], [0, 4], 'k--', alpha=0.3, label='No change')

    # Zones
    ax1.fill_between([0, 4], [0, 4], [4, 4], alpha=0.1, color='red', label='Drifting up')
    ax1.fill_between([0, 4], [0, 0], [0, 4], alpha=0.1, color='green', label='Recovering')

    # Event horizon marker
    ax1.axvline(x=1.23, color='red', linestyle=':', alpha=0.5, label='Event horizon baseline')

    ax1.set_xlabel('Drift at Turn N', fontsize=12)
    ax1.set_ylabel('Drift at Turn N+1', fontsize=12)
    ax1.set_title('PHASE PORTRAIT: Flow Direction', fontsize=14, fontweight='bold')
    ax1.set_xlim(0, 4)
    ax1.set_ylim(0, 4)
    ax1.set_aspect('equal')
    ax1.legend(loc='upper left', fontsize=9)
    ax1.grid(True, alpha=0.3)

    # RIGHT: Vector field (average flow)
    ax2 = axes[1]

    # Create grid
    grid_size = 20
    x_grid = np.linspace(0.1, 3.5, grid_size)
    y_grid = np.linspace(0.1, 3.5, grid_size)
    X, Y = np.meshgrid(x_grid, y_grid)

    # Calculate average flow at each point
    U = np.zeros_like(X)  # dx
    V = np.zeros_like(Y)  # dy
    counts = np.zeros_like(X)

    for traj in trajectories:
        drifts = traj.get("drifts", [])
        if len(drifts) < 3:
            continue

        for i in range(len(drifts) - 1):
            x_now = drifts[i]
            y_next = drifts[i+1]

            # Find nearest grid point
            i_idx = np.argmin(np.abs(x_grid - x_now))
            j_idx = np.argmin(np.abs(y_grid - y_next))

            if i < len(drifts) - 2:
                dx = drifts[i+1] - drifts[i]
                dy = drifts[i+2] - drifts[i+1]
                U[j_idx, i_idx] += dx
                V[j_idx, i_idx] += dy
                counts[j_idx, i_idx] += 1

    # Average
    mask = counts > 0
    U[mask] /= counts[mask]
    V[mask] /= counts[mask]

    # Normalize for visualization
    magnitude = np.sqrt(U**2 + V**2)
    magnitude[magnitude == 0] = 1  # Avoid division by zero
    U_norm = U / magnitude
    V_norm = V / magnitude

    # Plot vector field
    ax2.quiver(X, Y, U_norm, V_norm, magnitude, cmap='coolwarm', alpha=0.7)

    # Diagonal
    ax2.plot([0, 4], [0, 4], 'k--', alpha=0.3)

    ax2.set_xlabel('Drift at Turn N', fontsize=12)
    ax2.set_ylabel('Drift at Turn N+1', fontsize=12)
    ax2.set_title('VECTOR FIELD: Average Flow Direction\n(color = magnitude)',
                 fontsize=14, fontweight='bold')
    ax2.set_xlim(0, 4)
    ax2.set_ylim(0, 4)
    ax2.set_aspect('equal')
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path.name}")
    plt.close()

def plot_protocol_comparison(trajectories, output_path):
    """
    Compare trajectories by protocol type.
    Shows which perturbation patterns create which dynamics.
    """
    protocols = ["Gradual Ramp", "Sharp Shock", "Oscillation", "Social Engineering"]
    fig, axes = plt.subplots(2, 2, figsize=(14, 14))

    for idx, protocol in enumerate(protocols):
        ax = axes.flat[idx]

        protocol_trajs = [t for t in trajectories if t.get("protocol") == protocol]

        stuck = 0
        recovered = 0

        for traj in protocol_trajs:
            drifts = traj.get("drifts", [])
            if len(drifts) < 3:
                continue

            provider = traj.get("provider", "unknown")
            status = traj.get("status", "unknown")
            color = PROVIDER_COLORS.get(provider, "gray")

            if status == "STUCK":
                stuck += 1
                linestyle = '-'
            else:
                recovered += 1
                linestyle = '--'

            ax.plot(range(len(drifts)), drifts, color=color,
                   linestyle=linestyle, alpha=0.7, linewidth=1.5)

        ax.axhline(y=1.23, color='red', linestyle=':', alpha=0.5, label='Event Horizon')
        ax.set_xlabel('Turn', fontsize=11)
        ax.set_ylabel('Drift', fontsize=11)
        ax.set_title(f'{protocol}\n(STUCK: {stuck}, RECOVERED: {recovered})',
                    fontsize=12, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper right', fontsize=9)

    fig.suptitle('PROTOCOL COMPARISON: Different Perturbation Patterns',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"Saved: {output_path.name}")
    plt.close()

# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("RUN 009: DRAIN VISUALIZATION")
    print("=" * 60)

    # Find Run 009 data
    results_file = find_latest_run009()

    if results_file is None:
        print("\nNo Run 009 data found!")
        print("Run `python run009_drain_capture.py` first to generate data.")
        print("\nGenerating DEMO visualizations with Run 008 data instead...")

        # Fall back to Run 008 for demo
        run008_file = BASE_DIR / "armada_results" / "S7_run_008_20251201_020501.json"
        if run008_file.exists():
            print(f"Using: {run008_file}")

            with open(run008_file, encoding='utf-8') as f:
                data = json.load(f)

            # Extract trajectories from Run 008 format
            trajectories = []
            for ship_name, ship_data in data.get('results', {}).items():
                if not isinstance(ship_data, dict):
                    continue

                provider = "unknown"
                name_lower = ship_name.lower()
                if "claude" in name_lower:
                    provider = "claude"
                elif "gemini" in name_lower:
                    provider = "gemini"
                elif name_lower.startswith("o1") or name_lower.startswith("o3") or name_lower.startswith("o4") or "gpt" in name_lower:
                    provider = "gpt"

                for seq_name, seq_turns in ship_data.get('sequences', {}).items():
                    if not isinstance(seq_turns, list):
                        continue

                    drifts = []
                    for turn in seq_turns:
                        if isinstance(turn, dict) and 'drift_data' in turn:
                            drift = turn['drift_data'].get('drift', 0)
                            drifts.append(drift)

                    if len(drifts) >= 3:
                        baseline = drifts[0]
                        final = drifts[-1]
                        ratio = final / max(0.001, baseline)
                        status = "STUCK" if ratio > 1.5 else "RECOVERED"

                        trajectories.append({
                            "ship": ship_name,
                            "provider": provider,
                            "protocol": seq_name,
                            "drifts": drifts,
                            "status": status,
                            "baseline": baseline,
                            "below_horizon": baseline < 1.23
                        })

            print(f"Extracted {len(trajectories)} trajectories from Run 008")
        else:
            print("No data available. Exiting.")
            exit(1)
    else:
        print(f"\nUsing: {results_file}")
        trajectories = load_trajectories(results_file)
        print(f"Loaded {len(trajectories)} trajectories")

    # Generate visualizations
    print("\n" + "-" * 40)
    print("Generating visualizations...")

    plot_3d_drain(trajectories, OUTPUT_DIR / "run009_3d_drain.png")
    plot_topdown_drain(trajectories, OUTPUT_DIR / "run009_topdown_drain.png")
    plot_phase_portrait(trajectories, OUTPUT_DIR / "run009_phase_portrait.png")
    plot_protocol_comparison(trajectories, OUTPUT_DIR / "run009_protocol_comparison.png")

    print("-" * 40)
    print(f"\nAll visualizations saved to: {OUTPUT_DIR}")
    print("=" * 60)
