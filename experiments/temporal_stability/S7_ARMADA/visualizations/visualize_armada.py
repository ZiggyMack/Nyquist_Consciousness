"""
ARMADA VISUALIZATION - Unified Run-Agnostic Script
===================================================
Single visualization script that works with ANY armada run data.

USAGE:
  python visualize_armada.py                  # Auto-detect latest run
  python visualize_armada.py --run 008        # Specific run
  python visualize_armada.py --run 009        # Another run
  python visualize_armada.py --list           # List available runs
  python visualize_armada.py --all            # Generate all viz types

FEATURES:
- Auto-detects available run data files
- Generates raw + spline-smoothed visualizations
- Exports PNG (300 DPI), SVG, and interactive HTML
- Maintains 100% data integrity (smoothing is presentational only)

VISUALIZATION TYPES:
1. Phase Portrait (drift[N] vs drift[N+1])
2. Vortex/Drain View (polar spiral)
3. 3D Phase Space Basin
4. Stability Basin (baseline vs max drift)
5. Event Horizon Analysis
6. Pillar Structure Analysis
"""

import argparse
import json
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from pathlib import Path
from collections import defaultdict
from scipy.interpolate import make_interp_spline

# Try plotly for interactive HTML
try:
    import plotly.graph_objects as go
    PLOTLY_AVAILABLE = True
except ImportError:
    PLOTLY_AVAILABLE = False

# =============================================================================
# PATHS
# =============================================================================
BASE_DIR = Path(__file__).resolve().parent.parent
RESULTS_DIR = BASE_DIR / "armada_results"
OUTPUT_DIR = Path(__file__).resolve().parent / "pics"

# Provider colors (4 providers now)
PROVIDER_COLORS = {
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
    "grok": "#1a1a1a",
}

# =============================================================================
# RUN DETECTION
# =============================================================================

def find_available_runs():
    """Scan results directory for available run data."""
    runs = {}

    if not RESULTS_DIR.exists():
        return runs

    for f in RESULTS_DIR.glob("S7_run_*.json"):
        name = f.stem
        # Parse run number from filename
        # e.g., S7_run_008_20251201_020501.json -> 008
        parts = name.split("_")
        if len(parts) >= 3:
            run_num = parts[2]
            if run_num not in runs:
                runs[run_num] = []
            runs[run_num].append(f)

    # Also check for prep/pilot files
    for f in RESULTS_DIR.glob("S7_run_*_prep*.json"):
        name = f.stem
        parts = name.split("_")
        if len(parts) >= 3:
            run_key = f"{parts[2]}_prep"
            if run_key not in runs:
                runs[run_key] = []
            runs[run_key].append(f)

    # Sort files by modification time (newest first)
    for run_num in runs:
        runs[run_num].sort(key=lambda p: p.stat().st_mtime, reverse=True)

    return runs

def get_latest_run():
    """Get the most recent run file."""
    runs = find_available_runs()
    if not runs:
        return None, None

    # Find the newest file across all runs
    all_files = []
    for run_num, files in runs.items():
        for f in files:
            all_files.append((run_num, f))

    if not all_files:
        return None, None

    all_files.sort(key=lambda x: x[1].stat().st_mtime, reverse=True)
    return all_files[0]

def get_run_file(run_id):
    """Get the data file for a specific run."""
    runs = find_available_runs()

    # Normalize run_id (e.g., "8" -> "008", "008_prep" stays)
    if run_id.isdigit():
        run_id = run_id.zfill(3)

    if run_id in runs and runs[run_id]:
        return run_id, runs[run_id][0]

    return None, None

# =============================================================================
# DATA EXTRACTION
# =============================================================================

def get_provider(ship_name):
    """Classify ship by provider."""
    name = ship_name.lower()
    if "claude" in name:
        return "claude"
    elif "gemini" in name:
        return "gemini"
    elif "grok" in name:
        return "grok"
    elif name.startswith("o1") or name.startswith("o3") or name.startswith("o4") or "gpt" in name:
        return "gpt"
    return "unknown"

def extract_trajectories(data):
    """Extract drift trajectories from run data (handles multiple formats)."""
    trajectories = []

    # Try Run 008+ format (sequences)
    results = data.get('results', {})
    for ship_name, ship_data in results.items():
        if not isinstance(ship_data, dict):
            continue

        provider = get_provider(ship_name)

        # Format 1: sequences dict
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
                status = "VOLATILE" if ratio > 1.5 else "STABLE"

                trajectories.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': seq_name,
                    'drifts': drifts,
                    'status': status,
                    'baseline': baseline
                })

        # Format 2: protocols dict (Run 009 drain capture)
        for protocol_name, protocol_data in ship_data.get('protocols', {}).items():
            if not isinstance(protocol_data, dict):
                continue

            meta = protocol_data.get('meta', {})
            if 'drift_sequence' in meta:
                drifts = meta['drift_sequence']
                trajectories.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': protocol_name,
                    'drifts': drifts,
                    'status': meta.get('status', 'unknown'),
                    'baseline': meta.get('baseline', drifts[0] if drifts else 0)
                })

    # Use pre-extracted trajectories if available
    if 'trajectories_for_3d' in data:
        for t in data['trajectories_for_3d']:
            trajectories.append(t)

    return trajectories

# =============================================================================
# SPLINE SMOOTHING
# =============================================================================

def smooth_trajectory(values, num_points=100):
    """Apply cubic B-spline interpolation."""
    if len(values) < 4:
        t = np.arange(len(values))
        t_new = np.linspace(0, len(values)-1, num_points)
        return np.interp(t_new, t, values)

    t = np.arange(len(values))
    t_new = np.linspace(0, len(values)-1, num_points)
    spline = make_interp_spline(t, values, k=3)
    return spline(t_new)

def smooth_trajectory_2d(x_vals, y_vals, num_points=100):
    """Smooth a 2D trajectory."""
    return smooth_trajectory(x_vals, num_points), smooth_trajectory(y_vals, num_points)

# =============================================================================
# VISUALIZATION FUNCTIONS
# =============================================================================

def plot_phase_portrait(trajectories, output_dir, run_id):
    """Phase portrait: drift[N] vs drift[N+1] - Raw vs Smoothed."""
    fig, axes = plt.subplots(1, 2, figsize=(18, 9))

    for ax_idx, (ax, smoothed) in enumerate(zip(axes, [False, True])):
        title_suffix = "SMOOTHED (B-Spline)" if smoothed else "RAW DATA"

        for traj in trajectories:
            drifts = traj['drifts']
            if len(drifts) < 3:
                continue

            provider = traj['provider']
            status = traj['status']
            color = PROVIDER_COLORS.get(provider, 'gray')

            xs = drifts[:-1]
            ys = drifts[1:]

            alpha = 0.7 if status == "VOLATILE" else 0.4
            linewidth = 1.5 if status == "VOLATILE" else 0.8

            if smoothed:
                xs_smooth, ys_smooth = smooth_trajectory_2d(xs, ys, num_points=50)
                ax.plot(xs_smooth, ys_smooth, color=color, alpha=alpha, linewidth=linewidth)
                ax.scatter(xs, ys, color=color, s=15, alpha=0.5, edgecolors='white', linewidths=0.5, zorder=5)
            else:
                for i in range(len(xs) - 1):
                    ax.annotate('', xy=(xs[i+1], ys[i+1]), xytext=(xs[i], ys[i]),
                               arrowprops=dict(arrowstyle='->', color=color, alpha=alpha, lw=0.5))

            if len(xs) > 0:
                ax.scatter(xs[0], ys[0], color='lime', s=30, alpha=0.8, zorder=10,
                          marker='D', edgecolors='darkgreen', linewidths=1)
                end_color = 'red' if status == "VOLATILE" else 'cyan'
                ax.scatter(xs[-1], ys[-1], color=end_color, s=40, alpha=0.8, zorder=10,
                          marker='X' if status == "VOLATILE" else 'o', edgecolors='black', linewidths=1)

        ax.plot([0, 4], [0, 4], 'k--', alpha=0.3, label='No change')
        ax.fill_between([0, 4], [0, 4], [4, 4], alpha=0.08, color='red')
        ax.fill_between([0, 4], [0, 0], [0, 4], alpha=0.08, color='green')
        ax.axvline(x=1.23, color='red', linestyle=':', alpha=0.5)
        ax.axhline(y=1.23, color='red', linestyle=':', alpha=0.5)

        ax.set_xlabel('Drift at Turn N', fontsize=12)
        ax.set_ylabel('Drift at Turn N+1', fontsize=12)
        ax.set_title(f'PHASE PORTRAIT: {title_suffix}', fontsize=14, fontweight='bold')
        ax.set_xlim(0, 4)
        ax.set_ylim(0, 4)
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)

    fig.suptitle(f'Run {run_id}: Identity Flow - Raw vs Spline-Smoothed', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_phase_portrait.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_phase_portrait.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_phase_portrait.png + .svg")
    plt.close()

def plot_vortex(trajectories, output_dir, run_id):
    """Vortex/drain view - polar spiral visualization."""
    fig, axes = plt.subplots(1, 2, figsize=(18, 9))

    for ax_idx, (ax, smoothed) in enumerate(zip(axes, [False, True])):
        title_suffix = "SMOOTHED" if smoothed else "RAW"

        for traj in trajectories:
            drifts = traj['drifts']
            if len(drifts) < 3:
                continue

            provider = traj['provider']
            status = traj['status']
            color = PROVIDER_COLORS.get(provider, 'gray')

            turns = len(drifts)
            angles = np.linspace(0, 2*np.pi * (turns/5), turns)
            radii = np.array(drifts)

            xs = radii * np.cos(angles)
            ys = radii * np.sin(angles)

            alpha = 0.7 if status == "VOLATILE" else 0.4
            linewidth = 1.5 if status == "VOLATILE" else 0.8

            if smoothed:
                xs_smooth, ys_smooth = smooth_trajectory_2d(xs, ys, num_points=80)
                ax.plot(xs_smooth, ys_smooth, color=color, alpha=alpha, linewidth=linewidth)
                ax.scatter(xs, ys, color=color, s=12, alpha=0.4, edgecolors='white', linewidths=0.3, zorder=5)
            else:
                ax.plot(xs, ys, color=color, alpha=alpha, linewidth=linewidth)

            ax.scatter(xs[0], ys[0], color='lime', s=35, alpha=0.9, zorder=10,
                      marker='D', edgecolors='darkgreen', linewidths=1)
            end_color = 'red' if status == "VOLATILE" else 'cyan'
            ax.scatter(xs[-1], ys[-1], color=end_color, s=45, alpha=0.9, zorder=10,
                      marker='X' if status == "VOLATILE" else 'o', edgecolors='black', linewidths=1)

        theta = np.linspace(0, 2*np.pi, 100)
        ax.plot(1.23 * np.cos(theta), 1.23 * np.sin(theta), 'r--', linewidth=2.5, alpha=0.7)
        ax.scatter([0], [0], color='black', s=250, marker='*', zorder=15)

        for r in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]:
            circle = plt.Circle((0, 0), r, fill=False, color='gray', alpha=0.2, linestyle=':')
            ax.add_patch(circle)

        ax.set_xlim(-4, 4)
        ax.set_ylim(-4, 4)
        ax.set_aspect('equal')
        ax.set_xlabel('X (drift * cos(angle))', fontsize=11)
        ax.set_ylabel('Y (drift * sin(angle))', fontsize=11)
        ax.set_title(f'VORTEX VIEW: {title_suffix}', fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)

    fig.suptitle(f'Run {run_id}: Looking Into the Identity Drain', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_vortex.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_vortex.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_vortex.png + .svg")
    plt.close()

def plot_3d_basin(trajectories, output_dir, run_id):
    """3D phase space basin visualization."""
    fig = plt.figure(figsize=(18, 8))

    for plot_idx, smoothed in enumerate([False, True]):
        ax = fig.add_subplot(1, 2, plot_idx + 1, projection='3d')
        title_suffix = "SMOOTHED" if smoothed else "RAW"

        volatile_count = 0
        stable_count = 0

        for traj in trajectories:
            drifts = traj['drifts']
            if len(drifts) < 3:
                continue

            provider = traj['provider']
            status = traj['status']
            color = PROVIDER_COLORS.get(provider, 'gray')

            xs = drifts[:-1]
            ys = drifts[1:]
            zs = list(range(len(xs)))

            if status == "VOLATILE":
                alpha = 0.8
                linewidth = 2.0
                volatile_count += 1
            else:
                alpha = 0.5
                linewidth = 1.0
                stable_count += 1

            if smoothed:
                num_pts = 50
                t = np.arange(len(xs))
                t_new = np.linspace(0, len(xs)-1, num_pts)

                if len(xs) >= 4:
                    xs_s = make_interp_spline(t, xs, k=3)(t_new)
                    ys_s = make_interp_spline(t, ys, k=3)(t_new)
                    zs_s = make_interp_spline(t, zs, k=3)(t_new)
                else:
                    xs_s = np.interp(t_new, t, xs)
                    ys_s = np.interp(t_new, t, ys)
                    zs_s = np.interp(t_new, t, zs)

                ax.plot(xs_s, ys_s, zs_s, color=color, alpha=alpha, linewidth=linewidth)
                ax.scatter(xs, ys, zs, color=color, s=15, alpha=0.5, edgecolors='white', linewidths=0.3)
            else:
                ax.plot(xs, ys, zs, color=color, alpha=alpha, linewidth=linewidth)

            if len(xs) > 0:
                ax.scatter([xs[0]], [ys[0]], [zs[0]], color='lime', s=40, alpha=0.9, marker='D')
                end_color = 'red' if status == "VOLATILE" else 'cyan'
                ax.scatter([xs[-1]], [ys[-1]], [zs[-1]], color=end_color, s=50, alpha=0.9,
                          marker='X' if status == "VOLATILE" else 'o')

        max_drift = 4
        max_turns = 10
        plane_range = np.linspace(0, max_drift, 15)
        X_plane, Z_plane = np.meshgrid(plane_range, range(max_turns))
        Y_plane = X_plane
        ax.plot_surface(X_plane, Y_plane, Z_plane, alpha=0.08, color='gray')

        ax.set_xlabel('Drift[N]', fontsize=10, labelpad=5)
        ax.set_ylabel('Drift[N+1]', fontsize=10, labelpad=5)
        ax.set_zlabel('Turn', fontsize=10, labelpad=5)
        ax.set_title(f'3D BASIN: {title_suffix}\n(VOLATILE: {volatile_count}, STABLE: {stable_count})',
                    fontsize=12, fontweight='bold')

        ax.set_xlim(0, max_drift)
        ax.set_ylim(0, max_drift)
        ax.set_zlim(0, max_turns)
        ax.view_init(elev=20, azim=45)

    fig.suptitle(f'Run {run_id}: Identity Attractor Basin - 3D Phase Space', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_3d_basin.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_3d_basin.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_3d_basin.png + .svg")
    plt.close()

def plot_stability_basin(trajectories, output_dir, run_id):
    """Stability basin: baseline vs max drift by provider."""
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))

    # Group by provider
    provider_data = defaultdict(lambda: {'baselines': [], 'max_drifts': [], 'statuses': []})

    for traj in trajectories:
        provider = traj['provider']
        drifts = traj['drifts']
        if len(drifts) >= 2:
            provider_data[provider]['baselines'].append(drifts[0])
            provider_data[provider]['max_drifts'].append(max(drifts))
            provider_data[provider]['statuses'].append(traj['status'])

    # Left: Baseline vs Max Drift
    ax1 = axes[0]
    for provider, pdata in provider_data.items():
        color = PROVIDER_COLORS.get(provider, 'gray')
        ax1.scatter(pdata['baselines'], pdata['max_drifts'],
                   c=color, alpha=0.6, s=60, label=f"{provider.title()} (n={len(pdata['baselines'])})")

    ax1.plot([0, 4], [0, 4], 'k--', alpha=0.3, label='No change')
    ax1.axvline(x=1.23, color='red', linestyle=':', alpha=0.5, label='Event Horizon')
    ax1.set_xlabel('Baseline Drift', fontsize=12)
    ax1.set_ylabel('Max Drift', fontsize=12)
    ax1.set_title('Baseline vs Max Drift by Provider', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 4)
    ax1.set_ylim(0, 4)

    # Right: VOLATILE vs STABLE distribution
    ax2 = axes[1]
    volatile_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'VOLATILE']
    stable_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'STABLE']

    bins = np.linspace(0, 3, 20)
    ax2.hist(stable_baselines, bins=bins, alpha=0.7, color='cyan', label=f'STABLE (n={len(stable_baselines)})', edgecolor='white')
    ax2.hist(volatile_baselines, bins=bins, alpha=0.7, color='red', label=f'VOLATILE (n={len(volatile_baselines)})', edgecolor='white')

    if volatile_baselines and stable_baselines:
        horizon = (np.mean(volatile_baselines) + np.mean(stable_baselines)) / 2
        ax2.axvline(x=horizon, color='black', linestyle='--', linewidth=2, label=f'Threshold (~{horizon:.2f})')

    ax2.set_xlabel('Baseline Drift', fontsize=12)
    ax2.set_ylabel('Count', fontsize=12)
    ax2.set_title('Event Horizon: Where Recovery Becomes Unlikely', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right')
    ax2.grid(True, alpha=0.3, axis='y')

    fig.suptitle(f'Run {run_id}: Identity Stability Basin', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_stability_basin.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: run{run_id}_stability_basin.png")
    plt.close()

def create_interactive_html(trajectories, output_dir, run_id):
    """Create interactive Plotly visualizations."""
    if not PLOTLY_AVAILABLE:
        print("  Skipping HTML export (plotly not installed)")
        return

    # 3D Basin
    fig = go.Figure()

    for traj in trajectories:
        drifts = traj['drifts']
        if len(drifts) < 3:
            continue

        provider = traj['provider']
        status = traj['status']
        color = PROVIDER_COLORS.get(provider, 'gray')

        xs = drifts[:-1]
        ys = drifts[1:]
        zs = list(range(len(xs)))

        # Smooth
        if len(xs) >= 4:
            t = np.arange(len(xs))
            t_new = np.linspace(0, len(xs)-1, 50)
            xs_s = make_interp_spline(t, xs, k=3)(t_new)
            ys_s = make_interp_spline(t, ys, k=3)(t_new)
            zs_s = make_interp_spline(t, zs, k=3)(t_new)
        else:
            xs_s, ys_s, zs_s = xs, ys, zs

        width = 4 if status == "VOLATILE" else 2

        fig.add_trace(go.Scatter3d(
            x=xs_s, y=ys_s, z=zs_s,
            mode='lines',
            line=dict(color=color, width=width),
            name=f"{traj['ship']} ({status})",
            hovertemplate=f"Ship: {traj['ship']}<br>Provider: {provider}<br>Status: {status}<extra></extra>"
        ))

    fig.update_layout(
        title=f"Run {run_id}: Interactive 3D Identity Basin",
        scene=dict(
            xaxis_title="Drift at Turn N",
            yaxis_title="Drift at Turn N+1",
            zaxis_title="Turn Number"
        ),
        width=1200,
        height=900
    )

    fig.write_html(output_dir / f'run{run_id}_interactive_3d.html')
    print(f"  Saved: run{run_id}_interactive_3d.html")

    # Vortex
    fig2 = go.Figure()

    for traj in trajectories:
        drifts = traj['drifts']
        if len(drifts) < 3:
            continue

        provider = traj['provider']
        status = traj['status']
        color = PROVIDER_COLORS.get(provider, 'gray')

        turns = len(drifts)
        angles = np.linspace(0, 2*np.pi * (turns/5), turns)
        radii = np.array(drifts)

        xs = radii * np.cos(angles)
        ys = radii * np.sin(angles)

        xs_s, ys_s = smooth_trajectory_2d(xs, ys, num_points=80)
        width = 3 if status == "VOLATILE" else 1.5

        fig2.add_trace(go.Scatter(
            x=xs_s, y=ys_s,
            mode='lines',
            line=dict(color=color, width=width),
            name=f"{traj['ship']} ({status})"
        ))

    # Event horizon circle
    theta = np.linspace(0, 2*np.pi, 100)
    fig2.add_trace(go.Scatter(
        x=1.23 * np.cos(theta), y=1.23 * np.sin(theta),
        mode='lines',
        line=dict(color='red', width=3, dash='dash'),
        name='Event Horizon'
    ))

    fig2.update_layout(
        title=f"Run {run_id}: Interactive Vortex View",
        xaxis=dict(scaleanchor='y', scaleratio=1, range=[-4, 4]),
        yaxis=dict(range=[-4, 4]),
        width=1000,
        height=1000
    )

    fig2.write_html(output_dir / f'run{run_id}_interactive_vortex.html')
    print(f"  Saved: run{run_id}_interactive_vortex.html")

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description='Armada Visualization - Unified Run-Agnostic Script')
    parser.add_argument('--run', type=str, help='Run ID (e.g., 008, 009, 008_prep)')
    parser.add_argument('--list', action='store_true', help='List available runs')
    parser.add_argument('--all', action='store_true', help='Generate all visualization types')
    parser.add_argument('--type', type=str, choices=['phase', 'vortex', '3d', 'stability', 'html'],
                       help='Specific visualization type')
    args = parser.parse_args()

    # List available runs
    if args.list:
        runs = find_available_runs()
        print("\nAvailable Runs:")
        print("-" * 40)
        for run_id, files in sorted(runs.items()):
            print(f"  Run {run_id}: {len(files)} file(s)")
            for f in files[:2]:
                print(f"    - {f.name}")
        return

    # Find run data
    if args.run:
        run_id, data_file = get_run_file(args.run)
    else:
        run_id, data_file = get_latest_run()

    if data_file is None:
        print("ERROR: No run data found!")
        print("  Run `python run008_with_keys.py` or `python run009_drain_capture.py` first.")
        return

    print("=" * 70)
    print("ARMADA VISUALIZATION")
    print("=" * 70)
    print(f"\nRun: {run_id}")
    print(f"Data: {data_file.name}")

    # Load data
    with open(data_file, encoding='utf-8') as f:
        data = json.load(f)

    trajectories = extract_trajectories(data)

    volatile = sum(1 for t in trajectories if t['status'] == "VOLATILE")
    stable = len(trajectories) - volatile
    print(f"Trajectories: {len(trajectories)} (VOLATILE: {volatile}, STABLE: {stable})")

    # Create output directory
    run_output_dir = OUTPUT_DIR / f"run{run_id}"
    run_output_dir.mkdir(parents=True, exist_ok=True)
    print(f"Output: {run_output_dir}")
    print("-" * 70)

    # Generate visualizations
    if args.type:
        viz_types = [args.type]
    elif args.all:
        viz_types = ['phase', 'vortex', '3d', 'stability', 'html']
    else:
        viz_types = ['phase', 'vortex', '3d', 'stability', 'html']

    print("\nGenerating visualizations...")

    if 'phase' in viz_types:
        plot_phase_portrait(trajectories, run_output_dir, run_id)

    if 'vortex' in viz_types:
        plot_vortex(trajectories, run_output_dir, run_id)

    if '3d' in viz_types:
        plot_3d_basin(trajectories, run_output_dir, run_id)

    if 'stability' in viz_types:
        plot_stability_basin(trajectories, run_output_dir, run_id)

    if 'html' in viz_types:
        create_interactive_html(trajectories, run_output_dir, run_id)

    print("\n" + "-" * 70)
    print("COMPLETE!")
    print(f"All outputs in: {run_output_dir}")
    print("=" * 70)

if __name__ == "__main__":
    main()
