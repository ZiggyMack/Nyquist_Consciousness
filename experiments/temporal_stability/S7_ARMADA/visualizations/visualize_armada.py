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
  python visualize_armada.py --dB             # Use decibel scaling

FEATURES:
- Auto-detects available run data files
- Generates raw + spline-smoothed visualizations
- Exports PNG (300 DPI), SVG, and interactive HTML
- Maintains 100% data integrity (smoothing is presentational only)
- dB scaling option for compressed dynamic range
- FFT spectral analysis for frequency content
- Event Horizon cylinder in 3D views

VISUALIZATION TYPES:
1. Phase Portrait (drift[N] vs drift[N+1])
2. Vortex/Drain View (polar spiral)
3. 3D Phase Space Basin with Event Horizon cylinder
4. Stability Basin (baseline vs max drift)
5. FFT Spectral Analysis
6. Interactive HTML exports
"""

import argparse
import json
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from pathlib import Path
from collections import defaultdict
from scipy.interpolate import make_interp_spline
from scipy.fft import fft, fftfreq

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

# Event Horizon threshold (Coherence Boundary)
EVENT_HORIZON = 1.23

# =============================================================================
# dB CONVERSION (preserves data integrity - presentational only)
# =============================================================================

def to_dB(value, reference=1.0):
    """Convert linear value to decibels. dB = 20 * log10(value/reference)"""
    value = np.array(value)
    # Avoid log(0) by clamping minimum
    value = np.maximum(value, 1e-10)
    return 20 * np.log10(value / reference)

def from_dB(dB_value, reference=1.0):
    """Convert decibels back to linear value."""
    return reference * (10 ** (dB_value / 20))

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

def normalize_status(status):
    """Map various status names to STABLE/VOLATILE.

    Identity Basin Model:
    - STABLE/RECOVERED = inside the coherence basin, identity maintained
    - VOLATILE/STUCK = outside the basin, identity dissolved
    """
    status_upper = str(status).upper()
    if status_upper in ['STABLE', 'RECOVERED']:
        return 'STABLE'
    elif status_upper in ['VOLATILE', 'STUCK']:
        return 'VOLATILE'
    else:
        return 'UNKNOWN'

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
                raw_status = meta.get('status', 'unknown')
                trajectories.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': protocol_name,
                    'drifts': drifts,
                    'status': normalize_status(raw_status),
                    'baseline': meta.get('baseline', drifts[0] if drifts else 0)
                })

    # Use pre-extracted trajectories if available
    if 'trajectories_for_3d' in data:
        for t in data['trajectories_for_3d']:
            # Normalize: some runs use 'drift_sequence' instead of 'drifts'
            if 'drift_sequence' in t and 'drifts' not in t:
                t['drifts'] = t['drift_sequence']
            # Normalize status
            if 'status' in t:
                t['status'] = normalize_status(t['status'])
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

def plot_phase_portrait(trajectories, output_dir, run_id, use_dB=False):
    """Phase portrait: drift[N] vs drift[N+1] - Raw vs Smoothed."""
    fig, axes = plt.subplots(1, 2, figsize=(18, 9))

    scale_label = " (dB)" if use_dB else ""
    eh_val = to_dB(EVENT_HORIZON) if use_dB else EVENT_HORIZON

    for ax_idx, (ax, smoothed) in enumerate(zip(axes, [False, True])):
        title_suffix = "SMOOTHED (B-Spline)" if smoothed else "RAW DATA"

        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue

            if use_dB:
                drifts = to_dB(drifts)

            provider = traj['provider']
            status = traj['status']
            color = PROVIDER_COLORS.get(provider, 'gray')

            xs = drifts[:-1]
            ys = drifts[1:]

            # STABLE = inside basin = good, VOLATILE = outside = bad
            alpha = 0.4 if status == "STABLE" else 0.7
            linewidth = 0.8 if status == "STABLE" else 1.5

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
                # STABLE = cyan (good), VOLATILE = red (bad)
                end_color = 'cyan' if status == "STABLE" else 'red'
                end_marker = 'o' if status == "STABLE" else 'X'
                ax.scatter(xs[-1], ys[-1], color=end_color, s=40, alpha=0.8, zorder=10,
                          marker=end_marker, edgecolors='black', linewidths=1)

        # Axis limits based on scale
        if use_dB:
            ax_min, ax_max = -20, 20
        else:
            ax_min, ax_max = 0, 4

        ax.plot([ax_min, ax_max], [ax_min, ax_max], 'k--', alpha=0.3, label='No change')
        ax.fill_between([ax_min, ax_max], [ax_min, ax_max], [ax_max, ax_max], alpha=0.08, color='red')
        ax.fill_between([ax_min, ax_max], [ax_min, ax_min], [ax_min, ax_max], alpha=0.08, color='green')
        ax.axvline(x=eh_val, color='red', linestyle=':', alpha=0.5, label=f'Coherence Boundary ({EVENT_HORIZON})')
        ax.axhline(y=eh_val, color='red', linestyle=':', alpha=0.5)

        ax.set_xlabel(f'Drift at Turn N{scale_label}', fontsize=12)
        ax.set_ylabel(f'Drift at Turn N+1{scale_label}', fontsize=12)
        ax.set_title(f'PHASE PORTRAIT: {title_suffix}', fontsize=14, fontweight='bold')
        ax.set_xlim(ax_min, ax_max)
        ax.set_ylim(ax_min, ax_max)
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)

    scale_note = " [dB Scale]" if use_dB else ""
    fig.suptitle(f'Run {run_id}: Identity Flow{scale_note}', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    suffix = "_dB" if use_dB else ""
    plt.savefig(output_dir / f'run{run_id}_phase_portrait{suffix}.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_phase_portrait{suffix}.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_phase_portrait{suffix}.png + .svg")
    plt.close()

def plot_vortex(trajectories, output_dir, run_id, use_dB=False):
    """Vortex/drain view - polar spiral visualization."""
    fig, axes = plt.subplots(1, 2, figsize=(18, 9))

    scale_label = " (dB)" if use_dB else ""

    for ax_idx, (ax, smoothed) in enumerate(zip(axes, [False, True])):
        title_suffix = "SMOOTHED" if smoothed else "RAW"

        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue

            if use_dB:
                # For vortex, shift dB to positive range for radius
                drifts_dB = to_dB(drifts)
                # Shift so minimum is at least 0.5
                drifts = drifts_dB - drifts_dB.min() + 0.5

            provider = traj['provider']
            status = traj['status']
            color = PROVIDER_COLORS.get(provider, 'gray')

            turns = len(drifts)
            angles = np.linspace(0, 2*np.pi * (turns/5), turns)
            radii = np.array(drifts)

            xs = radii * np.cos(angles)
            ys = radii * np.sin(angles)

            alpha = 0.4 if status == "STABLE" else 0.7
            linewidth = 0.8 if status == "STABLE" else 1.5

            if smoothed:
                xs_smooth, ys_smooth = smooth_trajectory_2d(xs, ys, num_points=80)
                ax.plot(xs_smooth, ys_smooth, color=color, alpha=alpha, linewidth=linewidth)
                ax.scatter(xs, ys, color=color, s=12, alpha=0.4, edgecolors='white', linewidths=0.3, zorder=5)
            else:
                ax.plot(xs, ys, color=color, alpha=alpha, linewidth=linewidth)

            ax.scatter(xs[0], ys[0], color='lime', s=35, alpha=0.9, zorder=10,
                      marker='D', edgecolors='darkgreen', linewidths=1)
            end_color = 'cyan' if status == "STABLE" else 'red'
            end_marker = 'o' if status == "STABLE" else 'X'
            ax.scatter(xs[-1], ys[-1], color=end_color, s=45, alpha=0.9, zorder=10,
                      marker=end_marker, edgecolors='black', linewidths=1)

        # Coherence Boundary circle
        eh_radius = to_dB(EVENT_HORIZON) - to_dB(0.1) + 0.5 if use_dB else EVENT_HORIZON
        theta = np.linspace(0, 2*np.pi, 100)
        ax.plot(eh_radius * np.cos(theta), eh_radius * np.sin(theta), 'r--', linewidth=2.5, alpha=0.7,
               label='Coherence Boundary')
        ax.scatter([0], [0], color='gold', s=300, marker='*', zorder=15, label='Identity Attractor')

        # Reference circles
        if use_dB:
            radii_ref = [1, 2, 3, 4, 5]
        else:
            radii_ref = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]
        for r in radii_ref:
            circle = plt.Circle((0, 0), r, fill=False, color='gray', alpha=0.2, linestyle=':')
            ax.add_patch(circle)

        ax_lim = 6 if use_dB else 4
        ax.set_xlim(-ax_lim, ax_lim)
        ax.set_ylim(-ax_lim, ax_lim)
        ax.set_aspect('equal')
        ax.set_xlabel(f'X (drift * cos(angle)){scale_label}', fontsize=11)
        ax.set_ylabel(f'Y (drift * sin(angle)){scale_label}', fontsize=11)
        ax.set_title(f'VORTEX VIEW: {title_suffix}', fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)

    scale_note = " [dB Scale]" if use_dB else ""
    fig.suptitle(f'Run {run_id}: Identity Basin Vortex{scale_note}\n(Inside = STABLE, Outside = VOLATILE)',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    suffix = "_dB" if use_dB else ""
    plt.savefig(output_dir / f'run{run_id}_vortex{suffix}.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_vortex{suffix}.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_vortex{suffix}.png + .svg")
    plt.close()

def plot_3d_basin(trajectories, output_dir, run_id, use_dB=False):
    """3D phase space basin visualization with Event Horizon cylinder."""
    fig = plt.figure(figsize=(18, 8))

    scale_label = " (dB)" if use_dB else ""

    for plot_idx, smoothed in enumerate([False, True]):
        ax = fig.add_subplot(1, 2, plot_idx + 1, projection='3d')
        title_suffix = "SMOOTHED" if smoothed else "RAW"

        stable_count = 0
        volatile_count = 0

        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue

            if use_dB:
                drifts = to_dB(drifts)

            provider = traj['provider']
            status = traj['status']
            color = PROVIDER_COLORS.get(provider, 'gray')

            xs = drifts[:-1]
            ys = drifts[1:]
            zs = list(range(len(xs)))

            if status == "STABLE":
                alpha = 0.5
                linewidth = 1.0
                stable_count += 1
            else:
                alpha = 0.8
                linewidth = 2.0
                volatile_count += 1

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
                end_color = 'cyan' if status == "STABLE" else 'red'
                end_marker = 'o' if status == "STABLE" else 'X'
                ax.scatter([xs[-1]], [ys[-1]], [zs[-1]], color=end_color, s=50, alpha=0.9,
                          marker=end_marker)

        # Event Horizon Cylinder (Coherence Boundary)
        eh_val = to_dB(EVENT_HORIZON) if use_dB else EVENT_HORIZON
        max_turns = 15
        theta_cyl = np.linspace(0, 2*np.pi, 50)
        z_cyl = np.linspace(0, max_turns, 20)
        Theta_cyl, Z_cyl = np.meshgrid(theta_cyl, z_cyl)
        X_cyl = eh_val * np.cos(Theta_cyl)
        Y_cyl = eh_val * np.sin(Theta_cyl)
        ax.plot_surface(X_cyl, Y_cyl, Z_cyl, alpha=0.15, color='red', linewidth=0)

        if use_dB:
            max_drift = 20
            ax_min = -20
        else:
            max_drift = 4
            ax_min = 0

        ax.set_xlabel(f'Drift[N]{scale_label}', fontsize=10, labelpad=5)
        ax.set_ylabel(f'Drift[N+1]{scale_label}', fontsize=10, labelpad=5)
        ax.set_zlabel('Turn', fontsize=10, labelpad=5)
        ax.set_title(f'3D BASIN: {title_suffix}\n(STABLE: {stable_count}, VOLATILE: {volatile_count})',
                    fontsize=12, fontweight='bold')

        ax.set_xlim(ax_min, max_drift)
        ax.set_ylim(ax_min, max_drift)
        ax.set_zlim(0, max_turns)
        ax.view_init(elev=20, azim=45)

    scale_note = " [dB Scale]" if use_dB else ""
    fig.suptitle(f'Run {run_id}: Identity Attractor Basin{scale_note}\n(Red Cylinder = Coherence Boundary at {EVENT_HORIZON})',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    suffix = "_dB" if use_dB else ""
    plt.savefig(output_dir / f'run{run_id}_3d_basin{suffix}.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_3d_basin{suffix}.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_3d_basin{suffix}.png + .svg")
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
    ax1.axvline(x=EVENT_HORIZON, color='red', linestyle=':', alpha=0.5, label=f'Coherence Boundary ({EVENT_HORIZON})')
    ax1.set_xlabel('Baseline Drift', fontsize=12)
    ax1.set_ylabel('Max Drift', fontsize=12)
    ax1.set_title('Baseline vs Max Drift by Provider', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 4)
    ax1.set_ylim(0, 4)

    # Right: STABLE vs VOLATILE distribution
    ax2 = axes[1]
    stable_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'STABLE']
    volatile_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'VOLATILE']

    bins = np.linspace(0, 3, 20)
    if stable_baselines:
        ax2.hist(stable_baselines, bins=bins, alpha=0.7, color='cyan',
                label=f'STABLE (n={len(stable_baselines)})', edgecolor='white')
    if volatile_baselines:
        ax2.hist(volatile_baselines, bins=bins, alpha=0.7, color='red',
                label=f'VOLATILE (n={len(volatile_baselines)})', edgecolor='white')

    # Draw coherence boundary
    ax2.axvline(x=EVENT_HORIZON, color='black', linestyle='--', linewidth=2,
               label=f'Coherence Boundary ({EVENT_HORIZON})')

    ax2.set_xlabel('Baseline Drift', fontsize=12)
    ax2.set_ylabel('Count', fontsize=12)
    ax2.set_title('Identity Basin: STABLE vs VOLATILE Distribution', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right')
    ax2.grid(True, alpha=0.3, axis='y')

    fig.suptitle(f'Run {run_id}: Identity Stability Analysis', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_stability_basin.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: run{run_id}_stability_basin.png")
    plt.close()

def plot_fft_spectral(trajectories, output_dir, run_id):
    """FFT spectral analysis of drift sequences by provider."""
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # Group trajectories by provider
    provider_spectra = defaultdict(list)

    for traj in trajectories:
        drifts = np.array(traj['drifts'])
        if len(drifts) < 4:
            continue

        # Compute FFT
        n = len(drifts)
        # Remove DC component (mean)
        drifts_centered = drifts - np.mean(drifts)
        fft_vals = fft(drifts_centered)
        freqs = fftfreq(n, d=1.0)  # 1 sample per turn

        # Only positive frequencies
        pos_mask = freqs >= 0
        freqs_pos = freqs[pos_mask]
        magnitude = np.abs(fft_vals[pos_mask])
        # Convert to dB
        magnitude_dB = 20 * np.log10(magnitude + 1e-10)

        provider_spectra[traj['provider']].append({
            'freqs': freqs_pos,
            'magnitude_dB': magnitude_dB,
            'ship': traj['ship']
        })

    # Plot by provider
    providers = ['claude', 'gpt', 'gemini', 'grok']

    for idx, provider in enumerate(providers):
        ax = axes[idx // 2, idx % 2]

        if provider not in provider_spectra or not provider_spectra[provider]:
            ax.text(0.5, 0.5, f'No {provider.title()} data', ha='center', va='center',
                   fontsize=14, transform=ax.transAxes)
            ax.set_title(f'{provider.upper()}', fontsize=14, fontweight='bold')
            continue

        color = PROVIDER_COLORS.get(provider, 'gray')

        # Average spectrum across all trajectories for this provider
        all_mags = []
        common_freqs = None

        for spec in provider_spectra[provider]:
            if common_freqs is None:
                common_freqs = spec['freqs']
            # Interpolate to common frequency grid if needed
            if len(spec['freqs']) == len(common_freqs):
                all_mags.append(spec['magnitude_dB'])

        if all_mags:
            avg_mag = np.mean(all_mags, axis=0)
            std_mag = np.std(all_mags, axis=0)

            ax.fill_between(common_freqs, avg_mag - std_mag, avg_mag + std_mag,
                           alpha=0.3, color=color)
            ax.plot(common_freqs, avg_mag, color=color, linewidth=2,
                   label=f'Mean (n={len(all_mags)})')

            # Plot individual trajectories faintly
            for spec in provider_spectra[provider][:10]:  # Limit to 10 for clarity
                if len(spec['freqs']) == len(common_freqs):
                    ax.plot(spec['freqs'], spec['magnitude_dB'], color=color, alpha=0.15, linewidth=0.5)

        ax.set_xlabel('Frequency (cycles/turn)', fontsize=11)
        ax.set_ylabel('Magnitude (dB)', fontsize=11)
        ax.set_title(f'{provider.upper()} ({len(provider_spectra[provider])} sequences)',
                    fontsize=14, fontweight='bold')
        ax.legend(loc='upper right')
        ax.grid(True, alpha=0.3)
        ax.set_xlim(0, 0.5)  # Nyquist frequency
        ax.set_ylim(-50, 20)

    fig.suptitle(f'Run {run_id}: FFT Spectral Analysis - Identity Frequency Content\n' +
                '(Low freq = gradual drift, High freq = rapid oscillation)',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_fft_spectral.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: run{run_id}_fft_spectral.png")
    plt.close()

def create_interactive_html(trajectories, output_dir, run_id):
    """Create interactive Plotly visualizations."""
    if not PLOTLY_AVAILABLE:
        print("  Skipping HTML export (plotly not installed)")
        return

    # 3D Basin with Event Horizon cylinder
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

        width = 2 if status == "STABLE" else 4

        fig.add_trace(go.Scatter3d(
            x=xs_s, y=ys_s, z=zs_s,
            mode='lines',
            line=dict(color=color, width=width),
            name=f"{traj['ship']} ({status})",
            hovertemplate=f"Ship: {traj['ship']}<br>Provider: {provider}<br>Status: {status}<extra></extra>"
        ))

    # Add Event Horizon cylinder
    theta_cyl = np.linspace(0, 2*np.pi, 50)
    z_cyl = np.linspace(0, 15, 20)
    Theta_cyl, Z_cyl = np.meshgrid(theta_cyl, z_cyl)
    X_cyl = EVENT_HORIZON * np.cos(Theta_cyl)
    Y_cyl = EVENT_HORIZON * np.sin(Theta_cyl)

    fig.add_trace(go.Surface(
        x=X_cyl, y=Y_cyl, z=Z_cyl,
        opacity=0.2,
        colorscale=[[0, 'red'], [1, 'red']],
        showscale=False,
        name='Coherence Boundary'
    ))

    fig.update_layout(
        title=f"Run {run_id}: Interactive 3D Identity Basin<br>(Red cylinder = Coherence Boundary at {EVENT_HORIZON})",
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
        width = 1.5 if status == "STABLE" else 3

        fig2.add_trace(go.Scatter(
            x=xs_s, y=ys_s,
            mode='lines',
            line=dict(color=color, width=width),
            name=f"{traj['ship']} ({status})"
        ))

    # Event horizon circle
    theta = np.linspace(0, 2*np.pi, 100)
    fig2.add_trace(go.Scatter(
        x=EVENT_HORIZON * np.cos(theta), y=EVENT_HORIZON * np.sin(theta),
        mode='lines',
        line=dict(color='red', width=3, dash='dash'),
        name=f'Coherence Boundary ({EVENT_HORIZON})'
    ))

    # Identity attractor at center
    fig2.add_trace(go.Scatter(
        x=[0], y=[0],
        mode='markers',
        marker=dict(color='gold', size=15, symbol='star'),
        name='Identity Attractor'
    ))

    fig2.update_layout(
        title=f"Run {run_id}: Interactive Vortex View<br>(Inside boundary = STABLE, Outside = VOLATILE)",
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
    parser.add_argument('--dB', action='store_true', help='Use decibel scaling for visualizations')
    parser.add_argument('--type', type=str, choices=['phase', 'vortex', '3d', 'stability', 'fft', 'html'],
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
    print(f"Scale: {'Decibel (dB)' if args.dB else 'Linear'}")

    # Load data
    with open(data_file, encoding='utf-8') as f:
        data = json.load(f)

    trajectories = extract_trajectories(data)

    stable = sum(1 for t in trajectories if t['status'] == "STABLE")
    volatile = sum(1 for t in trajectories if t['status'] == "VOLATILE")
    unknown = len(trajectories) - stable - volatile
    print(f"Trajectories: {len(trajectories)} (STABLE: {stable}, VOLATILE: {volatile}, UNKNOWN: {unknown})")

    # Create output directory
    run_output_dir = OUTPUT_DIR / f"run{run_id}"
    run_output_dir.mkdir(parents=True, exist_ok=True)
    print(f"Output: {run_output_dir}")
    print("-" * 70)

    # Generate visualizations
    if args.type:
        viz_types = [args.type]
    elif args.all:
        viz_types = ['phase', 'vortex', '3d', 'stability', 'fft', 'html']
    else:
        viz_types = ['phase', 'vortex', '3d', 'stability', 'fft', 'html']

    print("\nGenerating visualizations...")

    if 'phase' in viz_types:
        plot_phase_portrait(trajectories, run_output_dir, run_id, use_dB=args.dB)

    if 'vortex' in viz_types:
        plot_vortex(trajectories, run_output_dir, run_id, use_dB=args.dB)

    if '3d' in viz_types:
        plot_3d_basin(trajectories, run_output_dir, run_id, use_dB=args.dB)

    if 'stability' in viz_types:
        plot_stability_basin(trajectories, run_output_dir, run_id)

    if 'fft' in viz_types:
        plot_fft_spectral(trajectories, run_output_dir, run_id)

    if 'html' in viz_types:
        create_interactive_html(trajectories, run_output_dir, run_id)

    print("\n" + "-" * 70)
    print("COMPLETE!")
    print(f"All outputs in: {run_output_dir}")
    print("=" * 70)

if __name__ == "__main__":
    main()
