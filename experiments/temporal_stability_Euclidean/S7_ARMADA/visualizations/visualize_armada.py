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
7. Radar Plots (provider fingerprints, pillar comparisons)
"""

import argparse
import json
import sys
import subprocess
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
RESULTS_DIR = BASE_DIR / "0_results" / "runs"
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
# VISUALIZATION EXCLUSIONS (per-run appropriateness)
# =============================================================================
# Some experiments collect different data types. Exclude inappropriate visualizations.
# Key: run_id, Value: dict with excluded viz types and reason

VISUALIZATION_EXCLUSIONS = {
    "010": {
        "stability": "Cognitive oscilloscope experiment - no stability data collected (keyword-based drift 0-1.0)",
        "fft": "Keyword-based drift not suitable for spectral analysis"
    },
    # Run 008 is a stress test - stability is valid but shows all VOLATILE (expected)
    # Add more exclusions as needed
}

def should_skip_visualization(run_id: str, viz_type: str) -> tuple:
    """Check if a visualization type should be skipped for a given run.

    Returns: (should_skip: bool, reason: str or None)
    """
    if run_id in VISUALIZATION_EXCLUSIONS:
        exclusions = VISUALIZATION_EXCLUSIONS[run_id]
        if viz_type in exclusions:
            return True, exclusions[viz_type]
    return False, None

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
    """Scan results directory for available run data, including legacy_runs/."""
    runs = {}

    if not RESULTS_DIR.exists():
        return runs

    # Search both main directory and legacy_runs subdirectory
    search_dirs = [RESULTS_DIR]
    legacy_dir = RESULTS_DIR / "legacy_runs"
    if legacy_dir.exists():
        search_dirs.append(legacy_dir)

    for search_dir in search_dirs:
        for f in search_dir.glob("S7_run_*.json"):
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
        for f in search_dir.glob("S7_run_*_prep*.json"):
            name = f.stem
            parts = name.split("_")
            if len(parts) >= 3:
                run_key = f"{parts[2]}_prep"
                if run_key not in runs:
                    runs[run_key] = []
                runs[run_key].append(f)

        # Also check for older armada format (S7_armada_run_*)
        for f in search_dir.glob("S7_armada_run_*.json"):
            name = f.stem
            parts = name.split("_")
            if len(parts) >= 4:
                run_num = parts[3].zfill(3)  # Normalize to 3 digits
                if run_num not in runs:
                    runs[run_num] = []
                runs[run_num].append(f)

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

    # Format 5: Run 012/014 list-based format
    # results is a LIST of ship objects with 'turns' or 'phases' arrays
    if isinstance(results, list):
        for ship_data in results:
            if not isinstance(ship_data, dict):
                continue

            ship_name = ship_data.get('ship', ship_data.get('model', 'unknown'))
            provider = ship_data.get('provider', get_provider(ship_name))

            # Try 'turns' first (Run 012 format)
            turns = ship_data.get('turns', [])

            # If no turns, try 'phases' (Run 014 rescue format)
            if not turns and 'phases' in ship_data:
                phases = ship_data['phases']
                if isinstance(phases, dict):
                    # Flatten phases (baseline, drift_induction, rescue) into single list
                    turns = []
                    for phase_name in ['baseline', 'drift_induction', 'rescue', 'post_rescue']:
                        phase_data = phases.get(phase_name, [])
                        if isinstance(phase_data, list):
                            turns.extend(phase_data)

            if not turns or not isinstance(turns, list):
                continue

            # Extract drift values from turns
            drifts = []
            for turn in turns:
                if isinstance(turn, dict):
                    # Primary: 'drift' field
                    drift = turn.get('drift')
                    if drift is not None:
                        drifts.append(drift)

            if len(drifts) >= 3:
                baseline = drifts[0]
                max_drift = max(drifts)
                status = "VOLATILE" if max_drift >= EVENT_HORIZON else "STABLE"

                trajectories.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': 'rescue',
                    'drifts': drifts,
                    'status': status,
                    'baseline': baseline
                })

        # If we found trajectories from list format, return early
        if trajectories:
            return trajectories

    # Continue with dict-based formats (must be a dict to iterate)
    if not isinstance(results, dict):
        return trajectories

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
                max_drift = max(drifts)
                # Use Event Horizon for status: VOLATILE if crossed boundary
                status = "VOLATILE" if max_drift >= EVENT_HORIZON else "STABLE"

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

        # Format 3: turns array (Run 010+ recursive format)
        # Looks for 'drift' field, falling back to various legacy field names
        if 'turns' in ship_data and isinstance(ship_data['turns'], list):
            turns = ship_data['turns']
            drifts = []
            for turn in turns:
                if isinstance(turn, dict):
                    # Primary: 'drift' field
                    # Fallbacks for legacy data: drift_skylar (equal weights), drift_lucian, drift_data.drift
                    drift = turn.get('drift')
                    if drift is None:
                        drift = turn.get('drift_skylar')  # Legacy Run 010 field
                    if drift is None:
                        drift = turn.get('drift_lucian')  # Alternative weighting
                    if drift is None and 'drift_data' in turn:
                        drift = turn['drift_data'].get('drift')
                    if drift is not None:
                        drifts.append(drift)

            if len(drifts) >= 3:
                baseline = drifts[0]
                max_drift = max(drifts)
                status = "VOLATILE" if max_drift >= EVENT_HORIZON else "STABLE"

                trajectories.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': 'recursive',
                    'drifts': drifts,
                    'status': status,
                    'baseline': baseline
                })

    # Use pre-extracted trajectories if available
    if 'trajectories_for_3d' in data:
        for t in data['trajectories_for_3d']:
            # Normalize: some runs use 'drift_sequence' instead of 'drifts'
            if 'drift_sequence' in t and 'drifts' not in t:
                t['drifts'] = t['drift_sequence']
            # Recalculate status based on Event Horizon (ignore source status)
            drifts = t.get('drifts', [])
            if drifts:
                max_drift = max(drifts)
                t['status'] = "VOLATILE" if max_drift >= EVENT_HORIZON else "STABLE"
            else:
                t['status'] = "UNKNOWN"
            trajectories.append(t)

    # Format 5: Run 013 Boundary Mapping (ships/probes structure)
    # Structure: ships[] -> probes[] -> drift
    if 'ships' in data and isinstance(data['ships'], list):
        for ship_data in data['ships']:
            if not isinstance(ship_data, dict):
                continue

            ship_name = ship_data.get('ship', ship_data.get('model', 'unknown'))
            provider = ship_data.get('provider', get_provider(ship_name))
            probes = ship_data.get('probes', [])

            if not probes or not isinstance(probes, list):
                continue

            # Extract drift values from probes
            drifts = []
            for probe in probes:
                if isinstance(probe, dict):
                    drift = probe.get('drift')
                    if drift is not None:
                        drifts.append(drift)

            if len(drifts) >= 3:
                baseline = drifts[0]
                max_drift = max(drifts)
                status = "VOLATILE" if max_drift >= EVENT_HORIZON else "STABLE"

                trajectories.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': 'boundary',
                    'drifts': drifts,
                    'status': status,
                    'baseline': baseline
                })

    # Format 4: Run 011 Persona A/B Comparison (control_fleet / persona_fleet arrays)
    for fleet_key in ['control_fleet', 'persona_fleet']:
        fleet_data = data.get(fleet_key, [])
        if not isinstance(fleet_data, list):
            continue

        for ship_data in fleet_data:
            if not isinstance(ship_data, dict):
                continue

            ship_name = ship_data.get('ship', 'unknown')
            provider = ship_data.get('provider', get_provider(ship_name))
            turns = ship_data.get('turns', [])

            if not turns:
                continue

            # Extract drift values from turns
            drifts = []
            for turn in turns:
                if isinstance(turn, dict) and 'drift' in turn:
                    drifts.append(turn['drift'])

            if len(drifts) >= 3:
                baseline = drifts[0]
                max_drift = max(drifts)
                status = "VOLATILE" if max_drift >= EVENT_HORIZON else "STABLE"

                # Add fleet suffix to distinguish control vs persona
                fleet_label = ship_data.get('fleet', fleet_key.replace('_fleet', '').upper())

                trajectories.append({
                    'ship': f"{ship_name} ({fleet_label})",
                    'provider': provider,
                    'sequence': fleet_label.lower(),
                    'drifts': drifts,
                    'status': status,
                    'baseline': baseline
                })

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

def plot_phase_portrait(trajectories, output_dir, run_id, use_dB=False, zoom_scale=None):
    """Phase portrait: drift[N] vs drift[N+1] - Raw vs Smoothed.

    NOTE: dB scaling is DISABLED. It distorts the phase space geometry
    by compressing small values to extreme negatives.

    Args:
        zoom_scale: If provided, use this as the axis max instead of 4.0
    """
    # Ignore dB flag - it distorts the geometry
    if use_dB:
        print("  NOTE: dB scaling disabled for phase portrait (distorts geometry)")
        return  # Skip dB version entirely

    fig, axes = plt.subplots(1, 2, figsize=(18, 9))

    scale_label = ""
    eh_val = EVENT_HORIZON
    ax_max = zoom_scale if zoom_scale else 4

    for ax_idx, (ax, smoothed) in enumerate(zip(axes, [False, True])):
        title_suffix = "SMOOTHED (B-Spline)" if smoothed else "RAW DATA"

        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue

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

        # Axis limits (linear scale only)
        ax_min = 0

        ax.plot([ax_min, ax_max], [ax_min, ax_max], 'k--', alpha=0.3, label='No change')
        ax.fill_between([ax_min, ax_max], [ax_min, ax_max], [ax_max, ax_max], alpha=0.08, color='red')
        ax.fill_between([ax_min, ax_max], [ax_min, ax_min], [ax_min, ax_max], alpha=0.08, color='green')
        ax.axvline(x=eh_val, color='red', linestyle=':', alpha=0.5, label=f'Coherence Boundary ({EVENT_HORIZON})')
        ax.axhline(y=eh_val, color='red', linestyle=':', alpha=0.5)

        ax.set_xlabel('Drift at Turn N', fontsize=12)
        ax.set_ylabel('Drift at Turn N+1', fontsize=12)
        zoom_label = " [ZOOMED]" if zoom_scale else ""
        ax.set_title(f'PHASE PORTRAIT: {title_suffix}{zoom_label}', fontsize=14, fontweight='bold')
        ax.set_xlim(ax_min, ax_max)
        ax.set_ylim(ax_min, ax_max)
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)

        # Add legend (on right/smoothed panel only for cleaner look)
        if smoothed:
            from matplotlib.lines import Line2D
            legend_handles = []
            # Provider colors
            provider_names = {'claude': 'Claude', 'gpt': 'GPT', 'gemini': 'Gemini', 'grok': 'Grok'}
            providers_in_data = set(t['provider'] for t in trajectories)
            for provider in sorted(providers_in_data):
                color = PROVIDER_COLORS.get(provider, 'gray')
                legend_handles.append(Line2D([0], [0], color=color, linewidth=2,
                                            label=provider_names.get(provider, provider.title())))
            # Marker explanations
            legend_handles.append(Line2D([0], [0], marker='D', color='w', markerfacecolor='lime',
                                        markersize=8, label='Start', markeredgecolor='darkgreen'))
            legend_handles.append(Line2D([0], [0], marker='o', color='w', markerfacecolor='cyan',
                                        markersize=8, label='End (STABLE)', markeredgecolor='black'))
            legend_handles.append(Line2D([0], [0], marker='X', color='w', markerfacecolor='red',
                                        markersize=10, label='End (VOLATILE)', markeredgecolor='black'))
            # Region explanations
            legend_handles.append(Line2D([0], [0], color='red', linestyle=':', linewidth=2,
                                        label=f'Event Horizon ({EVENT_HORIZON})'))
            ax.legend(handles=legend_handles, loc='upper left', fontsize=8, framealpha=0.9)

    fig.suptitle(f'Run {run_id}: Identity Flow', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_phase_portrait.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_phase_portrait.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_phase_portrait.png + .svg")
    plt.close()

def plot_vortex(trajectories, output_dir, run_id, use_dB=False, zoom_scale=None):
    """Vortex/drain view - polar spiral visualization.

    NOTE: dB scaling is DISABLED for vortex view. The polar coordinate
    geometry is distorted by logarithmic transformation. Linear scale only.

    Args:
        zoom_scale: If provided, use this as the axis limit instead of auto-calculating
    """
    # Ignore dB flag for vortex - it distorts the polar geometry
    if use_dB:
        print("  NOTE: dB scaling disabled for vortex view (distorts polar geometry)")
        return  # Skip dB version entirely

    fig, axes = plt.subplots(1, 2, figsize=(18, 9))

    scale_label = ""
    forced_ax_lim = zoom_scale  # Will be used if set

    # Collect all coordinates to determine auto-scale
    all_coords = []

    # Track providers for legend
    providers_seen = set()

    for ax_idx, (ax, smoothed) in enumerate(zip(axes, [False, True])):
        title_suffix = "SMOOTHED" if smoothed else "RAW"

        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue

            provider = traj['provider']
            providers_seen.add(provider)
            status = traj['status']
            color = PROVIDER_COLORS.get(provider, 'gray')

            turns = len(drifts)
            angles = np.linspace(0, 2*np.pi * (turns/5), turns)
            radii = np.array(drifts)

            xs = radii * np.cos(angles)
            ys = radii * np.sin(angles)

            # Collect for auto-scaling (only on first pass)
            if ax_idx == 0:
                all_coords.extend(xs)
                all_coords.extend(ys)

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

        # Coherence Boundary circle (Event Horizon)
        eh_radius = EVENT_HORIZON
        theta = np.linspace(0, 2*np.pi, 100)
        ax.plot(eh_radius * np.cos(theta), eh_radius * np.sin(theta), 'r--', linewidth=2.5, alpha=0.7,
               label='Event Horizon (1.23)')
        ax.scatter([0], [0], color='gold', s=300, marker='*', zorder=15, label='Identity Attractor')

        # Add legend entries for providers
        for provider in sorted(providers_seen):
            color = PROVIDER_COLORS.get(provider, 'gray')
            ax.plot([], [], color=color, linewidth=2, label=provider.upper())

        # Legend entries for markers
        ax.scatter([], [], color='lime', s=35, marker='D', edgecolors='darkgreen', label='Start')
        ax.scatter([], [], color='cyan', s=45, marker='o', edgecolors='black', label='End (STABLE)')
        ax.scatter([], [], color='red', s=45, marker='X', edgecolors='black', label='End (VOLATILE)')

        # AUTO-SCALE: Determine axis limits from data (or use forced zoom)
        if forced_ax_lim:
            ax_lim = forced_ax_lim
        elif all_coords:
            max_coord = max(abs(min(all_coords)), abs(max(all_coords)))
            # Add 20% padding, ensure Event Horizon is visible, and round up nicely
            ax_lim = max(max_coord * 1.2, EVENT_HORIZON * 1.3)
            # Round to nice number (0.5, 1, 1.5, 2, 2.5, 3, 4, 5, etc.)
            if ax_lim <= 1.5:
                ax_lim = 1.5
            elif ax_lim <= 2:
                ax_lim = 2
            elif ax_lim <= 3:
                ax_lim = 3
            elif ax_lim <= 4:
                ax_lim = 4
            else:
                ax_lim = np.ceil(ax_lim)
        else:
            ax_lim = 4  # Default fallback

        # Reference circles - adaptive based on scale
        if ax_lim <= 2:
            radii_ref = [0.25, 0.5, 0.75, 1.0, 1.25, 1.5]
        elif ax_lim <= 3:
            radii_ref = [0.5, 1.0, 1.5, 2.0, 2.5]
        else:
            radii_ref = [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5]

        for r in radii_ref:
            if r < ax_lim:
                circle = plt.Circle((0, 0), r, fill=False, color='gray', alpha=0.2, linestyle=':')
                ax.add_patch(circle)

        ax.set_xlim(-ax_lim, ax_lim)
        ax.set_ylim(-ax_lim, ax_lim)
        ax.set_aspect('equal')
        ax.set_xlabel(f'X (drift * cos(angle)){scale_label}', fontsize=11)
        ax.set_ylabel(f'Y (drift * sin(angle)){scale_label}', fontsize=11)
        zoom_label = " [ZOOMED]" if forced_ax_lim else ""
        ax.set_title(f'VORTEX VIEW: {title_suffix}{zoom_label}', fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)

        # Add legend (only on right plot)
        if smoothed:
            ax.legend(loc='upper right', fontsize=8, framealpha=0.9)

    fig.suptitle(f'Run {run_id}: Looking Into the Identity Drain\n(Inside = STABLE, Outside = VOLATILE)',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_vortex.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_vortex.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_vortex.png + .svg")
    plt.close()


def plot_vortex_x4(trajectories, output_dir, run_id, zoom_scale=None):
    """Vortex view split by provider - 2x2 grid showing each provider's field separately.

    This reveals the individual 'magnetic field' patterns of each provider.
    """
    providers = ['claude', 'gpt', 'gemini', 'grok']
    provider_names = {'claude': 'CLAUDE', 'gpt': 'GPT', 'gemini': 'GEMINI', 'grok': 'GROK'}

    fig, axes = plt.subplots(2, 2, figsize=(16, 16))
    axes = axes.flatten()

    # Group trajectories by provider
    by_provider = defaultdict(list)
    for traj in trajectories:
        by_provider[traj['provider']].append(traj)

    # Calculate global scale from all data (or use forced zoom)
    if zoom_scale:
        ax_lim = zoom_scale
    else:
        all_coords = []
        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue
            turns = len(drifts)
            angles = np.linspace(0, 2*np.pi * (turns/5), turns)
            xs = drifts * np.cos(angles)
            ys = drifts * np.sin(angles)
            all_coords.extend(xs)
            all_coords.extend(ys)

        if all_coords:
            max_coord = max(abs(min(all_coords)), abs(max(all_coords)))
            ax_lim = max(max_coord * 1.2, EVENT_HORIZON * 1.3)
            if ax_lim <= 2:
                ax_lim = 2
            elif ax_lim <= 3:
                ax_lim = 3
            elif ax_lim <= 4:
                ax_lim = 4
            else:
                ax_lim = np.ceil(ax_lim)
        else:
            ax_lim = 4

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        color = PROVIDER_COLORS.get(provider, 'gray')
        provider_trajs = by_provider.get(provider, [])

        stable_count = 0
        volatile_count = 0

        for traj in provider_trajs:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue

            status = traj['status']
            if status == "STABLE":
                stable_count += 1
            else:
                volatile_count += 1

            turns = len(drifts)
            angles = np.linspace(0, 2*np.pi * (turns/5), turns)
            radii = np.array(drifts)

            xs = radii * np.cos(angles)
            ys = radii * np.sin(angles)

            alpha = 0.5 if status == "STABLE" else 0.8
            linewidth = 1.0 if status == "STABLE" else 2.0

            # Smooth version
            xs_smooth, ys_smooth = smooth_trajectory_2d(xs, ys, num_points=80)
            ax.plot(xs_smooth, ys_smooth, color=color, alpha=alpha, linewidth=linewidth)
            ax.scatter(xs, ys, color=color, s=10, alpha=0.3, edgecolors='white', linewidths=0.2)

            # Start/end markers
            ax.scatter(xs[0], ys[0], color='lime', s=40, alpha=0.9, zorder=10,
                      marker='D', edgecolors='darkgreen', linewidths=1)
            end_color = 'cyan' if status == "STABLE" else 'red'
            end_marker = 'o' if status == "STABLE" else 'X'
            ax.scatter(xs[-1], ys[-1], color=end_color, s=50, alpha=0.9, zorder=10,
                      marker=end_marker, edgecolors='black', linewidths=1)

        # Event Horizon circle
        theta = np.linspace(0, 2*np.pi, 100)
        ax.plot(EVENT_HORIZON * np.cos(theta), EVENT_HORIZON * np.sin(theta),
               'r--', linewidth=2.5, alpha=0.7)

        # Identity Attractor
        ax.scatter([0], [0], color='gold', s=400, marker='*', zorder=15)

        # Reference circles
        for r in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]:
            if r < ax_lim:
                circle = plt.Circle((0, 0), r, fill=False, color='gray', alpha=0.15, linestyle=':')
                ax.add_patch(circle)

        ax.set_xlim(-ax_lim, ax_lim)
        ax.set_ylim(-ax_lim, ax_lim)
        ax.set_aspect('equal')
        ax.set_xlabel('X (drift * cos(angle))', fontsize=10)
        ax.set_ylabel('Y (drift * sin(angle))', fontsize=10)
        ax.set_title(f'{provider_names[provider]}\n(n={len(provider_trajs)}, STABLE: {stable_count}, VOLATILE: {volatile_count})',
                    fontsize=14, fontweight='bold', color=color)
        ax.grid(True, alpha=0.3)

    fig.suptitle(f'Run {run_id}: Identity Field by Provider\n(Separated view reveals individual field geometries)',
                fontsize=18, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_vortex_x4.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_vortex_x4.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_vortex_x4.png + .svg")
    plt.close()


def plot_vortex_by_company(trajectories, output_dir, run_id, zoom_scale=None):
    """Generate individual vortex plots per company, showing all models from that company.

    Creates: run{id}_vortex_Claude.png, run{id}_vortex_OpenAI.png,
             run{id}_vortex_Google.png, run{id}_vortex_Grok.png
    """
    # Map providers to company names for filenames
    provider_to_company = {
        'claude': 'Claude',
        'gpt': 'OpenAI',
        'gemini': 'Google',
        'grok': 'Grok'
    }

    providers = ['claude', 'gpt', 'gemini', 'grok']

    # Group trajectories by provider, then by ship name
    by_provider = defaultdict(list)
    for traj in trajectories:
        by_provider[traj['provider']].append(traj)

    # Calculate global scale from all data (or use forced zoom)
    if zoom_scale:
        ax_lim = zoom_scale
    else:
        all_coords = []
        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue
            turns = len(drifts)
            angles = np.linspace(0, 2*np.pi * (turns/5), turns)
            xs = drifts * np.cos(angles)
            ys = drifts * np.sin(angles)
            all_coords.extend(xs)
            all_coords.extend(ys)

        if all_coords:
            max_coord = max(abs(min(all_coords)), abs(max(all_coords)))
            ax_lim = max(max_coord * 1.2, EVENT_HORIZON * 1.3)
            if ax_lim <= 2:
                ax_lim = 2
            elif ax_lim <= 3:
                ax_lim = 3
            elif ax_lim <= 4:
                ax_lim = 4
            else:
                ax_lim = np.ceil(ax_lim)
        else:
            ax_lim = 4

    for provider in providers:
        company_name = provider_to_company[provider]
        provider_trajs = by_provider.get(provider, [])

        if not provider_trajs:
            print(f"  Skipping {company_name} (no data)")
            continue

        # Group by individual ship/model
        by_ship = defaultdict(list)
        for traj in provider_trajs:
            by_ship[traj['ship']].append(traj)

        # Determine subplot grid based on number of models
        n_models = len(by_ship)
        if n_models == 0:
            continue
        elif n_models <= 2:
            rows, cols = 1, n_models
            fig_width, fig_height = 8 * n_models, 8
        elif n_models <= 4:
            rows, cols = 2, 2
            fig_width, fig_height = 16, 16
        elif n_models <= 6:
            rows, cols = 2, 3
            fig_width, fig_height = 18, 12
        elif n_models <= 9:
            rows, cols = 3, 3
            fig_width, fig_height = 18, 18
        else:
            rows, cols = 4, 4
            fig_width, fig_height = 20, 20

        fig, axes = plt.subplots(rows, cols, figsize=(fig_width, fig_height))
        if n_models == 1:
            axes = np.array([axes])
        axes = axes.flatten()

        color = PROVIDER_COLORS.get(provider, 'gray')

        for idx, (ship_name, ship_trajs) in enumerate(sorted(by_ship.items())):
            if idx >= len(axes):
                break

            ax = axes[idx]

            stable_count = 0
            volatile_count = 0

            for traj in ship_trajs:
                drifts = np.array(traj['drifts'])
                if len(drifts) < 3:
                    continue

                status = traj['status']
                if status == "STABLE":
                    stable_count += 1
                else:
                    volatile_count += 1

                turns = len(drifts)
                angles = np.linspace(0, 2*np.pi * (turns/5), turns)
                radii = np.array(drifts)

                xs = radii * np.cos(angles)
                ys = radii * np.sin(angles)

                alpha = 0.6 if status == "STABLE" else 0.9
                linewidth = 1.5 if status == "STABLE" else 2.5

                # Smooth version
                xs_smooth, ys_smooth = smooth_trajectory_2d(xs, ys, num_points=80)
                ax.plot(xs_smooth, ys_smooth, color=color, alpha=alpha, linewidth=linewidth)
                ax.scatter(xs, ys, color=color, s=12, alpha=0.4, edgecolors='white', linewidths=0.2)

                # Start/end markers
                ax.scatter(xs[0], ys[0], color='lime', s=50, alpha=0.9, zorder=10,
                          marker='D', edgecolors='darkgreen', linewidths=1.5)
                end_color = 'cyan' if status == "STABLE" else 'red'
                end_marker = 'o' if status == "STABLE" else 'X'
                ax.scatter(xs[-1], ys[-1], color=end_color, s=60, alpha=0.9, zorder=10,
                          marker=end_marker, edgecolors='black', linewidths=1.5)

            # Event Horizon circle
            theta = np.linspace(0, 2*np.pi, 100)
            ax.plot(EVENT_HORIZON * np.cos(theta), EVENT_HORIZON * np.sin(theta),
                   'r--', linewidth=2.5, alpha=0.7)

            # Identity Attractor
            ax.scatter([0], [0], color='gold', s=400, marker='*', zorder=15)

            # Reference circles
            for r in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0]:
                if r < ax_lim:
                    circle = plt.Circle((0, 0), r, fill=False, color='gray', alpha=0.15, linestyle=':')
                    ax.add_patch(circle)

            ax.set_xlim(-ax_lim, ax_lim)
            ax.set_ylim(-ax_lim, ax_lim)
            ax.set_aspect('equal')
            ax.set_xlabel('X (drift * cos(angle))', fontsize=10)
            ax.set_ylabel('Y (drift * sin(angle))', fontsize=10)

            # Truncate long ship names for title
            display_name = ship_name if len(ship_name) <= 25 else ship_name[:22] + '...'
            ax.set_title(f'{display_name}\n(n={len(ship_trajs)}, S: {stable_count}, V: {volatile_count})',
                        fontsize=11, fontweight='bold')
            ax.grid(True, alpha=0.3)

        # Hide unused subplots
        for idx in range(len(by_ship), len(axes)):
            axes[idx].set_visible(False)

        fig.suptitle(f'Run {run_id}: {company_name} Identity Field by Model\n' +
                    f'(Coherence Boundary = {EVENT_HORIZON})',
                    fontsize=18, fontweight='bold', color=color, y=1.02)

        plt.tight_layout()
        plt.savefig(output_dir / f'run{run_id}_vortex_{company_name}.png', dpi=300, bbox_inches='tight')
        plt.savefig(output_dir / f'run{run_id}_vortex_{company_name}.svg', format='svg', bbox_inches='tight')
        print(f"  Saved: run{run_id}_vortex_{company_name}.png + .svg")
        plt.close()


def plot_3d_basin(trajectories, output_dir, run_id, use_dB=False, show_cylinder=False, zoom_scale=None):
    """3D phase space basin visualization.

    Args:
        show_cylinder: If True, show Event Horizon cylinder overlay (default: False)
        zoom_scale: If provided, use this as the axis max instead of auto-calculating

    NOTE: dB scaling is DISABLED. Linear scale preserves geometry.
    """
    from matplotlib.lines import Line2D  # Import at function scope for legend

    # Ignore dB flag - it distorts the geometry
    if use_dB:
        print("  NOTE: dB scaling disabled for 3D basin (distorts geometry)")
        return  # Skip dB version entirely

    fig = plt.figure(figsize=(18, 8))

    # Track which providers are present for legend
    providers_seen = set()

    for plot_idx, smoothed in enumerate([False, True]):
        ax = fig.add_subplot(1, 2, plot_idx + 1, projection='3d')
        title_suffix = "SMOOTHED" if smoothed else "RAW"

        stable_count = 0
        volatile_count = 0

        for traj in trajectories:
            drifts = np.array(traj['drifts'])
            if len(drifts) < 3:
                continue

            provider = traj['provider']
            providers_seen.add(provider)
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

        # Event Horizon Cylinder (Coherence Boundary) - optional
        if show_cylinder:
            eh_val = EVENT_HORIZON
            max_turns = 15
            theta_cyl = np.linspace(0, 2*np.pi, 50)
            z_cyl = np.linspace(0, max_turns, 20)
            Theta_cyl, Z_cyl = np.meshgrid(theta_cyl, z_cyl)
            X_cyl = eh_val * np.cos(Theta_cyl)
            Y_cyl = eh_val * np.sin(Theta_cyl)
            ax.plot_surface(X_cyl, Y_cyl, Z_cyl, alpha=0.15, color='red', linewidth=0)

        # Compute data-driven limits for better zoom (or use forced zoom)
        if zoom_scale:
            max_drift = zoom_scale
        else:
            # Key insight: Always show enough to see the aggregate SHAPE
            # Minimum window should include Event Horizon + margin for context
            MIN_AXIS_RANGE = EVENT_HORIZON * 1.5  # ~1.85 - shows EH with room to spare

            all_xs = []
            all_ys = []
            for traj in trajectories:
                drifts = np.array(traj['drifts'])
                if len(drifts) >= 2:
                    all_xs.extend(drifts[:-1])
                    all_ys.extend(drifts[1:])

            if all_xs and all_ys:
                # Use data extent + padding
                data_max = max(max(all_xs), max(all_ys))
                max_drift = data_max * 1.15  # 15% padding beyond data
                max_drift = min(max_drift, 4)  # Cap at 4
                max_drift = max(max_drift, MIN_AXIS_RANGE)  # At least show EH context
            else:
                max_drift = MIN_AXIS_RANGE
        ax_min = 0
        max_turns = 15

        ax.set_xlabel('Drift[N]', fontsize=10, labelpad=5)
        ax.set_ylabel('Drift[N+1]', fontsize=10, labelpad=5)
        ax.set_zlabel('Turn', fontsize=10, labelpad=5)
        zoom_label = " [ZOOMED]" if zoom_scale else ""
        ax.set_title(f'3D BASIN: {title_suffix}{zoom_label}\n(STABLE: {stable_count}, VOLATILE: {volatile_count})',
                    fontsize=12, fontweight='bold')

        ax.set_xlim(ax_min, max_drift)
        ax.set_ylim(ax_min, max_drift)
        ax.set_zlim(0, max_turns)
        # Better viewing angle - closer, more overhead
        ax.view_init(elev=25, azim=35)

        # Add legend (only on right/smoothed plot for cleaner look)
        if smoothed:
            # Create legend handles for providers
            legend_handles = []
            provider_names = {'claude': 'Claude', 'gpt': 'GPT', 'gemini': 'Gemini', 'grok': 'Grok'}
            for provider in sorted(providers_seen):
                color = PROVIDER_COLORS.get(provider, 'gray')
                legend_handles.append(Line2D([0], [0], color=color, linewidth=2,
                                            label=provider_names.get(provider, provider.title())))

            # Add marker legend entries
            legend_handles.append(Line2D([0], [0], marker='D', color='w', markerfacecolor='lime',
                                        markersize=8, label='Start', markeredgecolor='darkgreen'))
            legend_handles.append(Line2D([0], [0], marker='X', color='w', markerfacecolor='red',
                                        markersize=10, label='End (VOLATILE)', markeredgecolor='black'))
            legend_handles.append(Line2D([0], [0], marker='o', color='w', markerfacecolor='cyan',
                                        markersize=8, label='End (STABLE)', markeredgecolor='black'))

            ax.legend(handles=legend_handles, loc='upper left', fontsize=9, framealpha=0.9)

    subtitle = f'(Coherence Boundary = {EVENT_HORIZON})' if show_cylinder else f'(Event Horizon at {EVENT_HORIZON})'
    fig.suptitle(f'Run {run_id}: Identity Attractor Basin\n{subtitle}',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_3d_basin.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_3d_basin.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_3d_basin.png + .svg")
    plt.close()

def plot_stability_basin(trajectories, output_dir, run_id, zoom_scale=None):
    """Stability basin: baseline vs max drift by provider."""
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))
    ax_max = zoom_scale if zoom_scale else 4

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

    ax1.plot([0, ax_max], [0, ax_max], 'k--', alpha=0.3, label='No change')
    ax1.axvline(x=EVENT_HORIZON, color='red', linestyle=':', alpha=0.5, label=f'Coherence Boundary ({EVENT_HORIZON})')
    ax1.set_xlabel('Baseline Drift', fontsize=12)
    ax1.set_ylabel('Max Drift', fontsize=12)
    zoom_label = " [ZOOMED]" if zoom_scale else ""
    ax1.set_title(f'Baseline vs Max Drift by Provider{zoom_label}', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left')
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, ax_max)
    ax1.set_ylim(0, ax_max)

    # Right: STABLE vs VOLATILE distribution (side-by-side bars to prevent overlap)
    ax2 = axes[1]
    stable_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'STABLE']
    volatile_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'VOLATILE']

    # Auto-scale bins based on actual data range (fixes Run 014 histogram bug)
    all_baselines = stable_baselines + volatile_baselines
    if all_baselines:
        bin_max = max(max(all_baselines) * 1.1, 3.0)  # At least 3.0, or 10% above max
    else:
        bin_max = 3.0
    bins = np.linspace(0, bin_max, 20)
    # Use side-by-side histogram to show both distributions clearly
    if stable_baselines or volatile_baselines:
        data_to_plot = []
        labels = []
        colors = []
        if stable_baselines:
            data_to_plot.append(stable_baselines)
            labels.append(f'STABLE (recovers, n={len(stable_baselines)})')
            colors.append('cyan')
        if volatile_baselines:
            data_to_plot.append(volatile_baselines)
            labels.append(f'VOLATILE (no recovery, n={len(volatile_baselines)})')
            colors.append('red')
        ax2.hist(data_to_plot, bins=bins, alpha=0.8, color=colors,
                label=labels, edgecolor='white', rwidth=0.85)

    # Draw coherence boundary
    ax2.axvline(x=EVENT_HORIZON, color='black', linestyle='--', linewidth=2,
               label=f'Coherence Boundary ({EVENT_HORIZON})')

    ax2.set_xlabel('Baseline Drift', fontsize=12)
    ax2.set_ylabel('Count', fontsize=12)
    ax2.set_title('Identity Basin: STABLE vs VOLATILE Distribution\n(Status = max drift < 1.23, not baseline)', fontsize=13, fontweight='bold')
    ax2.legend(loc='upper right')
    ax2.grid(True, alpha=0.3, axis='y')

    fig.suptitle(f'Run {run_id}: Identity Stability Analysis', fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_stability_basin.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: run{run_id}_stability_basin.png")
    plt.close()


def plot_pillar_analysis(trajectories, output_dir, run_id, zoom_scale=None):
    """Pillar analysis: Shows how providers cluster in angular phase space.

    This is a derived view of the identity stress test data that reveals
    structural "pillars" - angular positions where provider trajectories cluster.

    Creates 4-panel visualization:
    1. 3-Pillar structure with provider centroids
    2. Extended pillars (by individual model)
    3. Angular distribution histogram
    4. Pillar stability (distance from Event Horizon)
    """
    from matplotlib.lines import Line2D
    ax_lim = zoom_scale if zoom_scale else 4

    fig, axes = plt.subplots(2, 2, figsize=(18, 16))

    # Calculate centroid position for each provider
    # Using mean endpoint in polar coordinates (vortex space)
    provider_stats = defaultdict(lambda: {
        'xs_end': [], 'ys_end': [],  # Final positions
        'xs_start': [], 'ys_start': [],  # Start positions
        'baselines': [], 'finals': [],
        'angles_end': [], 'radii_end': [],
        'ships': defaultdict(lambda: {'xs': [], 'ys': [], 'baselines': [], 'finals': []})
    })

    for traj in trajectories:
        drifts = np.array(traj['drifts'])
        if len(drifts) < 3:
            continue

        provider = traj['provider']
        ship = traj['ship']

        turns = len(drifts)
        angles = np.linspace(0, 2*np.pi * (turns/5), turns)
        radii = np.array(drifts)

        xs = radii * np.cos(angles)
        ys = radii * np.sin(angles)

        # Store endpoint data
        provider_stats[provider]['xs_end'].append(xs[-1])
        provider_stats[provider]['ys_end'].append(ys[-1])
        provider_stats[provider]['xs_start'].append(xs[0])
        provider_stats[provider]['ys_start'].append(ys[0])
        provider_stats[provider]['baselines'].append(drifts[0])
        provider_stats[provider]['finals'].append(drifts[-1])

        # Angular position of endpoint
        angle_end = np.arctan2(ys[-1], xs[-1])
        if angle_end < 0:
            angle_end += 2 * np.pi
        provider_stats[provider]['angles_end'].append(angle_end)
        provider_stats[provider]['radii_end'].append(np.sqrt(xs[-1]**2 + ys[-1]**2))

        # Per-ship stats
        provider_stats[provider]['ships'][ship]['xs'].append(xs[-1])
        provider_stats[provider]['ships'][ship]['ys'].append(ys[-1])
        provider_stats[provider]['ships'][ship]['baselines'].append(drifts[0])
        provider_stats[provider]['ships'][ship]['finals'].append(drifts[-1])

    providers = ['claude', 'gpt', 'gemini', 'grok']
    provider_names = {'claude': 'Claude', 'gpt': 'GPT', 'gemini': 'Gemini', 'grok': 'Grok'}

    # ===== PANEL 1: 3-Pillar Structure =====
    ax1 = axes[0, 0]

    # Draw all trajectories faintly
    for traj in trajectories:
        drifts = np.array(traj['drifts'])
        if len(drifts) < 3:
            continue
        provider = traj['provider']
        color = PROVIDER_COLORS.get(provider, 'gray')

        turns = len(drifts)
        angles = np.linspace(0, 2*np.pi * (turns/5), turns)
        xs = drifts * np.cos(angles)
        ys = drifts * np.sin(angles)

        ax1.plot(xs, ys, color=color, alpha=0.15, linewidth=0.5)

    # Draw provider centroids as stars
    centroid_data = []
    for provider in providers:
        if provider not in provider_stats or not provider_stats[provider]['xs_end']:
            continue

        stats = provider_stats[provider]
        color = PROVIDER_COLORS.get(provider, 'gray')

        # Centroid of endpoints
        cx = np.mean(stats['xs_end'])
        cy = np.mean(stats['ys_end'])

        # Mean baseline and final
        mean_baseline = np.mean(stats['baselines'])
        mean_final = np.mean(stats['finals'])

        # Safety margin: how far BELOW the Event Horizon (positive = safe, negative = danger)
        safety_margin = EVENT_HORIZON - mean_baseline

        centroid_data.append({
            'provider': provider,
            'cx': cx, 'cy': cy,
            'baseline': mean_baseline,
            'final': mean_final,
            'safety_margin': safety_margin,
            'n': len(stats['xs_end'])
        })

        # Draw centroid star
        ax1.scatter([cx], [cy], color=color, s=500, marker='*',
                   edgecolors='black', linewidths=2, zorder=20,
                   label=f"{provider_names[provider]} (n={len(stats['xs_end'])})")

        # Draw line from origin to centroid
        ax1.plot([0, cx], [0, cy], color=color, linestyle='--', linewidth=2, alpha=0.5)

    # Event Horizon circle
    theta = np.linspace(0, 2*np.pi, 100)
    ax1.plot(EVENT_HORIZON * np.cos(theta), EVENT_HORIZON * np.sin(theta),
            'r--', linewidth=2.5, alpha=0.7, label=f'Coherence Boundary ({EVENT_HORIZON})')
    ax1.scatter([0], [0], color='gold', s=200, marker='*', zorder=15)

    ax1.set_xlim(-ax_lim, ax_lim)
    ax1.set_ylim(-ax_lim, ax_lim)
    ax1.set_aspect('equal')
    ax1.set_xlabel('X (drift * cos)', fontsize=11)
    ax1.set_ylabel('Y (drift * sin)', fontsize=11)
    zoom_label = " [ZOOMED]" if zoom_scale else ""
    ax1.set_title(f'3-PILLAR STRUCTURE{zoom_label}\n(Provider Centroids in Vortex Space)', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper right', fontsize=9)
    ax1.grid(True, alpha=0.3)

    # ===== PANEL 2: Extended Pillars (by model) =====
    ax2 = axes[0, 1]

    # Draw all model centroids
    all_ship_data = []
    for provider in providers:
        if provider not in provider_stats:
            continue
        color = PROVIDER_COLORS.get(provider, 'gray')

        for ship, ship_stats in provider_stats[provider]['ships'].items():
            if not ship_stats['xs']:
                continue

            sx = np.mean(ship_stats['xs'])
            sy = np.mean(ship_stats['ys'])
            mean_baseline = np.mean(ship_stats['baselines'])

            all_ship_data.append({
                'ship': ship,
                'provider': provider,
                'x': sx, 'y': sy,
                'baseline': mean_baseline,
                'n': len(ship_stats['xs'])
            })

            ax2.scatter([sx], [sy], color=color, s=100, alpha=0.7,
                       edgecolors='black', linewidths=1)

            # Store position for label collision detection
            all_ship_data[-1]['label_pos'] = (sx, sy)

    # Event Horizon circle
    ax2.plot(EVENT_HORIZON * np.cos(theta), EVENT_HORIZON * np.sin(theta),
            'r--', linewidth=2, alpha=0.7)
    ax2.scatter([0], [0], color='gold', s=150, marker='*', zorder=15)

    ax2.set_xlim(-ax_lim, ax_lim)
    ax2.set_ylim(-ax_lim, ax_lim)
    ax2.set_aspect('equal')
    ax2.set_xlabel('X (drift * cos)', fontsize=11)
    ax2.set_ylabel('Y (drift * sin)', fontsize=11)
    ax2.set_title(f'EXTENDED PILLARS{zoom_label}\n({len(all_ship_data)} Individual Models)', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)

    # Legend for providers
    legend_handles = [Line2D([0], [0], marker='o', color='w',
                            markerfacecolor=PROVIDER_COLORS.get(p, 'gray'),
                            markersize=10, label=provider_names[p])
                     for p in providers if p in provider_stats]
    ax2.legend(handles=legend_handles, loc='upper right', fontsize=9)

    # Smart labeling: only show labels if points are spread out enough
    # Calculate point spread to detect tight clustering (like Run 010)
    if all_ship_data:
        xs = [d['x'] for d in all_ship_data]
        ys = [d['y'] for d in all_ship_data]
        spread_x = max(xs) - min(xs) if xs else 0
        spread_y = max(ys) - min(ys) if ys else 0
        spread = max(spread_x, spread_y)

        # Only show labels if spread is > 0.5 (relative to ax_lim)
        # OR if there are <= 8 points (always label small datasets)
        show_labels = spread > 0.5 or len(all_ship_data) <= 8

        if show_labels:
            for ship_data in all_ship_data:
                sx, sy = ship_data['x'], ship_data['y']
                ship = ship_data['ship']
                label = ship[:15] + '...' if len(ship) > 15 else ship
                ax2.annotate(label, (sx, sy), fontsize=6, alpha=0.7,
                            xytext=(3, 3), textcoords='offset points')
        else:
            # Add note about clustering
            ax2.text(0.02, 0.02, f'Labels hidden: {len(all_ship_data)} points clustered',
                    transform=ax2.transAxes, fontsize=8, alpha=0.5, style='italic')

    # ===== PANEL 3: Angular Distribution =====
    ax3 = axes[1, 0]

    # Histogram of endpoint angles by provider
    bins = np.linspace(0, 2*np.pi, 25)

    for provider in providers:
        if provider not in provider_stats or not provider_stats[provider]['angles_end']:
            continue
        color = PROVIDER_COLORS.get(provider, 'gray')
        angles = provider_stats[provider]['angles_end']

        ax3.hist(angles, bins=bins, alpha=0.5, color=color,
                label=f"{provider_names[provider]} (n={len(angles)})",
                edgecolor='white')

    # Mark 120° intervals (ideal hexagon)
    for angle in [0, np.pi/3, 2*np.pi/3, np.pi, 4*np.pi/3, 5*np.pi/3]:
        ax3.axvline(x=angle, color='gray', linestyle=':', alpha=0.5)

    ax3.set_xlabel('Angular Position (radians)', fontsize=11)
    ax3.set_ylabel('Count', fontsize=11)
    ax3.set_title('ANGULAR DISTRIBUTION\n(Where trajectories end in polar space)', fontsize=14, fontweight='bold')
    ax3.legend(loc='upper right', fontsize=9)
    ax3.set_xlim(0, 2*np.pi)
    ax3.set_xticks([0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi])
    ax3.set_xticklabels(['0', 'π/2', 'π', '3π/2', '2π'])
    ax3.grid(True, alpha=0.3)

    # ===== PANEL 4: Pillar Stability =====
    ax4 = axes[1, 1]

    # Bar chart: safety margin from Event Horizon by provider
    if centroid_data:
        providers_with_data = [c['provider'] for c in centroid_data]
        margins = [c['safety_margin'] for c in centroid_data]
        colors = [PROVIDER_COLORS.get(p, 'gray') for p in providers_with_data]
        labels = [f"{provider_names[p]}\n(n={c['n']})" for p, c in zip(providers_with_data, centroid_data)]

        bars = ax4.bar(range(len(centroid_data)), margins, color=colors,
                      edgecolor='black', linewidth=2)
        ax4.set_xticks(range(len(centroid_data)))
        ax4.set_xticklabels(labels, fontsize=10)

        # Add value labels on bars
        for i, (bar, margin) in enumerate(zip(bars, margins)):
            height = bar.get_height()
            label_y = height + 0.02 if height >= 0 else height - 0.08
            ax4.text(bar.get_x() + bar.get_width()/2., label_y,
                    f'{margin:.2f}', ha='center', va='bottom' if height >= 0 else 'top',
                    fontsize=11, fontweight='bold')

        # Event Horizon line at 0
        ax4.axhline(y=0, color='red', linestyle='--', linewidth=2,
                   label=f'Event Horizon ({EVENT_HORIZON})')

        # Color regions - positive = safe (green), negative = danger (red)
        ax4.axhspan(-2, 0, alpha=0.1, color='red', label='Beyond EH (VOLATILE)')
        ax4.axhspan(0, 2, alpha=0.1, color='green', label='Below EH (STABLE)')

    ax4.set_ylabel('Safety Margin from Event Horizon', fontsize=11)
    ax4.set_title('PILLAR STABILITY\n(Positive = safely below boundary)', fontsize=14, fontweight='bold')
    ax4.legend(loc='upper right', fontsize=9)
    ax4.grid(True, alpha=0.3, axis='y')
    ax4.set_ylim(-1, 1.5)

    fig.suptitle(f'Run {run_id}: PILLAR ANALYSIS\n(Structural support of the identity manifold)',
                fontsize=18, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_pillar_analysis.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_pillar_analysis.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_pillar_analysis.png + .svg")
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

def create_interactive_html(trajectories, output_dir, run_id, zoom_scale=None):
    """Create interactive Plotly visualizations."""
    if not PLOTLY_AVAILABLE:
        print("  Skipping HTML export (plotly not installed)")
        return

    ax_lim = zoom_scale if zoom_scale else 4

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

    zoom_label = " [ZOOMED]" if zoom_scale else ""
    fig2.update_layout(
        title=f"Run {run_id}: Interactive Vortex View{zoom_label}<br>(Inside boundary = STABLE, Outside = VOLATILE)",
        xaxis=dict(scaleanchor='y', scaleratio=1, range=[-ax_lim, ax_lim]),
        yaxis=dict(range=[-ax_lim, ax_lim]),
        width=1000,
        height=1000
    )

    fig2.write_html(output_dir / f'run{run_id}_interactive_vortex.html')
    print(f"  Saved: run{run_id}_interactive_vortex.html")


def plot_radar_fingerprint(trajectories, output_dir, run_id):
    """Create provider fingerprint radar plot from trajectory data.

    Shows 5 dimensions per provider:
    - Mean Drift (normalized to Event Horizon)
    - Peak Drift (normalized)
    - Volatility (% of trajectories exceeding EH)
    - Stability (% staying below EH)
    - Consistency (inverse of std dev)
    """
    # Collect metrics per provider
    provider_metrics = defaultdict(lambda: {
        'drifts': [],
        'max_drifts': [],
        'volatile_count': 0,
        'stable_count': 0,
        'n_trajectories': 0
    })

    for traj in trajectories:
        provider = traj.get('provider', 'unknown')
        drifts = traj.get('drifts', [])

        if not drifts or provider == 'unknown':
            continue

        provider_metrics[provider]['drifts'].extend(drifts)
        provider_metrics[provider]['max_drifts'].append(max(drifts))

        if max(drifts) >= EVENT_HORIZON:
            provider_metrics[provider]['volatile_count'] += 1
        else:
            provider_metrics[provider]['stable_count'] += 1

        provider_metrics[provider]['n_trajectories'] += 1

    # Compute radar values for each provider
    radar_data = {}

    for provider, metrics in provider_metrics.items():
        if not metrics['drifts'] or metrics['n_trajectories'] == 0:
            continue

        mean_drift = np.mean(metrics['drifts'])
        max_drift = np.mean(metrics['max_drifts']) if metrics['max_drifts'] else 0
        volatility_rate = metrics['volatile_count'] / metrics['n_trajectories']
        stability_rate = metrics['stable_count'] / metrics['n_trajectories']
        drift_variance = np.std(metrics['drifts']) if len(metrics['drifts']) > 1 else 0

        # Normalize to 0-1 scale
        radar_data[provider] = {
            'Mean Drift': min(mean_drift / EVENT_HORIZON, 1.5) / 1.5,  # Cap at 150%
            'Peak Drift': min(max_drift / EVENT_HORIZON, 2.0) / 2.0,  # Cap at 200%
            'Volatility': volatility_rate,
            'Stability': stability_rate,
            'Consistency': 1 - min(drift_variance, 1.0),
        }

    if not radar_data:
        print(f"  SKIPPED: radar (no provider data)")
        return

    # Create radar plot
    categories = list(next(iter(radar_data.values())).keys())
    N = len(categories)

    angles = [n / float(N) * 2 * np.pi for n in range(N)]
    angles += angles[:1]  # Complete the loop

    fig, ax = plt.subplots(figsize=(10, 10), subplot_kw=dict(polar=True))

    for provider, values in radar_data.items():
        vals = list(values.values())
        vals += vals[:1]  # Complete the loop

        color = PROVIDER_COLORS.get(provider, '#888888')
        ax.plot(angles, vals, 'o-', linewidth=2, label=provider.title(), color=color)
        ax.fill(angles, vals, alpha=0.25, color=color)

    # Set category labels
    ax.set_xticks(angles[:-1])
    ax.set_xticklabels(categories, size=11, fontweight='bold')

    # Set radial limits
    ax.set_ylim(0, 1)
    ax.set_yticks([0.25, 0.5, 0.75, 1.0])
    ax.set_yticklabels(['25%', '50%', '75%', '100%'], size=9)

    # Title and legend
    ax.set_title(f'Run {run_id}: Provider Identity Fingerprint\n(5-Dimension Behavioral Signature)',
                 size=14, fontweight='bold', pad=20)
    ax.legend(loc='upper right', bbox_to_anchor=(1.15, 1.1))

    plt.tight_layout()
    output_path = output_dir / f'run{run_id}_provider_fingerprint.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.savefig(output_path.with_suffix('.svg'), bbox_inches='tight')
    print(f"  Saved: run{run_id}_provider_fingerprint.png + .svg")
    plt.close()


# =============================================================================
# MAIN
# =============================================================================

def compute_zoom_scale(trajectories):
    """Compute optimal axis scale based on actual data distribution.

    Returns a scale that shows 99th percentile + Event Horizon with 20% padding.
    """
    all_drifts = []
    for traj in trajectories:
        all_drifts.extend(traj.get('drifts', []))

    if not all_drifts:
        return 4.0  # Default

    all_drifts = np.array(all_drifts)
    p99 = np.percentile(all_drifts, 99)
    data_max = max(p99, all_drifts.max())

    # Scale should show Event Horizon for context, with 20% padding
    scale = max(data_max * 1.2, EVENT_HORIZON * 1.1)

    # Round to nice number
    if scale <= 1.0:
        return 1.0
    elif scale <= 1.5:
        return 1.5
    elif scale <= 2.0:
        return 2.0
    elif scale <= 2.5:
        return 2.5
    elif scale <= 3.0:
        return 3.0
    else:
        return 4.0


def main():
    parser = argparse.ArgumentParser(description='Armada Visualization - Unified Run-Agnostic Script')
    parser.add_argument('--run', type=str, help='Run ID (e.g., 008, 009, 008_prep)')
    parser.add_argument('--list', action='store_true', help='List available runs')
    parser.add_argument('--all', action='store_true', help='Generate all visualization types')
    parser.add_argument('--dB', action='store_true', help='Use decibel scaling for visualizations')
    parser.add_argument('--zoom', action='store_true', help='Auto-zoom to fit data (for tight distributions)')
    parser.add_argument('--type', type=str, choices=['phase', 'vortex', '3d', 'pillar', 'stability', 'fft', 'html', 'radar'],
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

    # Handle specialized runs (015, 016) that have their own visualizers
    if args.run in ['015', '15']:
        print("=" * 70)
        print("DELEGATING TO SPECIALIZED VISUALIZER: Run 015")
        print("=" * 70)
        print("\nRun 015 uses different data format (stability criteria).")
        print("Launching: 9_STABILITY_CRITERIA/visualize_run015.py")
        print("-" * 70)
        script_path = BASE_DIR / "9_STABILITY_CRITERIA" / "visualize_run015.py"
        subprocess.run([sys.executable, str(script_path)])
        return

    if args.run in ['016', '16']:
        print("=" * 70)
        print("DELEGATING TO SPECIALIZED VISUALIZER: Run 016")
        print("=" * 70)
        print("\nRun 016 uses different data format (settling time).")
        print("Launching: 10_SETTLING_TIME/visualize_run016.py")
        print("-" * 70)
        script_path = BASE_DIR / "10_SETTLING_TIME" / "visualize_run016.py"
        subprocess.run([sys.executable, str(script_path)])
        return

    if args.run in ['017', '17']:
        print("=" * 70)
        print("DELEGATING TO SPECIALIZED VISUALIZER: Run 017")
        print("=" * 70)
        print("\nRun 017 uses context damping format.")
        print("Launching: 11_CONTEXT_DAMPING/visualize_run017.py")
        print("-" * 70)
        script_path = BASE_DIR / "11_CONTEXT_DAMPING" / "visualize_run017.py"
        subprocess.run([sys.executable, str(script_path)])
        return

    if args.run in ['018', '18']:
        print("=" * 70)
        print("DELEGATING TO SPECIALIZED VISUALIZER: Run 018")
        print("=" * 70)
        print("\nRun 018: Recursive Learnings (4 sub-experiments).")
        print("Launching: 11_CONTEXT_DAMPING/visualize_run018.py")
        print("-" * 70)
        script_path = BASE_DIR / "11_CONTEXT_DAMPING" / "visualize_run018.py"
        subprocess.run([sys.executable, str(script_path)])
        return

    if args.run in ['020', '20', '020A', '020a', '020B', '020b']:
        print("=" * 70)
        print("DELEGATING TO SPECIALIZED VISUALIZER: Run 020")
        print("=" * 70)
        print("\nRun 020: Tribunal (A) + Induced vs Inherent (B)")
        print("  020A: Good Cop/Bad Cop tribunal paradigm")
        print("  020B: Control vs Treatment comparison")
        print("-" * 70)
        script_path = OUTPUT_DIR / "visualize_run020.py"
        if script_path.exists():
            subprocess.run([sys.executable, str(script_path)])
        else:
            print(f"NOTE: {script_path} not yet implemented.")
            print("Run 020 data exists in 0_results/runs/pre_armada_020/")
            print("Visualization script to be created.")
        return

    # Find run data (for standard trajectory runs 008-014)
    if args.run:
        run_id, data_file = get_run_file(args.run)
    else:
        run_id, data_file = get_latest_run()

    if data_file is None:
        print("ERROR: No run data found!")
        print("  Run `python 4_BASIN_TOPOLOGY/run008_with_keys.py` or `python 3_EVENT_HORIZON/run009_drain_capture.py` first.")
        print("\n  For specialized runs:")
        print("    --run 015  -> Stability Criteria (9_STABILITY_CRITERIA/visualize_run015.py)")
        print("    --run 016  -> Settling Time (10_SETTLING_TIME/visualize_run016.py)")
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

    # Compute zoom scale if requested
    zoom_scale = None
    if args.zoom:
        zoom_scale = compute_zoom_scale(trajectories)
        print(f"Zoom: ENABLED (scale = {zoom_scale})")

    # Create output directories organized by visualization type
    # Structure: pics/vortex/, pics/phase_portrait/, pics/basin_3d/, pics/stability/, pics/fft/, pics/interactive/
    output_dirs = {
        'vortex': OUTPUT_DIR / '1_vortex',
        'phase': OUTPUT_DIR / '2_phase_portrait',
        '3d': OUTPUT_DIR / '3_basin_3d',
        'pillar': OUTPUT_DIR / '4_pillar',
        'stability': OUTPUT_DIR / '5_stability',
        'html': OUTPUT_DIR / '6_interactive',
        'fft': OUTPUT_DIR / '7_fft',
        'radar': OUTPUT_DIR / '10_radar',
    }

    # Create all needed directories
    for d in output_dirs.values():
        d.mkdir(parents=True, exist_ok=True)

    print(f"Output: {OUTPUT_DIR} (organized by type)")
    print("-" * 70)

    # Generate visualizations
    if args.type:
        viz_types = [args.type]
    elif args.all:
        viz_types = ['phase', 'vortex', '3d', 'pillar', 'stability', 'fft', 'html', 'radar']
    else:
        viz_types = ['phase', 'vortex', '3d', 'pillar', 'stability', 'fft', 'html', 'radar']

    print("\nGenerating visualizations...")

    if 'phase' in viz_types:
        plot_phase_portrait(trajectories, output_dirs['phase'], run_id, use_dB=args.dB, zoom_scale=zoom_scale)

    if 'vortex' in viz_types:
        plot_vortex(trajectories, output_dirs['vortex'], run_id, use_dB=args.dB, zoom_scale=zoom_scale)
        plot_vortex_x4(trajectories, output_dirs['vortex'], run_id, zoom_scale=zoom_scale)
        plot_vortex_by_company(trajectories, output_dirs['vortex'], run_id, zoom_scale=zoom_scale)

    if '3d' in viz_types:
        plot_3d_basin(trajectories, output_dirs['3d'], run_id, use_dB=args.dB, zoom_scale=zoom_scale)

    if 'pillar' in viz_types:
        plot_pillar_analysis(trajectories, output_dirs['pillar'], run_id, zoom_scale=zoom_scale)

    if 'stability' in viz_types:
        skip, reason = should_skip_visualization(run_id, 'stability')
        if skip:
            print(f"  SKIPPED: stability ({reason})")
        else:
            plot_stability_basin(trajectories, output_dirs['stability'], run_id, zoom_scale=zoom_scale)

    if 'fft' in viz_types:
        skip, reason = should_skip_visualization(run_id, 'fft')
        if skip:
            print(f"  SKIPPED: fft ({reason})")
        else:
            plot_fft_spectral(trajectories, output_dirs['fft'], run_id)

    if 'html' in viz_types:
        create_interactive_html(trajectories, output_dirs['html'], run_id, zoom_scale=zoom_scale)

    if 'radar' in viz_types:
        plot_radar_fingerprint(trajectories, output_dirs['radar'], run_id)

    print("\n" + "-" * 70)
    print("COMPLETE!")
    print(f"All outputs in: {OUTPUT_DIR}")
    print("=" * 70)

if __name__ == "__main__":
    main()
