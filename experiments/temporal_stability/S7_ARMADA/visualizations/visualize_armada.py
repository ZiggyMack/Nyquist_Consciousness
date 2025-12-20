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

# Provider colors (expanded for full fleet)
PROVIDER_COLORS = {
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
    "grok": "#1a1a1a",
    "meta-llama": "#FF6B6B",
    "mistralai": "#FFD93D",
    "deepseek": "#6BCB77",
    "qwen": "#4D96FF",
    "moonshotai": "#9B59B6",
}

# Event Horizon threshold
# Cosine distance calibrated from run023b (2025-12-20)
# See 15_IRON_CLAD_FOUNDATION/results/COSINE_EVENT_HORIZON_CALIBRATION.md
EVENT_HORIZON = 0.80

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

    # Search main directory, legacy_runs, and IRON_CLAD results
    search_dirs = [RESULTS_DIR]
    legacy_dir = RESULTS_DIR / "legacy_runs"
    if legacy_dir.exists():
        search_dirs.append(legacy_dir)
    # IRON CLAD foundation results (run023b cosine data)
    iron_clad_dir = BASE_DIR / "15_IRON_CLAD_FOUNDATION" / "results"
    if iron_clad_dir.exists():
        search_dirs.append(iron_clad_dir)

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
    elif "llama" in name:
        return "meta-llama"
    elif "mistral" in name or "mixtral" in name:
        return "mistralai"
    elif "deepseek" in name:
        return "deepseek"
    elif "qwen" in name:
        return "qwen"
    elif "kimi" in name:
        return "moonshotai"
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
        # Check if this is run023b format (has 'probe_sequence' in items)
        # vs run012/014 format (has 'turns' or 'phases')
        is_iron_clad_format = (
            len(results) > 0 and
            isinstance(results[0], dict) and
            'probe_sequence' in results[0]
        )

        if is_iron_clad_format:
            # Format 6: Run 023b IRON CLAD (results array with probe_sequence)
            # Group results by model and extract drift sequences
            model_results = defaultdict(list)
            for result in results:
                if not isinstance(result, dict):
                    continue
                model = result.get('model', 'unknown')
                model_results[model].append(result)

            for model, model_result_list in model_results.items():
                # Derive provider from model name (not from data's 'provider' field which is API provider)
                provider = get_provider(model)

                # AGGREGATION STRATEGY for cleaner 3D basin visualization:
                # Use peak_drift per iteration (one point per iteration = ~30 points)
                # instead of all probe drifts (~780 points) which creates spaghetti
                iteration_peaks = []
                for r in sorted(model_result_list, key=lambda x: x.get('iteration', 0)):
                    # Use pre-computed peak_drift if available
                    if 'peak_drift' in r:
                        iteration_peaks.append(r['peak_drift'])
                    else:
                        # Fallback: compute from probe_sequence
                        probe_seq = r.get('probe_sequence', [])
                        drifts = [p['drift'] for p in probe_seq if isinstance(p, dict) and 'drift' in p]
                        if drifts:
                            iteration_peaks.append(max(drifts))

                if len(iteration_peaks) >= 3:
                    baseline = iteration_peaks[0]
                    max_drift = max(iteration_peaks)
                    status = "VOLATILE" if max_drift >= EVENT_HORIZON else "STABLE"

                    # Shorten model name for display
                    short_name = model.split('/')[-1] if '/' in model else model

                    trajectories.append({
                        'ship': short_name,
                        'full_model': model,  # Keep full name for API type detection
                        'provider': provider,
                        'sequence': 'iron_clad',
                        'drifts': iteration_peaks,
                        'status': status,
                        'baseline': baseline
                    })

            if trajectories:
                return trajectories

        # Standard run012/014 format with turns/phases
        for ship_data in results:
            if not isinstance(ship_data, dict):
                continue

            ship_name = ship_data.get('ship', ship_data.get('model', 'unknown'))
            # Always derive provider from model name (data's 'provider' is API name, not category)
            provider = get_provider(ship_name)

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
            # Always derive provider from model name (data's 'provider' is API name, not category)
            provider = get_provider(ship_name)
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
            # Always derive provider from model name (data's 'provider' is API name, not category)
            provider = get_provider(ship_name)
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
    """Phase portrait: drift[N] vs drift[N+1] - Raw vs Aggregated.

    Left panel: Raw data with all individual trajectories
    Right panel: Aggregated/smoothed view for cleaner presentation

    NOTE: dB scaling is DISABLED. It distorts the phase space geometry
    by compressing small values to extreme negatives.

    Args:
        zoom_scale: If provided, use this as the axis max instead of 4.0
    """
    from matplotlib.lines import Line2D

    # Ignore dB flag - it distorts the geometry
    if use_dB:
        print("  NOTE: dB scaling disabled for phase portrait (distorts geometry)")
        return  # Skip dB version entirely

    fig, axes = plt.subplots(1, 2, figsize=(18, 9))

    scale_label = ""
    eh_val = EVENT_HORIZON

    # Auto-calculate axis max from data if not provided
    if zoom_scale:
        ax_max = zoom_scale
    else:
        # Find actual data extent
        all_drifts = []
        for traj in trajectories:
            all_drifts.extend(traj['drifts'])
        if all_drifts:
            data_max = max(all_drifts)
            # Set axis to data max + 20% padding, minimum of EH + 0.2 for context
            ax_max = max(data_max * 1.2, eh_val + 0.2)
            ax_max = min(ax_max, 2.0)  # Cap at theoretical cosine max
        else:
            ax_max = 1.2  # Default fallback

    zoom_label = " [ZOOMED]" if zoom_scale else ""
    ax_min = 0

    # Provider display names
    provider_names = {
        'claude': 'Claude', 'gpt': 'GPT', 'gemini': 'Gemini', 'grok': 'Grok',
        'meta-llama': 'Llama', 'mistralai': 'Mistral', 'deepseek': 'DeepSeek',
        'qwen': 'Qwen', 'moonshotai': 'Moonshot'
    }

    # ===== LEFT PANEL: RAW DATA =====
    ax = axes[0]

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

    ax.plot([ax_min, ax_max], [ax_min, ax_max], 'k--', alpha=0.3, label='No change')
    ax.fill_between([ax_min, ax_max], [ax_min, ax_max], [ax_max, ax_max], alpha=0.08, color='red')
    ax.fill_between([ax_min, ax_max], [ax_min, ax_min], [ax_min, ax_max], alpha=0.08, color='green')
    ax.axvline(x=eh_val, color='red', linestyle=':', alpha=0.5)
    ax.axhline(y=eh_val, color='red', linestyle=':', alpha=0.5)

    ax.set_xlabel('Drift at Turn N', fontsize=12)
    ax.set_ylabel('Drift at Turn N+1', fontsize=12)
    ax.set_title(f'PHASE PORTRAIT: RAW DATA{zoom_label}', fontsize=14, fontweight='bold')
    ax.set_xlim(ax_min, ax_max)
    ax.set_ylim(ax_min, ax_max)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)

    # ===== RIGHT PANEL: AGGREGATED/SMOOTHED (pretty version) =====
    ax = axes[1]

    # Aggregate by provider: compute mean trajectory with B-spline smoothing
    provider_trajectories = defaultdict(list)
    for traj in trajectories:
        provider = traj['provider']
        drifts = np.array(traj['drifts'])
        if len(drifts) >= 3:
            provider_trajectories[provider].append(drifts)

    for provider, traj_list in provider_trajectories.items():
        color = PROVIDER_COLORS.get(provider, 'gray')

        # Resample all trajectories to standard 30-point grid (N=30 iterations)
        target_len = 30
        resampled = []
        for drifts in traj_list:
            if len(drifts) >= 2:
                old_x = np.linspace(0, 1, len(drifts))
                new_x = np.linspace(0, 1, target_len)
                resampled.append(np.interp(new_x, old_x, drifts))

        if not resampled:
            continue

        resampled = np.array(resampled)
        mean_drifts = np.mean(resampled, axis=0)

        # Create phase portrait coordinates from mean trajectory
        xs = mean_drifts[:-1]  # ~29 points
        ys = mean_drifts[1:]

        # Smooth the mean trajectory with B-spline for prettier visualization
        if len(xs) >= 4:
            xs_smooth, ys_smooth = smooth_trajectory_2d(xs, ys, num_points=100)

            # Plot thick smooth line for mean trajectory
            ax.plot(xs_smooth, ys_smooth, color=color, linewidth=3, alpha=0.9,
                   label=f'{provider_names.get(provider, provider)} ({len(traj_list)} ships)')
        else:
            # Not enough points for spline, just plot raw
            ax.plot(xs, ys, color=color, linewidth=2, alpha=0.8,
                   label=f'{provider_names.get(provider, provider)} ({len(traj_list)} ships)')

        # Mark start and end of mean trajectory
        if len(xs) > 0:
            ax.scatter(xs[0], ys[0], color='lime', s=80, alpha=0.9, zorder=15,
                      marker='D', edgecolors='darkgreen', linewidths=2)
            ax.scatter(xs[-1], ys[-1], color=color, s=100, alpha=0.9, zorder=15,
                      marker='*', edgecolors='black', linewidths=1)

    # Decorations
    ax.plot([ax_min, ax_max], [ax_min, ax_max], 'k--', alpha=0.3, label='No change')
    ax.fill_between([ax_min, ax_max], [ax_min, ax_max], [ax_max, ax_max], alpha=0.08, color='red')
    ax.fill_between([ax_min, ax_max], [ax_min, ax_min], [ax_min, ax_max], alpha=0.08, color='green')
    ax.axvline(x=eh_val, color='red', linestyle=':', alpha=0.5)
    ax.axhline(y=eh_val, color='red', linestyle=':', alpha=0.5)

    ax.set_xlabel('Drift at Turn N', fontsize=12)
    ax.set_ylabel('Drift at Turn N+1', fontsize=12)
    ax.set_title(f'PHASE PORTRAIT: AGGREGATED BY PROVIDER{zoom_label}', fontsize=14, fontweight='bold')
    ax.set_xlim(ax_min, ax_max)
    ax.set_ylim(ax_min, ax_max)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)

    # Legend with provider colors and markers
    legend_handles = []
    providers_in_data = set(t['provider'] for t in trajectories)
    for provider in sorted(providers_in_data):
        color = PROVIDER_COLORS.get(provider, 'gray')
        n_ships = len(provider_trajectories.get(provider, []))
        legend_handles.append(Line2D([0], [0], color=color, linewidth=3,
                                    label=f'{provider_names.get(provider, provider)} ({n_ships} ships)'))
    # Marker explanations
    legend_handles.append(Line2D([0], [0], marker='D', color='w', markerfacecolor='lime',
                                markersize=10, label='Start (baseline)', markeredgecolor='darkgreen'))
    legend_handles.append(Line2D([0], [0], marker='*', color='w', markerfacecolor='gray',
                                markersize=12, label='End (final)', markeredgecolor='black'))
    legend_handles.append(Line2D([0], [0], color='red', linestyle=':', linewidth=2,
                                label=f'Event Horizon ({EVENT_HORIZON})'))
    ax.legend(handles=legend_handles, loc='upper left', fontsize=8, framealpha=0.9)

    fig.suptitle(f'Run {run_id}: Identity Flow (Left: All Ships | Right: Provider Means)',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_phase_portrait.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_phase_portrait.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_phase_portrait.png + .svg")
    plt.close()

    # Also generate an aggregated-only version for maximum prettiness
    _plot_phase_portrait_aggregated(trajectories, output_dir, run_id, ax_max, eh_val)


def _plot_phase_portrait_aggregated(trajectories, output_dir, run_id, ax_max, eh_val):
    """Generate a standalone aggregated phase portrait (single panel, maximum pretty).

    Aggregation strategy:
    1. Each trajectory already has ~30 peak_drift values (one per iteration)
    2. Average across ships per provider to get provider mean trajectory
    3. Apply B-spline smoothing for pretty curves
    """
    from matplotlib.lines import Line2D

    fig, ax = plt.subplots(figsize=(12, 12))

    provider_names = {
        'claude': 'Claude', 'gpt': 'GPT', 'gemini': 'Gemini', 'grok': 'Grok',
        'meta-llama': 'Llama', 'mistralai': 'Mistral', 'deepseek': 'DeepSeek',
        'qwen': 'Qwen', 'moonshotai': 'Moonshot'
    }

    # Auto-fit axis to data range (not starting at 0)
    all_drifts = []
    for traj in trajectories:
        all_drifts.extend(traj['drifts'])
    if all_drifts:
        data_min = min(all_drifts)
        data_max = max(all_drifts)
        # Add 10% padding on each side
        ax_min = max(0, data_min - (data_max - data_min) * 0.1)
        ax_max = data_max + (data_max - data_min) * 0.1
        ax_max = min(ax_max, 2.0)  # Cap at cosine max
    else:
        ax_min = 0

    # Aggregate by provider - trajectories already contain iteration-level peak_drifts
    provider_trajectories = defaultdict(list)
    for traj in trajectories:
        provider = traj['provider']
        drifts = np.array(traj['drifts'])
        if len(drifts) >= 3:
            provider_trajectories[provider].append(drifts)

    for provider, traj_list in provider_trajectories.items():
        color = PROVIDER_COLORS.get(provider, 'gray')

        # Resample all trajectories to same length (30 points typical)
        target_len = 30  # Standard N=30 iterations
        resampled = []
        for drifts in traj_list:
            if len(drifts) >= 2:
                old_x = np.linspace(0, 1, len(drifts))
                new_x = np.linspace(0, 1, target_len)
                resampled.append(np.interp(new_x, old_x, drifts))

        if not resampled:
            continue

        resampled = np.array(resampled)
        mean_drifts = np.mean(resampled, axis=0)

        # Phase portrait: drift[N] vs drift[N+1]
        xs = mean_drifts[:-1]  # ~29 points
        ys = mean_drifts[1:]

        # Apply B-spline smoothing for pretty curves
        if len(xs) >= 4:
            xs_smooth, ys_smooth = smooth_trajectory_2d(xs, ys, num_points=100)
            ax.plot(xs_smooth, ys_smooth, color=color, linewidth=4, alpha=0.9,
                   label=f'{provider_names.get(provider, provider)} ({len(traj_list)} ships)')
        else:
            ax.plot(xs, ys, color=color, linewidth=3, alpha=0.8,
                   label=f'{provider_names.get(provider, provider)} ({len(traj_list)} ships)')

        # Mark start and end
        if len(xs) > 0:
            ax.scatter(xs[0], ys[0], color='lime', s=150, alpha=0.9, zorder=15,
                      marker='D', edgecolors='darkgreen', linewidths=2)
            ax.scatter(xs[-1], ys[-1], color=color, s=200, alpha=0.9, zorder=15,
                      marker='*', edgecolors='black', linewidths=2)

    # Decorations
    ax.plot([ax_min, ax_max], [ax_min, ax_max], 'k--', alpha=0.3, linewidth=2)
    ax.fill_between([ax_min, ax_max], [ax_min, ax_max], [ax_max, ax_max], alpha=0.06, color='red')
    ax.fill_between([ax_min, ax_max], [ax_min, ax_min], [ax_min, ax_max], alpha=0.06, color='green')
    ax.axvline(x=eh_val, color='red', linestyle='--', alpha=0.7, linewidth=2)
    ax.axhline(y=eh_val, color='red', linestyle='--', alpha=0.7, linewidth=2)

    ax.set_xlabel('Drift at Turn N (Cosine Distance)', fontsize=14)
    ax.set_ylabel('Drift at Turn N+1 (Cosine Distance)', fontsize=14)
    ax.set_title(f'Run {run_id}: Identity Flow by Provider (Aggregated Means)\n'
                f'{len(trajectories)} Ships | Event Horizon = {eh_val}',
                fontsize=16, fontweight='bold')
    ax.set_xlim(ax_min, ax_max)
    ax.set_ylim(ax_min, ax_max)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3)

    ax.legend(loc='upper left', fontsize=10, framealpha=0.9)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_phase_portrait_aggregated.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_phase_portrait_aggregated.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_phase_portrait_aggregated.png + .svg")
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

        # Event Horizon circle
        eh_radius = EVENT_HORIZON
        theta = np.linspace(0, 2*np.pi, 100)
        ax.plot(eh_radius * np.cos(theta), eh_radius * np.sin(theta), 'r--', linewidth=2.5, alpha=0.7,
               label=f'Event Horizon ({EVENT_HORIZON})')
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
    """Vortex view split by provider - grid showing each provider's field separately.

    This reveals the individual 'magnetic field' patterns of each provider.
    Dynamically adjusts grid size based on number of providers with data.
    """
    # Get providers that actually have data
    by_provider = defaultdict(list)
    for traj in trajectories:
        by_provider[traj['provider']].append(traj)

    # Filter to providers with data, maintain a sensible order
    all_providers = ['claude', 'gpt', 'gemini', 'grok', 'meta-llama', 'mistralai', 'deepseek', 'qwen', 'moonshotai']
    providers = [p for p in all_providers if p in by_provider and by_provider[p]]

    if not providers:
        print("  [SKIP] No provider data found for vortex_x4")
        return

    provider_names = {
        'claude': 'CLAUDE', 'gpt': 'GPT', 'gemini': 'GEMINI', 'grok': 'GROK',
        'meta-llama': 'META-LLAMA', 'mistralai': 'MISTRAL', 'deepseek': 'DEEPSEEK',
        'qwen': 'QWEN', 'moonshotai': 'MOONSHOT'
    }

    # Calculate grid size
    n_providers = len(providers)
    if n_providers <= 4:
        n_cols, n_rows = 2, 2
    elif n_providers <= 6:
        n_cols, n_rows = 3, 2
    elif n_providers <= 9:
        n_cols, n_rows = 3, 3
    else:
        n_cols = 4
        n_rows = (n_providers + 3) // 4

    fig, axes = plt.subplots(n_rows, n_cols, figsize=(6*n_cols, 6*n_rows))
    if n_rows == 1 and n_cols == 1:
        axes = np.array([axes])
    axes = axes.flatten()

    # Hide unused axes
    for idx in range(n_providers, len(axes)):
        axes[idx].set_visible(False)

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

        # Count total drift points, not just trajectories
        total_points = sum(len(t['drifts']) for t in provider_trajs)
        n_ships = len(provider_trajs)
        ax.set_title(f'{provider_names.get(provider, provider.upper())}\n(ships={n_ships}, n={total_points}, S: {stable_count}, V: {volatile_count})',
                    fontsize=12, fontweight='bold', color=color)
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
            # Count total drift points, not just trajectories
            total_points = sum(len(t['drifts']) for t in ship_trajs)
            ax.set_title(f'{display_name}\n(n={total_points}, S: {stable_count}, V: {volatile_count})',
                        fontsize=11, fontweight='bold')
            ax.grid(True, alpha=0.3)

        # Hide unused subplots
        for idx in range(len(by_ship), len(axes)):
            axes[idx].set_visible(False)

        fig.suptitle(f'Run {run_id}: {company_name} Identity Field by Model\n' +
                    f'(Event Horizon = {EVENT_HORIZON})',
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

        # Event Horizon Cylinder - optional
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

    subtitle = f'(Event Horizon = {EVENT_HORIZON})'
    fig.suptitle(f'Run {run_id}: Identity Attractor Basin\n{subtitle}',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_3d_basin.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_3d_basin.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_3d_basin.png + .svg")
    plt.close()

def plot_stability_basin(trajectories, output_dir, run_id, zoom_scale=None):
    """Stability basin: scatter + histogram view of STABLE vs VOLATILE classification.

    Panels:
    1. Baseline vs Peak Drift scatter (by provider)
    2. STABLE vs VOLATILE histogram distribution
    """
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))

    # Auto-scale axis limits based on actual data (cosine distance range [0, 2])
    if zoom_scale:
        ax_max = zoom_scale
    else:
        all_max_drifts = [max(t['drifts']) for t in trajectories if t.get('drifts')]
        if all_max_drifts:
            data_max = max(all_max_drifts)
            ax_max = max(data_max * 1.2, EVENT_HORIZON + 0.15)
            ax_max = min(ax_max, 2.0)
        else:
            ax_max = 1.2

    # Group by provider
    provider_data = defaultdict(lambda: {'baselines': [], 'max_drifts': [], 'statuses': []})

    for traj in trajectories:
        provider = traj['provider']
        drifts = traj['drifts']
        if len(drifts) >= 2:
            provider_data[provider]['baselines'].append(drifts[0])
            provider_data[provider]['max_drifts'].append(max(drifts))
            provider_data[provider]['statuses'].append(traj['status'])

    # ===== PANEL 1: Baseline vs Peak Drift =====
    ax1 = axes[0]
    for provider, pdata in provider_data.items():
        color = PROVIDER_COLORS.get(provider, 'gray')
        ax1.scatter(pdata['baselines'], pdata['max_drifts'],
                   c=color, alpha=0.7, s=100, label=f"{provider.title()} (n={len(pdata['baselines'])})")

    ax1.plot([0, ax_max], [0, ax_max], 'k--', alpha=0.3, label='No change')
    ax1.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, alpha=0.7,
                label=f'Event Horizon ({EVENT_HORIZON})')
    ax1.set_xlabel('Baseline Drift (Cosine Distance)', fontsize=12)
    ax1.set_ylabel('Peak Drift (Cosine Distance)', fontsize=12)
    ax1.set_title('Baseline vs Peak Drift by Provider', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left', fontsize=10)
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, ax_max)
    ax1.set_ylim(0, ax_max)

    # ===== PANEL 2: STABLE vs VOLATILE histogram =====
    ax2 = axes[1]
    stable_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'STABLE']
    volatile_baselines = [traj['baseline'] for traj in trajectories if traj['status'] == 'VOLATILE']

    all_baselines = stable_baselines + volatile_baselines
    if all_baselines:
        bin_max = max(all_baselines) * 1.1
        bin_max = max(bin_max, EVENT_HORIZON + 0.1)
        bin_max = min(bin_max, 2.0)
    else:
        bin_max = 1.0
    bins = np.linspace(0, bin_max, 12)

    if stable_baselines or volatile_baselines:
        data_to_plot = []
        labels = []
        colors = []
        if stable_baselines:
            data_to_plot.append(stable_baselines)
            labels.append(f'STABLE (n={len(stable_baselines)})')
            colors.append('#2ecc71')
        if volatile_baselines:
            data_to_plot.append(volatile_baselines)
            labels.append(f'VOLATILE (n={len(volatile_baselines)})')
            colors.append('#e74c3c')
        ax2.hist(data_to_plot, bins=bins, alpha=0.8, color=colors,
                label=labels, edgecolor='white', rwidth=0.85)

    ax2.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax2.set_xlabel('Baseline Drift (Cosine Distance)', fontsize=12)
    ax2.set_ylabel('Ship Count', fontsize=12)
    ax2.set_title(f'STABLE vs VOLATILE Distribution\n(Classification: peak_drift < {EVENT_HORIZON})',
                 fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right', fontsize=11)
    ax2.grid(True, alpha=0.3, axis='y')

    # Overall title
    stable_count = len(stable_baselines)
    volatile_count = len(volatile_baselines)
    fig.suptitle(f'Run {run_id}: Identity Stability Basin\n'
                f'{len(trajectories)} Ships | STABLE: {stable_count} | VOLATILE: {volatile_count} | EH={EVENT_HORIZON}',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_stability_basin.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_stability_basin.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_stability_basin.png + .svg")
    plt.close()


def _plot_boxplots_single(trajectories, output_dir, run_id, zoom_scale, title_suffix, filename_suffix):
    """Helper function to create a single boxplot visualization for a subset of trajectories."""
    if not trajectories:
        return

    fig, axes = plt.subplots(1, 2, figsize=(18, 8))

    # Auto-scale axis limits
    if zoom_scale:
        ax_max = zoom_scale
    else:
        all_max_drifts = [max(t['drifts']) for t in trajectories if t.get('drifts')]
        if all_max_drifts:
            data_max = max(all_max_drifts)
            ax_max = max(data_max * 1.2, EVENT_HORIZON + 0.15)
            ax_max = min(ax_max, 2.0)
        else:
            ax_max = 1.2

    # Group by provider for panel 2
    provider_data = defaultdict(lambda: {'max_drifts': []})
    for traj in trajectories:
        provider = traj['provider']
        drifts = traj['drifts']
        if len(drifts) >= 2:
            provider_data[provider]['max_drifts'].append(max(drifts))

    # ===== PANEL 1: Drift Distribution by Ship =====
    ax1 = axes[0]

    ship_data = []
    ship_names = []
    ship_colors = []

    for traj in sorted(trajectories, key=lambda t: np.mean(t['drifts'])):
        ship_data.append(traj['drifts'])
        # Shorten ship name for display
        short_name = traj['ship']
        # Remove provider prefixes for cleaner labels
        if '/' in short_name:
            short_name = short_name.split('/')[-1]
        short_name = short_name.replace('claude-', 'c-').replace('gpt-', 'g-')
        short_name = short_name.replace('gemini-', 'gem-').replace('grok-', 'grk-')
        short_name = short_name.replace('-20241022', '').replace('-20251001', '')
        short_name = short_name.replace('-Instruct-Turbo', '').replace('-Instruct', '')
        short_name = short_name.replace('-Turbo', '').replace('-Distill-', '-')
        if len(short_name) > 18:
            short_name = short_name[:16] + '..'
        ship_names.append(short_name)
        ship_colors.append(PROVIDER_COLORS.get(traj['provider'], 'gray'))

    if ship_data:
        bp = ax1.boxplot(ship_data, patch_artist=True, vert=True)

        for patch, color in zip(bp['boxes'], ship_colors):
            patch.set_facecolor(color)
            patch.set_alpha(0.7)

        ax1.set_xticklabels(ship_names, rotation=55, ha='right', fontsize=9)
        ax1.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
                   label=f'Event Horizon ({EVENT_HORIZON})')
        ax1.set_ylabel('Drift (Cosine Distance)', fontsize=12)
        ax1.set_title('Drift Distribution by Ship (sorted by mean)', fontsize=13, fontweight='bold')
        ax1.legend(loc='upper left', fontsize=10)
        ax1.grid(True, alpha=0.3, axis='y')
        ax1.set_ylim(0, ax_max)

    # ===== PANEL 2: Peak Drift by Provider =====
    ax2 = axes[1]

    # Use all available providers, sorted by median drift
    provider_order = sorted(provider_data.keys(),
                           key=lambda p: np.median(provider_data[p]['max_drifts']) if provider_data[p]['max_drifts'] else 0)
    provider_peaks = []
    provider_labels = []
    provider_colors_list = []

    for provider in provider_order:
        if provider in provider_data and provider_data[provider]['max_drifts']:
            provider_peaks.append(provider_data[provider]['max_drifts'])
            n = len(provider_data[provider]['max_drifts'])
            provider_labels.append(f'{provider.title()}\n(n={n})')
            provider_colors_list.append(PROVIDER_COLORS.get(provider, 'gray'))

    if provider_peaks:
        # Style outliers to be more visible and match legend
        flierprops = dict(marker='o', markerfacecolor='none', markeredgecolor='gray',
                         markersize=6, alpha=0.6, linestyle='none')
        bp = ax2.boxplot(provider_peaks, patch_artist=True, vert=True, widths=0.6,
                        flierprops=flierprops)

        for patch, color in zip(bp['boxes'], provider_colors_list):
            patch.set_facecolor(color)
            patch.set_alpha(0.7)

        ax2.set_xticklabels(provider_labels, fontsize=10)
        ax2.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
                   label=f'Event Horizon ({EVENT_HORIZON})')
        ax2.set_ylabel('Peak Drift (Cosine Distance)', fontsize=12)
        ax2.set_title('Peak Drift by Provider (sorted by median)', fontsize=13, fontweight='bold')

        # Add legend with outlier explanation
        from matplotlib.lines import Line2D
        legend_handles = [
            Line2D([0], [0], color='red', linestyle='--', linewidth=2, label=f'Event Horizon ({EVENT_HORIZON})'),
            Line2D([0], [0], marker='o', color='w', markerfacecolor='none', markeredgecolor='gray',
                   markersize=8, label='Outliers (>1.5×IQR)')
        ]
        ax2.legend(handles=legend_handles, loc='upper right', fontsize=10)
        ax2.grid(True, alpha=0.3, axis='y')

        # Scale right panel based on its own data for better resolution
        all_provider_peaks = [p for peaks in provider_peaks for p in peaks]
        if all_provider_peaks:
            panel2_max = max(all_provider_peaks) * 1.15
            panel2_max = max(panel2_max, EVENT_HORIZON + 0.1)  # At least show EH
            panel2_max = min(panel2_max, 2.0)  # Cap at cosine max
        else:
            panel2_max = ax_max
        ax2.set_ylim(0, panel2_max)

    # Overall title
    stable_count = sum(1 for t in trajectories if t.get('status') == 'STABLE')
    volatile_count = sum(1 for t in trajectories if t.get('status') == 'VOLATILE')
    fig.suptitle(f'Run {run_id}: {title_suffix}\n'
                f'{len(trajectories)} Ships | STABLE: {stable_count} | VOLATILE: {volatile_count} | EH={EVENT_HORIZON}',
                fontsize=15, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_{filename_suffix}.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_{filename_suffix}.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_{filename_suffix}.png + .svg")
    plt.close()


def plot_stability_boxplots(trajectories, output_dir, run_id, zoom_scale=None):
    """Stability box plots: generates TWO separate high-resolution visualizations.

    1. By Ship - Drift distribution per ship (all ships, sorted by mean)
    2. By Provider - Peak drift per provider (aggregated)

    Both visualizations include ALL ships for maximum resolution.
    """
    if not trajectories:
        return

    # Generate by-ship visualization
    _plot_boxplots_byship(trajectories, output_dir, run_id, zoom_scale)

    # Generate by-provider visualization
    _plot_boxplots_byprovider(trajectories, output_dir, run_id, zoom_scale)


def _plot_boxplots_byship(trajectories, output_dir, run_id, zoom_scale):
    """Single-panel boxplot: Drift distribution by ship (all ships)."""
    if not trajectories:
        return

    # Auto-scale axis limits
    if zoom_scale:
        ax_max = zoom_scale
    else:
        all_max_drifts = [max(t['drifts']) for t in trajectories if t.get('drifts')]
        if all_max_drifts:
            data_max = max(all_max_drifts)
            ax_max = max(data_max * 1.2, EVENT_HORIZON + 0.15)
            ax_max = min(ax_max, 2.0)
        else:
            ax_max = 1.2

    fig, ax = plt.subplots(figsize=(16, 8))

    ship_data = []
    ship_names = []
    ship_colors = []

    for traj in sorted(trajectories, key=lambda t: np.mean(t['drifts'])):
        ship_data.append(traj['drifts'])
        # Shorten ship name for display
        short_name = traj['ship']
        # Remove provider prefixes for cleaner labels
        if '/' in short_name:
            short_name = short_name.split('/')[-1]
        short_name = short_name.replace('claude-', 'c-').replace('gpt-', 'g-')
        short_name = short_name.replace('gemini-', 'gem-').replace('grok-', 'grk-')
        short_name = short_name.replace('-20241022', '').replace('-20251001', '')
        short_name = short_name.replace('-Instruct-Turbo', '').replace('-Instruct', '')
        short_name = short_name.replace('-Turbo', '').replace('-Distill-', '-')
        if len(short_name) > 18:
            short_name = short_name[:16] + '..'
        ship_names.append(short_name)
        ship_colors.append(PROVIDER_COLORS.get(traj['provider'], 'gray'))

    if ship_data:
        bp = ax.boxplot(ship_data, patch_artist=True, vert=True)

        for patch, color in zip(bp['boxes'], ship_colors):
            patch.set_facecolor(color)
            patch.set_alpha(0.7)

        ax.set_xticklabels(ship_names, rotation=55, ha='right', fontsize=9)
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
                   label=f'Event Horizon ({EVENT_HORIZON})')
        ax.set_ylabel('Drift (Cosine Distance)', fontsize=12)
        ax.set_xlabel('Ship (sorted by mean drift)', fontsize=12)
        ax.legend(loc='upper left', fontsize=10)
        ax.grid(True, alpha=0.3, axis='y')
        ax.set_ylim(0, ax_max)

    # Title with stats
    stable_count = sum(1 for t in trajectories if t.get('status') == 'STABLE')
    volatile_count = sum(1 for t in trajectories if t.get('status') == 'VOLATILE')
    ax.set_title(f'Run {run_id}: Drift Distribution by Ship\n'
                 f'{len(trajectories)} Ships | STABLE: {stable_count} | VOLATILE: {volatile_count} | EH={EVENT_HORIZON}',
                 fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_stability_boxplots_byship.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_stability_boxplots_byship.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_stability_boxplots_byship.png + .svg")
    plt.close()


def _plot_boxplots_byprovider(trajectories, output_dir, run_id, zoom_scale):
    """Single-panel boxplot: Peak drift by provider (all ships aggregated)."""
    if not trajectories:
        return

    from matplotlib.lines import Line2D

    # Group by provider
    provider_data = defaultdict(lambda: {'max_drifts': []})
    for traj in trajectories:
        provider = traj['provider']
        drifts = traj['drifts']
        if len(drifts) >= 2:
            provider_data[provider]['max_drifts'].append(max(drifts))

    # Sort providers by median drift
    provider_order = sorted(provider_data.keys(),
                           key=lambda p: np.median(provider_data[p]['max_drifts']) if provider_data[p]['max_drifts'] else 0)

    provider_peaks = []
    provider_labels = []
    provider_colors_list = []

    provider_names = {
        'claude': 'Claude', 'gpt': 'GPT', 'gemini': 'Gemini', 'grok': 'Grok',
        'meta-llama': 'Llama', 'mistralai': 'Mistral', 'deepseek': 'DeepSeek',
        'qwen': 'Qwen', 'moonshotai': 'Moonshot'
    }

    for provider in provider_order:
        if provider in provider_data and provider_data[provider]['max_drifts']:
            provider_peaks.append(provider_data[provider]['max_drifts'])
            n = len(provider_data[provider]['max_drifts'])
            label = provider_names.get(provider, provider.title())
            provider_labels.append(f'{label}\n({n} ships)')
            provider_colors_list.append(PROVIDER_COLORS.get(provider, 'gray'))

    if not provider_peaks:
        return

    fig, ax = plt.subplots(figsize=(12, 8))

    # Style outliers to be more visible and match legend
    flierprops = dict(marker='o', markerfacecolor='none', markeredgecolor='gray',
                     markersize=6, alpha=0.6, linestyle='none')
    bp = ax.boxplot(provider_peaks, patch_artist=True, vert=True, widths=0.6,
                    flierprops=flierprops)

    for patch, color in zip(bp['boxes'], provider_colors_list):
        patch.set_facecolor(color)
        patch.set_alpha(0.7)

    ax.set_xticklabels(provider_labels, fontsize=11)
    ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax.set_ylabel('Peak Drift (Cosine Distance)', fontsize=12)
    ax.set_xlabel('Provider (sorted by median peak drift)', fontsize=12)

    # Add legend with outlier explanation
    legend_handles = [
        Line2D([0], [0], color='red', linestyle='--', linewidth=2, label=f'Event Horizon ({EVENT_HORIZON})'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='none', markeredgecolor='gray',
               markersize=8, label='Outliers (>1.5x IQR)')
    ]
    ax.legend(handles=legend_handles, loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')

    # Auto-fit y-axis to data range for better resolution (don't force start at 0)
    all_provider_peaks = [p for peaks in provider_peaks for p in peaks]
    if all_provider_peaks:
        data_min = min(all_provider_peaks)
        data_max = max(all_provider_peaks)
        data_range = data_max - data_min
        # Add 15% padding on each side
        ax_min = max(0, data_min - data_range * 0.15)
        ax_max = data_max + data_range * 0.15
        # Ensure Event Horizon is visible
        ax_max = max(ax_max, EVENT_HORIZON + 0.05)
        ax_min = min(ax_min, EVENT_HORIZON - 0.05) if EVENT_HORIZON > data_min else ax_min
        ax_max = min(ax_max, 2.0)  # Cap at cosine max
    else:
        ax_min, ax_max = 0, 1.2
    ax.set_ylim(ax_min, ax_max)

    # Title with stats
    stable_count = sum(1 for t in trajectories if t.get('status') == 'STABLE')
    volatile_count = sum(1 for t in trajectories if t.get('status') == 'VOLATILE')
    ax.set_title(f'Run {run_id}: Peak Drift by Provider\n'
                 f'{len(trajectories)} Ships | STABLE: {stable_count} | VOLATILE: {volatile_count} | EH={EVENT_HORIZON}',
                 fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_stability_boxplots_byprovider.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_stability_boxplots_byprovider.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_stability_boxplots_byprovider.png + .svg")
    plt.close()


def _plot_pillar_analysis_single(trajectories, output_dir, run_id, zoom_scale, title_suffix, filename_suffix):
    """Helper function to create a single pillar analysis visualization for a subset of trajectories.

    Creates 4-panel visualization:
    1. 3-Pillar structure with provider centroids
    2. Extended pillars (by individual model)
    3. Angular distribution histogram
    4. Pillar stability (distance from Event Horizon)
    """
    from matplotlib.lines import Line2D

    if not trajectories:
        return

    # Auto-scale axis limits based on data if not specified
    if zoom_scale:
        ax_lim = zoom_scale
    else:
        # Find max drift across all trajectories
        all_drifts = []
        for traj in trajectories:
            all_drifts.extend(traj.get('drifts', []))
        if all_drifts:
            max_drift = max(all_drifts)
            # Set axis limit to max drift + 20% padding, at least EVENT_HORIZON + 0.2
            ax_lim = max(max_drift * 1.2, EVENT_HORIZON + 0.2)
            ax_lim = min(ax_lim, 2.0)  # Cap at 2.0 for cosine distance
        else:
            ax_lim = 1.2  # Default for cosine methodology

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

    # Dynamically determine providers from data
    providers = list(provider_stats.keys())
    provider_names = {
        'claude': 'Claude', 'gpt': 'GPT', 'gemini': 'Gemini', 'grok': 'Grok',
        'meta-llama': 'Llama', 'mistralai': 'Mistral', 'deepseek': 'DeepSeek',
        'qwen': 'Qwen', 'moonshotai': 'Moonshot'
    }

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
            'r--', linewidth=2.5, alpha=0.7, label=f'Event Horizon ({EVENT_HORIZON})')
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

    # Smart labeling with adjustText to avoid overlaps
    if all_ship_data:
        try:
            from adjustText import adjust_text
            texts = []
            for ship_data in all_ship_data:
                sx, sy = ship_data['x'], ship_data['y']
                ship = ship_data['ship']
                # Shorter labels for readability
                label = ship.replace('claude-', '').replace('gpt-', '').replace('gemini-', '').replace('grok-', '')
                label = label.replace('-20241022', '').replace('-20251001', '')  # Remove date suffixes
                label = label[:10] + '..' if len(label) > 10 else label
                txt = ax2.text(sx, sy, label, fontsize=6, alpha=0.85)
                texts.append(txt)

            # Adjust text positions to avoid overlaps - stronger forces for tight clusters
            adjust_text(texts, ax=ax2,
                       arrowprops=dict(arrowstyle='-', color='gray', alpha=0.4, lw=0.5),
                       expand_points=(2.0, 2.0),
                       expand_text=(1.5, 1.5),
                       force_text=(1.0, 1.0),
                       force_points=(0.5, 0.5),
                       lim=500)  # More iterations for better placement
        except ImportError:
            # Fallback: radial labeling without adjustText
            for i, ship_data in enumerate(all_ship_data):
                sx, sy = ship_data['x'], ship_data['y']
                ship = ship_data['ship']
                label = ship[:12] + '..' if len(ship) > 12 else ship
                # Offset labels radially outward
                angle = np.arctan2(sy, sx) + (i % 5) * 0.2  # Spread labels
                offset_x = 15 * np.cos(angle)
                offset_y = 15 * np.sin(angle)
                ax2.annotate(label, (sx, sy), fontsize=6, alpha=0.7,
                            xytext=(offset_x, offset_y), textcoords='offset points',
                            arrowprops=dict(arrowstyle='-', color='gray', alpha=0.3, lw=0.5))

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
    ax4.set_title('PILLAR STABILITY\n(Positive = safely below Event Horizon)', fontsize=14, fontweight='bold')
    ax4.legend(loc='upper right', fontsize=9)
    ax4.grid(True, alpha=0.3, axis='y')
    ax4.set_ylim(-1, 1.5)

    # Count ships and classification
    stable_count = sum(1 for t in trajectories if t.get('status') == 'STABLE')
    volatile_count = sum(1 for t in trajectories if t.get('status') == 'VOLATILE')

    fig.suptitle(f'Run {run_id}: PILLAR ANALYSIS - {title_suffix}\n'
                f'{len(trajectories)} Ships | STABLE: {stable_count} | VOLATILE: {volatile_count} | EH={EVENT_HORIZON}',
                fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()
    plt.savefig(output_dir / f'run{run_id}_{filename_suffix}.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / f'run{run_id}_{filename_suffix}.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: run{run_id}_{filename_suffix}.png + .svg")
    plt.close()


def plot_pillar_analysis(trajectories, output_dir, run_id, zoom_scale=None):
    """Pillar analysis: generates THREE separate visualizations.

    1. Native API models (Claude, GPT, Gemini, Grok) - direct API access
    2. Together.ai models (Llama, Mistral, DeepSeek, Qwen, Moonshot) - via Together.ai
    3. Combined (all ships together)
    """
    # Split trajectories by API type
    # Together.ai models have '/' in their full_model name (e.g., "meta-llama/Llama-3.3-70B")
    native_trajectories = [t for t in trajectories if '/' not in t.get('full_model', t['ship'])]
    together_trajectories = [t for t in trajectories if '/' in t.get('full_model', t['ship'])]

    # Generate native API plot
    if native_trajectories:
        _plot_pillar_analysis_single(
            native_trajectories, output_dir, run_id, zoom_scale,
            title_suffix="Native API Models (Claude, GPT, Gemini, Grok)",
            filename_suffix="pillar_analysis_native"
        )

    # Generate Together.ai plot
    if together_trajectories:
        _plot_pillar_analysis_single(
            together_trajectories, output_dir, run_id, zoom_scale,
            title_suffix="Together.ai Models (Llama, Mistral, DeepSeek, Qwen, Moonshot)",
            filename_suffix="pillar_analysis_together"
        )

    # Generate combined plot (all ships)
    if trajectories:
        _plot_pillar_analysis_single(
            trajectories, output_dir, run_id, zoom_scale,
            title_suffix="All Ships Combined",
            filename_suffix="pillar_analysis"
        )


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
        name='Event Horizon'
    ))

    fig.update_layout(
        title=f"Run {run_id}: Interactive 3D Identity Basin<br>(Red cylinder = Event Horizon at {EVENT_HORIZON})",
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
        name=f'Event Horizon ({EVENT_HORIZON})'
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
    # Structure: pics/1_Vortex/, pics/2_Boundary_Mapping/, pics/3_Stability/, etc.
    output_dirs = {
        'vortex': OUTPUT_DIR / '1_Vortex',
        'phase': OUTPUT_DIR / '2_Boundary_Mapping',
        '3d': OUTPUT_DIR / '2_Boundary_Mapping',
        'pillar': OUTPUT_DIR / '3_Stability',
        'stability': OUTPUT_DIR / '3_Stability',
        'html': OUTPUT_DIR / '6_Architecture',
        'fft': OUTPUT_DIR / '9_FFT_Spectral',
        'radar': OUTPUT_DIR / '7_Radar',
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
            plot_stability_boxplots(trajectories, output_dirs['stability'], run_id, zoom_scale=zoom_scale)

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
