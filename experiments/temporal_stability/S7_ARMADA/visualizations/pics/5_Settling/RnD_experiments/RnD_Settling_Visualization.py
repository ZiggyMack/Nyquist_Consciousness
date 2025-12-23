"""
R&D Visualization Experiments for 5_Settling
==============================================

Advanced signal processing visualizations for settling time analysis.
These are experimental - user will review and decide which to include.

Visualizations:
1. WATERFALL PLOT - 3D time-frequency-amplitude (if temporal resolution permits)
2. PHASE-PLANE PLOT - drift vs d(drift)/dt showing attractor dynamics
3. FFT OF SETTLING CURVES - Frequency content of settling oscillations
4. CONSISTENCY ENVELOPE - Overlaid trajectories showing bundle coherence

DATA SOURCE NOTE (2025-12-21):
==============================
Now using Run 023d data with FULL 20-PROBE extended settling!
- Waterfall plots: Full temporal resolution (20 time points)
- FFT spectral analysis: Sufficient data for meaningful spectrogram
- Oobleck controllability: Captured for non-settling models

Run 023d: 750 experiments (25 ships x 30 iterations) COMPLETE.

Created: 2025-12-20
Author: Claude Code (Anthropic)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict
from scipy import signal
from scipy.fft import fft, fftfreq

# ============================================================================
# CONFIGURATION
# ============================================================================

DATA_FILE = Path(__file__).parent.parent.parent.parent.parent / \
    "15_IRON_CLAD_FOUNDATION" / "results" / "S7_run_023d_CURRENT.json"

OUTPUT_DIR = Path(__file__).parent  # Same folder as this script

EVENT_HORIZON = 0.80  # Cosine threshold

PROVIDER_COLORS = {
    'anthropic': '#E07B39',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#FF6B6B',
    'deepseek': '#7C3AED',
    'mistral': '#FF8C00',
    'alibaba': '#FF4500',
}

# ============================================================================
# DATA LOADING
# ============================================================================

def load_settling_data():
    """Load and filter settling experiment results."""
    with open(DATA_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)

    settling_results = []
    for result in data.get('results', []):
        # Support both 'settling' (023b) and 'extended_settling' (023d)
        exp_type = result.get('experiment', '')
        if exp_type in ('settling', 'extended_settling'):
            settling_results.append(result)

    print(f"Loaded {len(settling_results)} settling results")
    return settling_results

def extract_drift_timeseries(result, skip_baseline=False):
    """Extract drift values from probe sequence as time series.

    Args:
        result: Experiment result dict
        skip_baseline: If True, skip baseline probes (useful for 023d extended settling)
    """
    probe_seq = result.get('probe_sequence', [])
    drift_values = []
    for p in probe_seq:
        # Skip baseline probes if requested (they're always 0 in 023d)
        # Check both 'type' (legacy) and 'probe_type' (023d format)
        probe_type = p.get('probe_type', p.get('type', ''))
        if skip_baseline and probe_type == 'baseline':
            continue
        drift = p.get('drift', p.get('peak_drift', 0))
        if drift is not None:
            drift_values.append(float(drift))
    return np.array(drift_values)

# ============================================================================
# 1. WATERFALL PLOT - 3D Time-Frequency-Amplitude
# ============================================================================

def get_pastel_cmap(dark_mode=True):
    """Create consistent colormap for all waterfall plots.

    Args:
        dark_mode: If True, use vibrant colors suitable for dark backgrounds
    """
    from matplotlib.colors import LinearSegmentedColormap

    if dark_mode:
        # Blue → Purple → Magenta → Red gradient (no yellow-green!)
        # Clean, professional, high contrast on dark backgrounds
        colors = [
            '#4FC3F7',  # Light blue (stable/low drift)
            '#7E57C2',  # Purple (moderate)
            '#E040FB',  # Magenta (warning zone)
            '#FF5252',  # Red (high drift/unstable)
        ]
        bad_color = '#3D3D3D'  # Medium gray for NaN (settled early)
    else:
        # Original pastels for light mode
        colors = [
            '#98D8AA',  # Soft mint green (stable/low drift)
            '#C4E4C1',  # Light sage
            '#F5F5DC',  # Cream/beige (neutral)
            '#FFDAB9',  # Peach puff
            '#E8A0A0',  # Soft coral/rose (high drift)
        ]
        bad_color = '#D0D0D0'  # Light gray for NaN

    cmap = LinearSegmentedColormap.from_list('drift_cmap', colors)
    cmap.set_bad(color=bad_color)
    return cmap


# Use dark mode by default
DARK_MODE = True
BG_COLOR = '#1E1E1E' if DARK_MODE else 'white'
TEXT_COLOR = '#E8E8E8' if DARK_MODE else 'black'
GRID_COLOR = '#404040' if DARK_MODE else 'white'


def generate_waterfall_plot(results):
    """
    WATERFALL PLOT: 3D visualization showing multiple settling curves stacked.

    Each horizontal "slice" represents one ship's settling trajectory.
    X-axis: Probe number (time)
    Y-axis: Ship index (stacked)
    Color: Drift amplitude

    This reveals patterns across the fleet - do certain ships settle faster?
    Are there common inflection points where all ships show transitions?
    """
    print("\n[1/4] Generating WATERFALL PLOT...")

    # Group by model - skip baseline probes (always 0 in 023d)
    by_model = defaultdict(list)
    for r in results:
        model = r.get('model', 'unknown')
        drift_ts = extract_drift_timeseries(r, skip_baseline=True)
        if len(drift_ts) > 0:
            by_model[model].append(drift_ts)

    # Create waterfall data matrix
    max_probes = 21  # Step input + 20 recovery probes
    ships = sorted(by_model.keys())[:25]  # Limit to 25 ships for clarity

    waterfall_matrix = np.zeros((len(ships), max_probes))
    waterfall_matrix[:] = np.nan  # Use NaN for missing data

    for i, ship in enumerate(ships):
        if by_model[ship]:
            # FIXED: Average across ALL iterations for this ship
            all_ts = by_model[ship]
            avg_ts = np.zeros(max_probes)
            count = np.zeros(max_probes)

            for ts in all_ts:
                length = min(len(ts), max_probes)
                avg_ts[:length] += ts[:length]
                count[:length] += 1

            # Average where we have data
            with np.errstate(divide='ignore', invalid='ignore'):
                avg_ts = np.where(count > 0, avg_ts / count, np.nan)
            waterfall_matrix[i] = avg_ts

    # Create figure with dark background
    fig = plt.figure(figsize=(14, 10), facecolor=BG_COLOR)

    # Use dark-mode colormap
    drift_cmap = get_pastel_cmap(dark_mode=DARK_MODE)

    # 2D heatmap view (waterfall seen from above)
    ax1 = fig.add_subplot(211)
    ax1.set_facecolor(BG_COLOR)
    im = ax1.imshow(waterfall_matrix, aspect='auto', cmap=drift_cmap,
                    vmin=0, vmax=1.0, interpolation='nearest')

    # Add subtle grid for readability
    ax1.set_xticks(np.arange(-0.5, max_probes, 1), minor=True)
    ax1.set_yticks(np.arange(-0.5, len(ships), 1), minor=True)
    ax1.grid(which='minor', color=GRID_COLOR, linestyle='-', linewidth=0.3, alpha=0.5)

    ax1.set_xlabel('Recovery Phase (Step input + recovery probes)', fontsize=11, color=TEXT_COLOR)
    ax1.set_ylabel('Ship (stacked)', fontsize=11, color=TEXT_COLOR)
    ax1.set_title('WATERFALL VIEW: Fleet Settling Dynamics\n' +
                  '(Each row = one ship, averaged across N=30 iterations)',
                  fontsize=11, color=TEXT_COLOR)
    ax1.tick_params(colors=TEXT_COLOR)

    # Colorbar with EH marker
    cbar = plt.colorbar(im, ax=ax1, shrink=0.8)
    cbar.set_label('Drift (cosine)', fontsize=10, color=TEXT_COLOR)
    cbar.ax.axhline(y=EVENT_HORIZON, color='#FFD700', linewidth=2, linestyle='--')
    # Place EH label on left side of colorbar to avoid overlap with label
    cbar.ax.text(-0.5, EVENT_HORIZON, f'EH', fontsize=8, va='center', ha='right', color='#FFD700')
    cbar.ax.tick_params(colors=TEXT_COLOR)

    # Legend explaining colors
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='#4FC3F7', edgecolor='#888', label='Stable (low drift)'),
        Patch(facecolor='#FF5252', edgecolor='#888', label='Unstable (high drift)'),
        Patch(facecolor='#3D3D3D', edgecolor='#888', label='Settled Early')
    ]
    leg = ax1.legend(handles=legend_elements, loc='upper right', fontsize=8,
                     framealpha=0.9, facecolor='#2A2A2A', edgecolor='#555',
                     labelcolor=TEXT_COLOR, title='Legend', title_fontsize=9)
    leg.get_title().set_color(TEXT_COLOR)

    # Y-axis labels (ship names)
    short_names = [s[:15] + '..' if len(s) > 17 else s for s in ships]
    ax1.set_yticks(range(len(ships)))
    ax1.set_yticklabels(short_names, fontsize=7, color=TEXT_COLOR)

    # X-axis labels
    x_labels = ['Step'] + [str(i) for i in range(1, max_probes)]
    ax1.set_xticks(range(max_probes))
    ax1.set_xticklabels(x_labels, fontsize=8, color=TEXT_COLOR)

    # 3D surface view
    ax2 = fig.add_subplot(212, projection='3d')
    ax2.set_facecolor(BG_COLOR)

    X = np.arange(max_probes)
    Y = np.arange(len(ships))
    X, Y = np.meshgrid(X, Y)

    # Replace NaN with 0 for surface plot
    Z = np.nan_to_num(waterfall_matrix, nan=0)

    surf = ax2.plot_surface(X, Y, Z, cmap=drift_cmap,
                            linewidth=0.1, antialiased=True, alpha=0.8,
                            vmin=0, vmax=1.0)

    # Note: EH plane removed for cleaner visualization - EH shown on colorbar instead

    ax2.set_xlabel('Probe Number', fontsize=10, color=TEXT_COLOR)
    ax2.set_ylabel('Ship Index', fontsize=10, color=TEXT_COLOR)
    ax2.set_zlabel('Drift', fontsize=10, color=TEXT_COLOR)
    ax2.set_title('3D WATERFALL: Settling Surface Topology', fontsize=11, color=TEXT_COLOR)
    ax2.tick_params(colors=TEXT_COLOR)
    ax2.view_init(elev=25, azim=-60)

    plt.tight_layout()
    output_path = OUTPUT_DIR / 'waterfall_settling_fleet.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor=BG_COLOR, edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path


def generate_provider_waterfall_plots(results):
    """
    PER-PROVIDER WATERFALL PLOTS: 3D surface topology per provider.

    Shows the identity manifold topology for each provider - the shape of
    settling dynamics rendered as a 3D surface.
    """
    print("\n[1b/4] Generating PER-PROVIDER WATERFALL PLOTS (3D Surface Only)...")

    # Group results by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        by_provider[provider].append(r)

    providers = sorted(by_provider.keys())
    drift_cmap = get_pastel_cmap(dark_mode=DARK_MODE)
    max_probes = 21

    output_paths = []

    for provider in providers:
        provider_results = by_provider[provider]

        # Group by model within this provider
        by_model = defaultdict(list)
        for r in provider_results:
            model = r.get('model', 'unknown')
            drift_ts = extract_drift_timeseries(r, skip_baseline=True)
            if len(drift_ts) > 0:
                by_model[model].append(drift_ts)

        ships = sorted(by_model.keys())
        if not ships:
            continue

        # Build matrix
        waterfall_matrix = np.zeros((len(ships), max_probes))
        waterfall_matrix[:] = np.nan

        for i, ship in enumerate(ships):
            if by_model[ship]:
                all_ts = by_model[ship]
                avg_ts = np.zeros(max_probes)
                count = np.zeros(max_probes)

                for ts in all_ts:
                    length = min(len(ts), max_probes)
                    avg_ts[:length] += ts[:length]
                    count[:length] += 1

                with np.errstate(divide='ignore', invalid='ignore'):
                    avg_ts = np.where(count > 0, avg_ts / count, np.nan)
                waterfall_matrix[i] = avg_ts

        # Provider-specific color (brighter for dark background)
        provider_colors_bright = {
            'anthropic': '#FF9966',  # Brighter orange
            'openai': '#40E0D0',     # Turquoise
            'google': '#87CEEB',     # Sky blue
            'xai': '#FF6B6B',        # Coral red
            'together': '#DDA0DD',   # Plum
        }
        provider_color = provider_colors_bright.get(provider, '#E0E0E0')

        # Create figure with just 3D surface
        fig = plt.figure(figsize=(10, 8), facecolor=BG_COLOR)
        ax = fig.add_subplot(111, projection='3d')
        ax.set_facecolor(BG_COLOR)

        X = np.arange(max_probes)
        Y = np.arange(len(ships))
        X, Y = np.meshgrid(X, Y)

        # Replace NaN with 0 for surface plot
        Z = np.nan_to_num(waterfall_matrix, nan=0)

        surf = ax.plot_surface(X, Y, Z, cmap=drift_cmap,
                               linewidth=0.1, antialiased=True, alpha=0.8,
                               vmin=0, vmax=1.0)

        # Note: EH plane removed for cleaner visualization - EH shown on colorbar instead

        ax.set_xlabel('Probe Number', fontsize=11, color=TEXT_COLOR)
        ax.set_ylabel('Ship Index', fontsize=11, color=TEXT_COLOR)
        ax.set_zlabel('Drift', fontsize=11, color=TEXT_COLOR)
        ax.set_title(f'{provider.upper()} Identity Manifold\n' +
                     f'({len(ships)} ships, N=30 iterations averaged)',
                     fontsize=13, fontweight='bold', color=provider_color)
        ax.tick_params(colors=TEXT_COLOR)
        ax.view_init(elev=25, azim=-60)

        # Add colorbar
        cbar = fig.colorbar(surf, ax=ax, shrink=0.6, pad=0.1)
        cbar.set_label('Drift (cosine)', fontsize=10, color=TEXT_COLOR)
        cbar.ax.axhline(y=EVENT_HORIZON, color='#FFD700', linewidth=2, linestyle='--')
        cbar.ax.tick_params(colors=TEXT_COLOR)

        plt.tight_layout()

        output_path = OUTPUT_DIR / f'waterfall_{provider}.png'
        plt.savefig(output_path, dpi=150, bbox_inches='tight',
                    facecolor=BG_COLOR, edgecolor='none')
        plt.close()
        print(f"   Saved: {output_path}")
        output_paths.append(output_path)

    return output_paths


def generate_combined_provider_waterfalls(results):
    """
    COMBINED PROVIDER WATERFALLS: All 5 providers in one figure.

    Shows all identity manifolds side-by-side for easy comparison.
    2 rows x 3 columns layout (5 providers + 1 empty or legend).
    """
    print("\n[1c/4] Generating COMBINED PROVIDER WATERFALLS...")

    # Group results by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        by_provider[provider].append(r)

    providers = sorted(by_provider.keys())
    drift_cmap = get_pastel_cmap(dark_mode=DARK_MODE)
    max_probes = 21

    # Provider-specific colors
    provider_colors_bright = {
        'anthropic': '#FF9966',
        'openai': '#40E0D0',
        'google': '#87CEEB',
        'xai': '#FF6B6B',
        'together': '#DDA0DD',
    }

    # Create figure with 2x3 subplots
    fig = plt.figure(figsize=(18, 12), facecolor=BG_COLOR)

    for idx, provider in enumerate(providers[:5]):
        provider_results = by_provider[provider]

        # Group by model
        by_model = defaultdict(list)
        for r in provider_results:
            model = r.get('model', 'unknown')
            drift_ts = extract_drift_timeseries(r, skip_baseline=True)
            if len(drift_ts) > 0:
                by_model[model].append(drift_ts)

        ships = sorted(by_model.keys())
        if not ships:
            continue

        # Build matrix
        waterfall_matrix = np.zeros((len(ships), max_probes))
        waterfall_matrix[:] = np.nan

        for i, ship in enumerate(ships):
            if by_model[ship]:
                all_ts = by_model[ship]
                avg_ts = np.zeros(max_probes)
                count = np.zeros(max_probes)
                for ts in all_ts:
                    length = min(len(ts), max_probes)
                    avg_ts[:length] += ts[:length]
                    count[:length] += 1
                with np.errstate(divide='ignore', invalid='ignore'):
                    avg_ts = np.where(count > 0, avg_ts / count, np.nan)
                waterfall_matrix[i] = avg_ts

        provider_color = provider_colors_bright.get(provider, '#E0E0E0')

        # Subplot position (2 rows x 3 cols)
        ax = fig.add_subplot(2, 3, idx + 1, projection='3d')
        ax.set_facecolor(BG_COLOR)

        X = np.arange(max_probes)
        Y = np.arange(len(ships))
        X, Y = np.meshgrid(X, Y)
        Z = np.nan_to_num(waterfall_matrix, nan=0)

        surf = ax.plot_surface(X, Y, Z, cmap=drift_cmap,
                               linewidth=0.1, antialiased=True, alpha=0.8,
                               vmin=0, vmax=1.0)

        ax.set_xlabel('Probe', fontsize=9, color=TEXT_COLOR)
        ax.set_ylabel('Ship', fontsize=9, color=TEXT_COLOR)
        ax.set_zlabel('Drift', fontsize=9, color=TEXT_COLOR)
        ax.set_title(f'{provider.upper()}\n({len(ships)} ships)',
                     fontsize=11, fontweight='bold', color=provider_color)
        ax.tick_params(colors=TEXT_COLOR, labelsize=7)
        ax.view_init(elev=25, azim=-60)

    # Add legend/info in 6th subplot
    ax6 = fig.add_subplot(2, 3, 6)
    ax6.set_facecolor(BG_COLOR)
    ax6.axis('off')

    # Add colorbar for reference
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='#4FC3F7', edgecolor='#888', label='Stable (low drift)'),
        Patch(facecolor='#7E57C2', edgecolor='#888', label='Moderate drift'),
        Patch(facecolor='#E040FB', edgecolor='#888', label='Warning zone'),
        Patch(facecolor='#FF5252', edgecolor='#888', label='Unstable (high drift)'),
    ]
    leg = ax6.legend(handles=legend_elements, loc='center', fontsize=10,
                     framealpha=0.9, facecolor='#2A2A2A', edgecolor='#555',
                     labelcolor=TEXT_COLOR, title='Drift Scale', title_fontsize=12)
    leg.get_title().set_color(TEXT_COLOR)

    ax6.text(0.5, 0.15, 'Event Horizon (EH) = 0.80\nN=30 iterations averaged',
             ha='center', va='center', fontsize=10, color=TEXT_COLOR,
             transform=ax6.transAxes)

    plt.suptitle('PROVIDER IDENTITY MANIFOLDS: Comparative 3D Topology\n' +
                 '(Each surface shows settling dynamics for one provider family)',
                 fontsize=14, fontweight='bold', color=TEXT_COLOR, y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.95])

    output_path = OUTPUT_DIR / 'waterfall_all_providers.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor=BG_COLOR, edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path


# ============================================================================
# 2. PHASE-PLANE PLOT - Drift vs d(Drift)/dt
# ============================================================================

def generate_phase_plane_plot(results):
    """
    PHASE-PLANE PLOT: Shows attractor dynamics in state space.

    X-axis: Drift value (position)
    Y-axis: d(drift)/dt (velocity) - rate of change

    This reveals:
    - Limit cycles (closed loops) = oscillatory settling
    - Spiral towards origin = damped settling
    - Strange attractors = chaotic behavior
    - Stable nodes = quick convergence

    The "attractor basin" becomes visible - where does identity settle?
    """
    print("\n[2/4] Generating PHASE-PLANE PLOT...")

    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()

    # Group by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 3:  # Need at least 3 points for derivative
            by_provider[provider].append(drift_ts)

    providers = list(by_provider.keys())[:6]  # Max 6 panels

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        color = PROVIDER_COLORS.get(provider, '#888888')

        all_trajectories = by_provider[provider]

        for i, drift_ts in enumerate(all_trajectories[:20]):  # Limit to 20 trajectories
            # Calculate derivative (velocity)
            velocity = np.gradient(drift_ts)

            # Plot trajectory
            alpha = 0.3 if i > 0 else 0.8
            lw = 1 if i > 0 else 2
            ax.plot(drift_ts, velocity, color=color, alpha=alpha, linewidth=lw)

            # Mark start and end
            if i == 0:
                ax.scatter(drift_ts[0], velocity[0], color=color, s=80,
                          marker='o', zorder=10, edgecolor='white', linewidth=1.5)
                ax.scatter(drift_ts[-1], velocity[-1], color=color, s=80,
                          marker='s', zorder=10, edgecolor='white', linewidth=1.5)

        # Event Horizon vertical line
        ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--',
                   alpha=0.7, linewidth=1.5, label=f'EH={EVENT_HORIZON}')

        # Zero velocity line (equilibrium)
        ax.axhline(y=0, color='gray', linestyle='-', alpha=0.5, linewidth=0.5)

        # Origin marker (ideal settled state)
        ax.scatter(0, 0, color='green', s=150, marker='*', zorder=20,
                  edgecolor='white', linewidth=2, label='Origin (stable)')

        ax.set_xlabel('Drift (position)', fontsize=10)
        ax.set_ylabel('d(Drift)/dt (velocity)', fontsize=10)
        ax.set_title(f'{provider.upper()}\n({len(all_trajectories)} trajectories)',
                    fontsize=11, fontweight='bold')
        ax.set_xlim(-0.1, 1.5)
        ax.set_ylim(-0.5, 0.5)
        ax.grid(True, alpha=0.3)

        if idx == 0:
            ax.legend(loc='upper right', fontsize=8)

    # Hide unused axes
    for idx in range(len(providers), 6):
        axes[idx].set_visible(False)

    plt.suptitle('PHASE-PLANE ANALYSIS: Identity Attractor Dynamics\n' +
                 '(Circle = start, Square = settled | Limited to 6 probes - Run 023d: 20 probes)',
                 fontsize=12, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'phase_plane_attractor.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path

# ============================================================================
# 3. FFT OF SETTLING CURVES - Frequency Content
# ============================================================================

def generate_fft_settling_plot(results):
    """
    FFT ANALYSIS: Frequency content of settling oscillations.

    This reveals:
    - Low frequency = gradual, smooth settling
    - High frequency = rapid oscillations, "jitter"
    - Multiple peaks = complex dynamics, resonance
    - Single peak = dominant mode

    Different providers may have characteristic "spectral fingerprints"
    in their settling behavior.
    """
    print("\n[3/4] Generating FFT OF SETTLING CURVES...")

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Collect all settling curves by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 4:  # Need minimum points for FFT
            by_provider[provider].append(drift_ts)

    # Panel 1: Individual FFT spectra by provider
    ax1 = axes[0, 0]
    max_freq_components = []

    for provider, trajectories in by_provider.items():
        if len(trajectories) < 3:
            continue

        color = PROVIDER_COLORS.get(provider, '#888888')

        # Average FFT across trajectories
        all_ffts = []
        for drift_ts in trajectories[:50]:  # Limit for speed
            # Zero-pad to consistent length
            n = 16
            padded = np.zeros(n)
            length = min(len(drift_ts), n)
            padded[:length] = drift_ts[:length]

            # Compute FFT
            yf = np.abs(fft(padded))[:n//2]
            xf = fftfreq(n, d=1.0)[:n//2]
            all_ffts.append(yf)

        if all_ffts:
            avg_fft = np.mean(all_ffts, axis=0)
            ax1.plot(xf, avg_fft, color=color, linewidth=2,
                    label=provider, alpha=0.8)

            # Track max frequency component
            max_idx = np.argmax(avg_fft[1:]) + 1  # Skip DC
            max_freq_components.append((provider, xf[max_idx], avg_fft[max_idx]))

    ax1.set_xlabel('Frequency (cycles per probe)', fontsize=11)
    ax1.set_ylabel('Magnitude', fontsize=11)
    ax1.set_title('FFT Spectra by Provider\n(Averaged across trajectories)', fontsize=12)
    ax1.legend(loc='upper right', fontsize=9)
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 0.5)

    # Panel 2: Power spectral density comparison
    ax2 = axes[0, 1]

    provider_powers = []
    for provider, trajectories in by_provider.items():
        total_power = 0
        for drift_ts in trajectories[:50]:
            n = len(drift_ts)
            if n >= 4:
                yf = np.abs(fft(drift_ts))
                total_power += np.sum(yf**2) / n
        avg_power = total_power / max(len(trajectories[:50]), 1)
        provider_powers.append((provider, avg_power))

    provider_powers.sort(key=lambda x: x[1], reverse=True)
    providers = [p[0] for p in provider_powers]
    powers = [p[1] for p in provider_powers]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    bars = ax2.bar(range(len(providers)), powers, color=colors, alpha=0.8)
    ax2.set_xticks(range(len(providers)))
    ax2.set_xticklabels(providers, rotation=45, ha='right', fontsize=9)
    ax2.set_ylabel('Total Spectral Power', fontsize=11)
    ax2.set_title('Settling Energy by Provider\n(Higher = more oscillation)', fontsize=12)
    ax2.grid(True, alpha=0.3, axis='y')

    # Panel 3: Spectrogram of single trajectory (detailed view)
    ax3 = axes[1, 0]

    # Find a trajectory with good length
    best_trajectory = None
    best_provider = None
    for provider, trajectories in by_provider.items():
        for t in trajectories:
            if len(t) >= 10 and (best_trajectory is None or len(t) > len(best_trajectory)):
                best_trajectory = t
                best_provider = provider

    if best_trajectory is not None:
        # Short-time FFT (spectrogram-like)
        nperseg = min(4, len(best_trajectory) // 2)
        if nperseg >= 2:
            f, t, Sxx = signal.spectrogram(best_trajectory, fs=1.0, nperseg=nperseg,
                                           noverlap=nperseg-1, mode='magnitude')
            im = ax3.pcolormesh(t, f, Sxx, shading='gouraud', cmap='viridis')
            ax3.set_ylabel('Frequency', fontsize=11)
            ax3.set_xlabel('Probe Number (Time)', fontsize=11)
            ax3.set_title(f'Spectrogram: {best_provider}\n(Time-frequency evolution)', fontsize=12)
            plt.colorbar(im, ax=ax3, label='Magnitude')
    else:
        ax3.text(0.5, 0.5, 'Insufficient data\nfor spectrogram',
                ha='center', va='center', fontsize=12)
        ax3.set_title('Spectrogram (unavailable)', fontsize=12)

    # Panel 4: Dominant frequency by provider
    ax4 = axes[1, 1]

    dom_freqs = []
    dom_labels = []
    dom_colors = []

    for provider, trajectories in by_provider.items():
        all_dom = []
        for drift_ts in trajectories[:50]:
            n = 16
            padded = np.zeros(n)
            length = min(len(drift_ts), n)
            padded[:length] = drift_ts[:length]

            yf = np.abs(fft(padded))[:n//2]
            xf = fftfreq(n, d=1.0)[:n//2]

            # Find dominant frequency (excluding DC)
            if len(yf) > 1:
                dom_idx = np.argmax(yf[1:]) + 1
                all_dom.append(xf[dom_idx])

        if all_dom:
            dom_freqs.append(np.mean(all_dom))
            dom_labels.append(provider)
            dom_colors.append(PROVIDER_COLORS.get(provider, '#888888'))

    ax4.bar(range(len(dom_labels)), dom_freqs, color=dom_colors, alpha=0.8)
    ax4.set_xticks(range(len(dom_labels)))
    ax4.set_xticklabels(dom_labels, rotation=45, ha='right', fontsize=9)
    ax4.set_ylabel('Dominant Frequency', fontsize=11)
    ax4.set_title('Settling "Pitch" by Provider\n(Higher = faster oscillation)', fontsize=12)
    ax4.grid(True, alpha=0.3, axis='y')

    plt.suptitle('FFT ANALYSIS: Frequency Content of Settling Dynamics\n' +
                 '(Run 023d: 750 experiments x 20+ probes)',
                 fontsize=12, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'fft_settling_analysis.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path

# ============================================================================
# 4. CONSISTENCY ENVELOPE - Overlaid Trajectories
# ============================================================================

def generate_consistency_envelope(results):
    """
    CONSISTENCY ENVELOPE: All trajectories overlaid, showing trajectory bundle coherence.

    Conceptually inspired by eye diagrams but adapted for our measurement paradigm:
    - Unlike digital signals, our trajectories are not periodic/repeating
    - Each experiment is a single path-dependent trajectory
    - We overlay N trajectories to show the "bundle" consistency

    The envelope shows:
    - Envelope Width = amplitude variability (tighter = more consistent)
    - Trajectory Spread = timing/path variance
    - Coherence = how tightly the bundle converges

    UPDATED: Shows Anthropic, OpenAI, Google, xAI, DeepSeek, Llama as the 6 panels
    (DeepSeek and Llama are both hosted on Together.ai but shown separately)
    """
    print("\n[4/4] Generating CONSISTENCY ENVELOPE...")

    fig, axes = plt.subplots(2, 3, figsize=(16, 10))
    axes = axes.flatten()

    # Group by provider, but split Together.ai into DeepSeek and Llama
    by_category = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        model = r.get('model', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 3:
            # For Together.ai, categorize by model family
            if provider == 'together':
                family = get_model_family(model)
                if family in ('DeepSeek', 'Llama'):
                    by_category[family].append(drift_ts)
                # Skip other Together.ai models for this view
            else:
                by_category[provider].append(drift_ts)

    # Show these 6 categories: Anthropic, OpenAI, Google, xAI, DeepSeek, Llama
    categories = ['anthropic', 'openai', 'google', 'xai', 'DeepSeek', 'Llama']

    # Colors for categories
    category_colors = {
        'anthropic': '#E07B39',
        'openai': '#10A37F',
        'google': '#4285F4',
        'xai': '#1DA1F2',
        'DeepSeek': '#7C3AED',  # Purple
        'Llama': '#FF6B6B',     # Coral red
    }

    for idx, category in enumerate(categories):
        ax = axes[idx]
        color = category_colors.get(category, '#888888')

        trajectories = by_category[category]

        # Normalize all trajectories to same length
        max_len = 15
        normalized = []

        for drift_ts in trajectories:
            # Interpolate to fixed length
            if len(drift_ts) >= 2:
                x_orig = np.linspace(0, 1, len(drift_ts))
                x_new = np.linspace(0, 1, max_len)
                interp = np.interp(x_new, x_orig, drift_ts)
                normalized.append(interp)

        if not normalized:
            ax.text(0.5, 0.5, 'No data', ha='center', va='center')
            ax.set_title(f'{provider}', fontsize=11)
            continue

        normalized = np.array(normalized)

        # Plot all trajectories (the "eye")
        for traj in normalized:
            ax.plot(range(max_len), traj, color=color, alpha=0.15, linewidth=0.8)

        # Calculate and plot envelope
        mean_traj = np.mean(normalized, axis=0)
        std_traj = np.std(normalized, axis=0)

        ax.plot(range(max_len), mean_traj, color=color, linewidth=3,
               label='Mean trajectory')
        ax.fill_between(range(max_len), mean_traj - std_traj, mean_traj + std_traj,
                       color=color, alpha=0.3, label='+-1 std')

        # Event Horizon
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--',
                  linewidth=2, alpha=0.7, label=f'EH={EVENT_HORIZON}')

        # Calculate envelope width metric (inverse = coherence)
        # Envelope width = average std across trajectory (lower = tighter bundle)
        envelope_width = np.mean(std_traj)

        # Coherence metric: how much margin to Event Horizon (higher = better)
        min_margin = np.min(EVENT_HORIZON - (mean_traj + std_traj))
        coherence = max(0, min_margin / EVENT_HORIZON) * 100

        # Jitter metric (crossing spread at 0.3 threshold)
        crossings = []
        for traj in normalized:
            for i in range(len(traj)-1):
                if (traj[i] < 0.3 and traj[i+1] >= 0.3) or (traj[i] >= 0.3 and traj[i+1] < 0.3):
                    crossings.append(i + (0.3 - traj[i]) / (traj[i+1] - traj[i]))
        jitter = np.std(crossings) if crossings else 0

        ax.set_xlabel('Normalized Time', fontsize=10)
        ax.set_ylabel('Drift', fontsize=10)
        ax.set_title(f'{category.upper()}\n' +
                    f'Envelope Width: {envelope_width:.2f} | Jitter: {jitter:.2f}',
                    fontsize=11, fontweight='bold')
        ax.set_ylim(-0.1, 1.5)
        ax.set_xlim(0, max_len-1)
        ax.grid(True, alpha=0.3)

        if idx == 0:
            ax.legend(loc='upper right', fontsize=8)

    # Hide unused axes
    for idx in range(len(categories), 6):
        axes[idx].set_visible(False)

    plt.suptitle('CONSISTENCY ENVELOPE: Trajectory Bundle Analysis\n' +
                 '(Anthropic, OpenAI, Google, xAI + DeepSeek & Llama from Together.ai)',
                 fontsize=12, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'consistency_envelope.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path

# ============================================================================
# 4b. CONSISTENCY ENVELOPE - Together.ai Model Families
# ============================================================================

def get_model_family(model_name):
    """Extract model family from full model name."""
    model_lower = model_name.lower()
    if 'deepseek' in model_lower:
        return 'DeepSeek'
    elif 'llama' in model_lower:
        return 'Llama'
    elif 'mistral' in model_lower or 'mixtral' in model_lower:
        return 'Mistral'
    elif 'qwen' in model_lower:
        return 'Qwen'
    elif 'kimi' in model_lower:
        return 'Kimi'
    elif 'nemotron' in model_lower:
        return 'Nvidia'
    else:
        return 'Other'


def generate_consistency_envelope_together(results):
    """
    CONSISTENCY ENVELOPE - Together.ai Focus

    Shows all the model families hosted on Together.ai:
    DeepSeek, Llama, Mistral, Qwen, Kimi, Nvidia, etc.
    """
    print("\n[4b] Generating CONSISTENCY ENVELOPE (Together.ai)...")

    # Filter to Together.ai results only
    together_results = [r for r in results if r.get('provider') == 'together']

    if not together_results:
        print("   No Together.ai data found!")
        return None

    # Model family colors
    family_colors = {
        'DeepSeek': '#7C3AED',  # Purple
        'Llama': '#FF6B6B',     # Coral red
        'Mistral': '#FF8C00',   # Orange
        'Qwen': '#10A37F',      # Teal
        'Kimi': '#4285F4',      # Blue
        'Nvidia': '#76B900',    # Nvidia green
        'Other': '#888888',     # Gray
    }

    fig, axes = plt.subplots(2, 3, figsize=(16, 10))
    axes = axes.flatten()

    # Group by model family
    by_family = defaultdict(list)
    for r in together_results:
        model = r.get('model', 'unknown')
        family = get_model_family(model)
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 3:
            by_family[family].append((model, drift_ts))

    families = ['DeepSeek', 'Llama', 'Mistral', 'Qwen', 'Kimi', 'Nvidia']

    for idx, family in enumerate(families):
        ax = axes[idx]
        color = family_colors.get(family, '#888888')

        trajectories_data = by_family.get(family, [])
        trajectories = [t[1] for t in trajectories_data]
        models_in_family = list(set([t[0] for t in trajectories_data]))

        # Normalize all trajectories to same length
        max_len = 15
        normalized = []

        for drift_ts in trajectories:
            if len(drift_ts) >= 2:
                x_orig = np.linspace(0, 1, len(drift_ts))
                x_new = np.linspace(0, 1, max_len)
                interp = np.interp(x_new, x_orig, drift_ts)
                normalized.append(interp)

        if not normalized:
            ax.text(0.5, 0.5, 'No data', ha='center', va='center', fontsize=12)
            ax.set_title(f'{family}', fontsize=11)
            continue

        normalized = np.array(normalized)

        # Plot all trajectories
        for traj in normalized:
            ax.plot(range(max_len), traj, color=color, alpha=0.15, linewidth=0.8)

        # Calculate and plot envelope
        mean_traj = np.mean(normalized, axis=0)
        std_traj = np.std(normalized, axis=0)

        ax.plot(range(max_len), mean_traj, color=color, linewidth=3,
               label='Mean trajectory')
        ax.fill_between(range(max_len), mean_traj - std_traj, mean_traj + std_traj,
                       color=color, alpha=0.3, label='±1 std')

        # Event Horizon
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--',
                  linewidth=2, alpha=0.7, label=f'EH={EVENT_HORIZON}')

        # Calculate metrics
        envelope_width = np.mean(std_traj)

        # Jitter metric
        crossings = []
        for traj in normalized:
            for i in range(len(traj)-1):
                if (traj[i] < 0.3 and traj[i+1] >= 0.3) or (traj[i] >= 0.3 and traj[i+1] < 0.3):
                    crossings.append(i + (0.3 - traj[i]) / (traj[i+1] - traj[i]))
        jitter = np.std(crossings) if crossings else 0

        ax.set_xlabel('Normalized Time', fontsize=10)
        ax.set_ylabel('Drift', fontsize=10)

        # Show model names in subtitle
        model_names = ', '.join([m.split('/')[-1][:20] for m in models_in_family[:3]])
        if len(models_in_family) > 3:
            model_names += f'... (+{len(models_in_family)-3})'

        ax.set_title(f'{family.upper()} ({len(normalized)} traj)\n' +
                    f'Width: {envelope_width:.2f} | Jitter: {jitter:.2f}',
                    fontsize=11, fontweight='bold')
        ax.set_ylim(-0.1, 1.5)
        ax.set_xlim(0, max_len-1)
        ax.grid(True, alpha=0.3)

        if idx == 0:
            ax.legend(loc='upper right', fontsize=8)

    # Hide unused axes
    for idx in range(len(families), 6):
        axes[idx].set_visible(False)

    plt.suptitle('CONSISTENCY ENVELOPE: Together.ai Model Families\n' +
                 '(DeepSeek, Llama, Mistral, Qwen, Kimi, Nvidia)',
                 fontsize=12, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'consistency_envelope_together.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path


# ============================================================================
# 5. SPECTROGRAM GALLERY - Per-Provider + Combined Fleet
# ============================================================================

def generate_spectrogram_gallery(results):
    """
    SPECTROGRAM GALLERY: Time-frequency evolution for each provider + combined fleet.

    Shows the "spectral fingerprint" of settling dynamics:
    - X-axis: Time (probe number)
    - Y-axis: Frequency (oscillation rate)
    - Color: Magnitude (intensity of that frequency at that time)

    Patterns to look for:
    - High-frequency early, low-frequency late = damped oscillation (healthy settling)
    - Persistent high-frequency = unstable oscillation
    - Broadband = chaotic settling
    - Narrowband = dominant resonance mode
    """
    print("\n[5/6] Generating SPECTROGRAM GALLERY...")

    # Group trajectories by provider
    by_provider = defaultdict(list)
    all_trajectories = []

    for r in results:
        provider = r.get('provider', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 8:  # Need enough points for spectrogram
            by_provider[provider].append(drift_ts)
            all_trajectories.append(drift_ts)

    providers = sorted(by_provider.keys())
    n_providers = len(providers)

    # Create figure: 2 rows x 3 cols (5 providers + 1 combined)
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    axes = axes.flatten()

    def compute_averaged_spectrogram(trajectories, nperseg=4):
        """Compute averaged spectrogram across multiple trajectories."""
        if not trajectories:
            return None, None, None

        # Find consistent length (use median)
        lengths = [len(t) for t in trajectories]
        target_len = int(np.median(lengths))
        target_len = max(target_len, 10)  # Minimum 10 points

        all_Sxx = []
        f_out, t_out = None, None

        for drift_ts in trajectories[:100]:  # Limit for performance
            # Normalize length
            if len(drift_ts) < target_len:
                padded = np.zeros(target_len)
                padded[:len(drift_ts)] = drift_ts
                drift_ts = padded
            else:
                drift_ts = drift_ts[:target_len]

            # Compute spectrogram
            try:
                f, t, Sxx = signal.spectrogram(
                    drift_ts, fs=1.0,
                    nperseg=min(nperseg, len(drift_ts)//2),
                    noverlap=min(nperseg-1, len(drift_ts)//2 - 1),
                    mode='magnitude'
                )
                if f_out is None:
                    f_out, t_out = f, t
                if Sxx.shape == (len(f_out), len(t_out)):
                    all_Sxx.append(Sxx)
            except Exception:
                continue

        if not all_Sxx:
            return None, None, None

        # Average spectrograms
        avg_Sxx = np.mean(all_Sxx, axis=0)
        return f_out, t_out, avg_Sxx

    # Plot per-provider spectrograms
    for idx, provider in enumerate(providers[:5]):  # Max 5 providers
        ax = axes[idx]
        trajectories = by_provider[provider]
        color = PROVIDER_COLORS.get(provider, '#888888')

        f, t, Sxx = compute_averaged_spectrogram(trajectories)

        if Sxx is not None:
            im = ax.pcolormesh(t, f, Sxx, shading='gouraud', cmap='viridis')
            plt.colorbar(im, ax=ax, label='Magnitude', shrink=0.8)

            # Stats
            n_traj = len(trajectories)
            avg_len = np.mean([len(tr) for tr in trajectories])

            ax.set_xlabel('Time (probe)', fontsize=10)
            ax.set_ylabel('Frequency', fontsize=10)
            ax.set_title(f'{provider.upper()}\n({n_traj} trajectories, avg {avg_len:.0f} probes)',
                        fontsize=11, fontweight='bold', color=color)
        else:
            ax.text(0.5, 0.5, f'{provider}\nInsufficient data',
                   ha='center', va='center', fontsize=12)
            ax.set_title(f'{provider.upper()}', fontsize=11, fontweight='bold')

    # Plot combined fleet spectrogram in last panel
    ax = axes[5]
    f, t, Sxx = compute_averaged_spectrogram(all_trajectories, nperseg=5)

    if Sxx is not None:
        im = ax.pcolormesh(t, f, Sxx, shading='gouraud', cmap='plasma')
        plt.colorbar(im, ax=ax, label='Magnitude', shrink=0.8)

        ax.set_xlabel('Time (probe)', fontsize=10)
        ax.set_ylabel('Frequency', fontsize=10)
        ax.set_title(f'COMBINED FLEET\n({len(all_trajectories)} total trajectories)',
                    fontsize=11, fontweight='bold', color='darkred')
    else:
        ax.text(0.5, 0.5, 'COMBINED\nInsufficient data',
               ha='center', va='center', fontsize=12)

    plt.suptitle('SPECTROGRAM GALLERY: Time-Frequency Settling Signatures by Provider\n' +
                 '(Brighter = stronger frequency component at that time)',
                 fontsize=14, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'spectrogram_gallery.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path


# ============================================================================
# 6. BONUS: RECOVERY HEATMAP (Multi-dimensional view)
# ============================================================================

def generate_recovery_heatmap(results):
    """
    BONUS: Recovery Heatmap showing ship x time x drift.

    A dense visualization showing how each ship recovers over the probe sequence.
    Color intensity = drift magnitude. Goal: see fleet-wide patterns.

    NOTE: For 023d extended settling data, we skip baseline probes (always 0)
    and show the step_input + recovery phases where the interesting dynamics happen.
    """
    print("\n[BONUS] Generating RECOVERY HEATMAP...")

    fig, ax = plt.subplots(figsize=(16, 12))

    # Build matrix: ships x probes
    # Skip baseline probes for 023d - they're always 0 and not interesting
    by_model = defaultdict(list)
    for r in results:
        model = r.get('model', 'unknown')
        drift_ts = extract_drift_timeseries(r, skip_baseline=True)
        if len(drift_ts) > 0:
            by_model[model].append(drift_ts)

    max_probes = 21  # Show full 20+ probe recovery (after skipping 3 baseline)
    ships = sorted(by_model.keys())

    heatmap = np.zeros((len(ships), max_probes))
    heatmap[:] = np.nan

    for i, ship in enumerate(ships):
        if by_model[ship]:
            # Average across iterations
            all_ts = by_model[ship]
            avg_ts = np.zeros(max_probes)
            count = np.zeros(max_probes)

            for ts in all_ts:
                length = min(len(ts), max_probes)
                avg_ts[:length] += ts[:length]
                count[:length] += 1

            # Keep NaN where no data (model settled early)
            # This shows as gray in the heatmap
            with np.errstate(divide='ignore', invalid='ignore'):
                avg_ts = np.where(count > 0, avg_ts / count, np.nan)
            heatmap[i] = avg_ts

    # Create custom pastel colormap: soft mint → cream → soft coral
    # More professional and easier on the eyes than harsh red-green
    from matplotlib.colors import LinearSegmentedColormap
    pastel_colors = [
        '#98D8AA',  # Soft mint green (stable)
        '#C4E4C1',  # Light sage
        '#F5F5DC',  # Cream/beige (neutral)
        '#FFDAB9',  # Peach puff
        '#E8A0A0',  # Soft coral/rose (unstable)
    ]
    pastel_cmap = LinearSegmentedColormap.from_list('pastel_stability', pastel_colors)
    pastel_cmap.set_bad(color='#B8C5D6')  # Soft steel blue for NaN (early settlers)

    im = ax.imshow(heatmap, aspect='auto', cmap=pastel_cmap,
                   vmin=0, vmax=1.0, interpolation='nearest')

    # Add subtle grid lines for better readability
    ax.set_xticks(np.arange(-0.5, max_probes, 1), minor=True)
    ax.set_yticks(np.arange(-0.5, len(ships), 1), minor=True)
    ax.grid(which='minor', color='white', linestyle='-', linewidth=0.5, alpha=0.7)

    # Event Horizon threshold indicator (via colorbar)
    cbar = plt.colorbar(im, ax=ax, shrink=0.8, pad=0.02)
    cbar.set_label('Drift (cosine)', fontsize=10)
    # Draw EH line on colorbar
    cbar.ax.axhline(y=EVENT_HORIZON, color='#333333', linewidth=2, linestyle='--')

    # Labels
    ax.set_xlabel('Recovery Phase (Probe after step input)', fontsize=12)
    ax.set_ylabel('Ship', fontsize=12)
    ax.set_title('FLEET RECOVERY HEATMAP: Step Input → Recovery Dynamics',
                 fontsize=13, fontweight='bold', pad=10)

    # Add legend explaining the colors (more visible than in title)
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='#98D8AA', edgecolor='#666', label='Stable (low drift)'),
        Patch(facecolor='#E8A0A0', edgecolor='#666', label='Unstable (high drift)'),
        Patch(facecolor='#B8C5D6', edgecolor='#666', label='Settled Early')
    ]
    ax.legend(handles=legend_elements, loc='upper right', fontsize=9,
              framealpha=0.95, title='Legend', fancybox=True, shadow=True)

    # Y-axis labels
    short_names = [s[:15] + '..' if len(s) > 17 else s for s in ships]
    ax.set_yticks(range(len(ships)))
    ax.set_yticklabels(short_names, fontsize=7)

    # Probe number labels - label probe 1 as "Step" and rest as recovery numbers
    x_labels = ['Step'] + [str(i) for i in range(1, max_probes)]
    ax.set_xticks(range(max_probes))
    ax.set_xticklabels(x_labels, fontsize=8)

    plt.tight_layout()

    output_path = OUTPUT_DIR / 'rescue_recovery_heatmap.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path


# ============================================================================
# 7. PER-PROVIDER HEATMAP GALLERY
# ============================================================================

def generate_provider_heatmaps(results):
    """
    PROVIDER HEATMAPS: One heatmap per provider showing their ships' recovery dynamics.

    Same visualization as the fleet heatmap, but broken down by provider family
    for better visibility of per-provider patterns.
    """
    print("\n[7/7] Generating PER-PROVIDER HEATMAPS...")

    # Group results by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        by_provider[provider].append(r)

    providers = sorted(by_provider.keys())
    n_providers = len(providers)

    # Create a grid: 2 rows x 3 cols (fits up to 6 providers)
    n_cols = 3
    n_rows = (n_providers + n_cols - 1) // n_cols

    fig, axes = plt.subplots(n_rows, n_cols, figsize=(18, 5 * n_rows))
    axes = axes.flatten() if n_providers > 1 else [axes]

    max_probes = 21  # Show full 20+ probe recovery

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        provider_results = by_provider[provider]

        # Build matrix: ships x probes for this provider
        by_model = defaultdict(list)
        for r in provider_results:
            model = r.get('model', 'unknown')
            drift_ts = extract_drift_timeseries(r, skip_baseline=True)
            if len(drift_ts) > 0:
                by_model[model].append(drift_ts)

        ships = sorted(by_model.keys())

        if not ships:
            ax.text(0.5, 0.5, 'No data', ha='center', va='center', fontsize=12)
            ax.set_title(f'{provider}', fontsize=11, fontweight='bold')
            continue

        heatmap = np.zeros((len(ships), max_probes))
        heatmap[:] = np.nan

        for i, ship in enumerate(ships):
            if by_model[ship]:
                all_ts = by_model[ship]
                avg_ts = np.zeros(max_probes)
                count = np.zeros(max_probes)

                for ts in all_ts:
                    length = min(len(ts), max_probes)
                    avg_ts[:length] += ts[:length]
                    count[:length] += 1

                with np.errstate(divide='ignore', invalid='ignore'):
                    avg_ts = np.where(count > 0, avg_ts / count, np.nan)
                heatmap[i] = avg_ts

        # Create same pastel colormap for consistency
        from matplotlib.colors import LinearSegmentedColormap
        pastel_colors = [
            '#98D8AA',  # Soft mint green (stable)
            '#C4E4C1',  # Light sage
            '#F5F5DC',  # Cream/beige (neutral)
            '#FFDAB9',  # Peach puff
            '#E8A0A0',  # Soft coral/rose (unstable)
        ]
        pastel_cmap = LinearSegmentedColormap.from_list('pastel_stability', pastel_colors)
        pastel_cmap.set_bad(color='#B8C5D6')  # Soft steel blue for NaN

        im = ax.imshow(heatmap, aspect='auto', cmap=pastel_cmap,
                       vmin=0, vmax=1.0, interpolation='nearest')

        # Add subtle grid lines
        ax.set_xticks(np.arange(-0.5, max_probes, 1), minor=True)
        ax.set_yticks(np.arange(-0.5, len(ships), 1), minor=True)
        ax.grid(which='minor', color='white', linestyle='-', linewidth=0.5, alpha=0.7)

        # Event Horizon line on colorbar
        cbar = plt.colorbar(im, ax=ax, shrink=0.8, pad=0.02)
        cbar.set_label('Drift', fontsize=9)
        cbar.ax.axhline(y=EVENT_HORIZON, color='#333333', linewidth=2, linestyle='--')

        # Labels
        ax.set_xlabel('Recovery Phase', fontsize=10)
        ax.set_ylabel('Ship', fontsize=10)

        # Provider-specific color for title
        provider_color = PROVIDER_COLORS.get(provider, '#333333')
        ax.set_title(f'{provider.upper()} ({len(ships)} ships)',
                     fontsize=11, fontweight='bold', color=provider_color)

        # Y-axis: ship names (shorter for readability)
        # Extract just the model name without provider prefix
        short_names = []
        for s in ships:
            # Try to extract just the key part of the model name
            parts = s.split('/')
            name = parts[-1] if len(parts) > 1 else s
            # Truncate if still too long
            name = name[:18] + '..' if len(name) > 20 else name
            short_names.append(name)

        ax.set_yticks(range(len(ships)))
        ax.set_yticklabels(short_names, fontsize=8)

        # X-axis: probe numbers
        x_labels = ['S'] + [str(i) if i % 5 == 0 else '' for i in range(1, max_probes)]
        ax.set_xticks(range(max_probes))
        ax.set_xticklabels(x_labels, fontsize=7)

    # Hide unused axes
    for idx in range(n_providers, len(axes)):
        axes[idx].axis('off')

    plt.suptitle('PROVIDER FAMILY HEATMAPS: Recovery Dynamics by Provider\n' +
                 '(Green=stable, Red=unstable, Blue=settled early | S=Step input)',
                 fontsize=13, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'provider_heatmap_gallery.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 70)
    print("R&D VISUALIZATION EXPERIMENTS: 5_Settling")
    print("=" * 70)
    print(f"\nData source: {DATA_FILE}")
    print(f"Output dir:  {OUTPUT_DIR}")
    print(f"Event Horizon: {EVENT_HORIZON}")
    print()

    # Load data
    results = load_settling_data()

    if not results:
        print("ERROR: No settling data found!")
        return

    # Generate all visualizations
    outputs = []

    try:
        outputs.append(generate_waterfall_plot(results))
    except Exception as e:
        print(f"   ERROR in waterfall: {e}")

    try:
        provider_waterfalls = generate_provider_waterfall_plots(results)
        outputs.extend(provider_waterfalls)
    except Exception as e:
        print(f"   ERROR in provider waterfalls: {e}")

    try:
        outputs.append(generate_combined_provider_waterfalls(results))
    except Exception as e:
        print(f"   ERROR in combined provider waterfalls: {e}")

    try:
        outputs.append(generate_phase_plane_plot(results))
    except Exception as e:
        print(f"   ERROR in phase-plane: {e}")

    try:
        outputs.append(generate_fft_settling_plot(results))
    except Exception as e:
        print(f"   ERROR in FFT: {e}")

    try:
        outputs.append(generate_consistency_envelope(results))
    except Exception as e:
        print(f"   ERROR in consistency envelope: {e}")

    try:
        outputs.append(generate_consistency_envelope_together(results))
    except Exception as e:
        print(f"   ERROR in consistency envelope (together): {e}")

    try:
        outputs.append(generate_spectrogram_gallery(results))
    except Exception as e:
        print(f"   ERROR in spectrogram gallery: {e}")

    try:
        outputs.append(generate_recovery_heatmap(results))
    except Exception as e:
        print(f"   ERROR in heatmap: {e}")

    try:
        outputs.append(generate_provider_heatmaps(results))
    except Exception as e:
        print(f"   ERROR in provider heatmaps: {e}")

    print("\n" + "=" * 70)
    print("R&D VISUALIZATION COMPLETE")
    print("=" * 70)
    print(f"\nGenerated {len(outputs)} visualizations:")
    for o in outputs:
        if o is not None:
            name = o.name if hasattr(o, 'name') else str(o)
            print(f"  - {name}")
    print("\nReview these and let me know which to include in the final package!")

if __name__ == "__main__":
    main()
