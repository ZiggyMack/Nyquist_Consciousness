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

def extract_drift_timeseries(result):
    """Extract drift values from probe sequence as time series."""
    probe_seq = result.get('probe_sequence', [])
    drift_values = []
    for p in probe_seq:
        drift = p.get('drift', p.get('peak_drift', 0))
        if drift is not None:
            drift_values.append(float(drift))
    return np.array(drift_values)

# ============================================================================
# 1. WATERFALL PLOT - 3D Time-Frequency-Amplitude
# ============================================================================

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

    # Group by model
    by_model = defaultdict(list)
    for r in results:
        model = r.get('model', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) > 0:
            by_model[model].append(drift_ts)

    # Create waterfall data matrix
    max_probes = 20  # Maximum expected probe length
    ships = sorted(by_model.keys())[:25]  # Limit to 25 ships for clarity

    waterfall_matrix = np.zeros((len(ships), max_probes))
    waterfall_matrix[:] = np.nan  # Use NaN for missing data

    for i, ship in enumerate(ships):
        if by_model[ship]:
            # Average across iterations for this ship
            all_ts = by_model[ship]
            # Pad/truncate to max_probes
            for ts in all_ts:
                length = min(len(ts), max_probes)
                waterfall_matrix[i, :length] = ts[:length]
                break  # Just use first iteration for clarity

    # Create figure
    fig = plt.figure(figsize=(14, 10))

    # 2D heatmap view (waterfall seen from above)
    ax1 = fig.add_subplot(211)
    im = ax1.imshow(waterfall_matrix, aspect='auto', cmap='RdYlBu_r',
                    vmin=0, vmax=1.5, interpolation='nearest')
    ax1.axvline(x=3, color='white', linestyle='--', alpha=0.7, label='Step input')
    ax1.axhline(y=len(ships)//2, color='white', linestyle=':', alpha=0.5)

    # Event Horizon line
    ax1.text(max_probes - 1, 0.5, f'EH={EVENT_HORIZON}', color='red',
             fontsize=8, ha='right', va='bottom')

    ax1.set_xlabel('Probe Number (Time)', fontsize=11)
    ax1.set_ylabel('Ship (stacked)', fontsize=11)
    ax1.set_title('WATERFALL VIEW: Fleet Settling Dynamics\n' +
                  '(Each row = one ship | Current: 6 probes | Run 023d: 20 probes)', fontsize=11)

    # Colorbar
    cbar = plt.colorbar(im, ax=ax1, shrink=0.8)
    cbar.set_label('Drift (cosine distance)', fontsize=10)

    # Y-axis labels (ship names, rotated)
    short_names = [s[:12] + '..' if len(s) > 14 else s for s in ships]
    ax1.set_yticks(range(len(ships)))
    ax1.set_yticklabels(short_names, fontsize=7)

    # 3D surface view
    ax2 = fig.add_subplot(212, projection='3d')

    X = np.arange(max_probes)
    Y = np.arange(len(ships))
    X, Y = np.meshgrid(X, Y)

    # Replace NaN with 0 for surface plot
    Z = np.nan_to_num(waterfall_matrix, nan=0)

    surf = ax2.plot_surface(X, Y, Z, cmap='RdYlBu_r',
                            linewidth=0.1, antialiased=True, alpha=0.8)

    # Event Horizon plane
    eh_plane = np.ones_like(Z) * EVENT_HORIZON
    ax2.plot_surface(X, Y, eh_plane, alpha=0.2, color='red')

    ax2.set_xlabel('Probe Number', fontsize=10)
    ax2.set_ylabel('Ship Index', fontsize=10)
    ax2.set_zlabel('Drift', fontsize=10)
    ax2.set_title('3D WATERFALL: Settling Surface Topology', fontsize=11)
    ax2.view_init(elev=25, azim=-60)

    plt.tight_layout()
    output_path = OUTPUT_DIR / 'waterfall_settling_fleet.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
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
                 '(Limited to 6 probes - insufficient for spectrogram | Run 023d: 20 probes)',
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
    """
    print("\n[4/4] Generating CONSISTENCY ENVELOPE...")

    fig, axes = plt.subplots(2, 3, figsize=(16, 10))
    axes = axes.flatten()

    # Group by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 3:
            by_provider[provider].append(drift_ts)

    providers = list(by_provider.keys())[:6]

    for idx, provider in enumerate(providers):
        ax = axes[idx]
        color = PROVIDER_COLORS.get(provider, '#888888')

        trajectories = by_provider[provider]

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
        ax.set_title(f'{provider.upper()}\n' +
                    f'Envelope Width: {envelope_width:.2f} | Jitter: {jitter:.2f}',
                    fontsize=11, fontweight='bold')
        ax.set_ylim(-0.1, 1.5)
        ax.set_xlim(0, max_len-1)
        ax.grid(True, alpha=0.3)

        if idx == 0:
            ax.legend(loc='upper right', fontsize=8)

    # Hide unused axes
    for idx in range(len(providers), 6):
        axes[idx].set_visible(False)

    plt.suptitle('CONSISTENCY ENVELOPE: Trajectory Bundle Analysis\n' +
                 '(Tighter envelope = more consistent | Limited to 6 probes - Run 023d: 20 probes)',
                 fontsize=12, fontweight='bold', y=1.02)
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'consistency_envelope.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    plt.close()
    print(f"   Saved: {output_path}")

    return output_path

# ============================================================================
# 5. BONUS: RECOVERY HEATMAP (Multi-dimensional view)
# ============================================================================

def generate_recovery_heatmap(results):
    """
    BONUS: Recovery Heatmap showing ship x time x drift.

    A dense visualization showing how each ship recovers over the probe sequence.
    Color intensity = drift magnitude. Goal: see fleet-wide patterns.
    """
    print("\n[BONUS] Generating RECOVERY HEATMAP...")

    fig, ax = plt.subplots(figsize=(14, 10))

    # Build matrix: ships x probes
    by_model = defaultdict(list)
    for r in results:
        model = r.get('model', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) > 0:
            by_model[model].append(drift_ts)

    max_probes = 15
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

            count[count == 0] = 1  # Avoid division by zero
            avg_ts /= count
            heatmap[i] = avg_ts

    # Plot heatmap
    im = ax.imshow(heatmap, aspect='auto', cmap='RdYlGn_r',
                   vmin=0, vmax=1.0, interpolation='nearest')

    # Event Horizon threshold indicator (via colorbar)
    cbar = plt.colorbar(im, ax=ax, shrink=0.8)
    cbar.set_label('Drift (cosine distance)', fontsize=11)
    cbar.ax.axhline(y=EVENT_HORIZON, color='black', linewidth=2)
    cbar.ax.text(1.1, EVENT_HORIZON, f'EH={EVENT_HORIZON}',
                 fontsize=9, va='center', transform=cbar.ax.transAxes)

    # Labels
    ax.set_xlabel('Probe Number (Time)', fontsize=12)
    ax.set_ylabel('Ship', fontsize=12)
    ax.set_title('FLEET RECOVERY HEATMAP\n' +
                 '(Green = stable, Red = unstable | Limited to 6 probes - Run 023d: 20 probes)',
                 fontsize=12, fontweight='bold')

    # Y-axis labels
    short_names = [s[:15] + '..' if len(s) > 17 else s for s in ships]
    ax.set_yticks(range(len(ships)))
    ax.set_yticklabels(short_names, fontsize=7)

    # Probe number labels
    ax.set_xticks(range(max_probes))
    ax.set_xticklabels(range(1, max_probes + 1), fontsize=9)

    plt.tight_layout()

    output_path = OUTPUT_DIR / 'rescue_recovery_heatmap.png'
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
        outputs.append(generate_recovery_heatmap(results))
    except Exception as e:
        print(f"   ERROR in heatmap: {e}")

    print("\n" + "=" * 70)
    print("R&D VISUALIZATION COMPLETE")
    print("=" * 70)
    print(f"\nGenerated {len(outputs)} visualizations:")
    for o in outputs:
        print(f"  - {o.name}")
    print("\nReview these and let me know which to include in the final package!")

if __name__ == "__main__":
    main()
