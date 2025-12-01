"""
Run 008 Decibel-Scale Visualizations

Converts identity drift measurements to decibel scale (dB) for enhanced
dynamic range visualization — similar to audio spectrum analyzers.

dB conversion: dB = 20 * log10(value / reference)

This reveals:
- Small variations that are invisible on linear scale
- True dynamic range of identity fluctuations
- Patterns that emerge at different "loudness" levels

Also includes:
- Phase portrait / vector field (the "drain spiral")
- FFT spectral decomposition of turn-by-turn drift
"""

import json
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
from pathlib import Path
from collections import defaultdict
from scipy import signal
from scipy.fft import fft, fftfreq

# Paths
BASE_DIR = Path(__file__).resolve().parent.parent
RESULTS_FILE = BASE_DIR / "armada_results" / "S7_run_008_20251201_020501.json"
OUTPUT_DIR = Path(__file__).resolve().parent / "pics" / "dB"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# Provider colors — 3 platforms (o-series is part of OpenAI/GPT)
PROVIDER_COLORS = {
    "claude": "#7c3aed",    # Purple - Anthropic
    "gpt": "#10a37f",       # Green - OpenAI (includes o-series)
    "gemini": "#4285f4",    # Blue - Google
}

def get_provider(ship_name):
    """Determine provider from ship name. O-series models are OpenAI/GPT."""
    name = ship_name.lower()
    if "claude" in name:
        return "claude"
    elif "gemini" in name:
        return "gemini"
    # o-series (o1, o3, o4-mini) are OpenAI models, not a separate platform
    elif name.startswith("o1") or name.startswith("o3") or name.startswith("o4"):
        return "gpt"  # o-series IS GPT/OpenAI
    elif "gpt" in name:
        return "gpt"
    return "unknown"

def to_dB(value, reference=1.0, floor=-60):
    """
    Convert linear value to decibels.

    Args:
        value: Linear value to convert
        reference: Reference value (0 dB point)
        floor: Minimum dB value (prevents -inf)

    Returns:
        Value in decibels
    """
    if value <= 0:
        return floor
    db = 20 * np.log10(value / reference)
    return max(db, floor)

def to_dB_array(arr, reference=None, floor=-60):
    """Convert array to dB scale."""
    arr = np.array(arr)
    if reference is None:
        reference = np.mean(arr[arr > 0]) if np.any(arr > 0) else 1.0

    result = np.zeros_like(arr, dtype=float)
    for i, v in enumerate(arr):
        result[i] = to_dB(v, reference, floor)
    return result

def load_run008_data():
    """Load and parse Run 008 results."""
    with open(RESULTS_FILE, encoding='utf-8') as f:
        return json.load(f)

def extract_sequences_by_ship(data):
    """Extract turn-by-turn sequences for each ship."""
    ship_sequences = defaultdict(lambda: defaultdict(list))

    for ship_name, ship_data in data['results'].items():
        provider = get_provider(ship_name)

        for seq_name, seq_turns in ship_data.get('sequences', {}).items():
            if not isinstance(seq_turns, list):
                continue

            for turn in seq_turns:
                if 'drift_data' not in turn:
                    continue

                dims = turn['drift_data'].get('dimensions', {})
                drift = turn['drift_data'].get('drift', 0)
                turn_num = turn.get('turn', 0)

                ship_sequences[ship_name][seq_name].append({
                    'turn': turn_num,
                    'drift': drift,
                    'A': dims.get('pole_density', 0),
                    'B': dims.get('zero_density', 0),
                    'C': dims.get('meta_density', 0),
                    'D': dims.get('identity_coherence', 0),
                    'E': dims.get('hedging_ratio', 0),
                    'provider': provider,
                })

    return ship_sequences

def extract_all_points(data):
    """Extract all 5D data points."""
    points = []
    for ship_name, ship_data in data['results'].items():
        provider = get_provider(ship_name)
        for seq_name, seq_turns in ship_data.get('sequences', {}).items():
            if not isinstance(seq_turns, list):
                continue
            for turn in seq_turns:
                if 'drift_data' not in turn:
                    continue
                dims = turn['drift_data'].get('dimensions', {})
                if not dims:
                    continue
                points.append({
                    'ship': ship_name,
                    'provider': provider,
                    'A': dims.get('pole_density', 0),
                    'B': dims.get('zero_density', 0),
                    'C': dims.get('meta_density', 0),
                    'D': dims.get('identity_coherence', 0),
                    'E': dims.get('hedging_ratio', 0),
                    'drift': turn['drift_data'].get('drift', 0),
                })
    return points

# =============================================================================
# VISUALIZATION 1: dB-Scale Heatmap
# =============================================================================
def plot_db_heatmap(data):
    """Create heatmap with dB scaling for enhanced dynamic range."""
    ship_sequences = extract_sequences_by_ship(data)

    # Get all ships sorted by average drift
    ship_avg_drift = {}
    for ship, seqs in ship_sequences.items():
        all_drifts = []
        for seq_turns in seqs.values():
            all_drifts.extend([t['drift'] for t in seq_turns])
        if all_drifts:
            ship_avg_drift[ship] = np.mean(all_drifts)

    sorted_ships = sorted(ship_avg_drift.keys(), key=lambda x: ship_avg_drift[x])

    # Build dimension averages
    dims = ['A', 'B', 'C', 'D', 'E']
    matrix_linear = []

    for ship in sorted_ships:
        dim_avgs = []
        for dim in dims:
            all_vals = []
            for seq_turns in ship_sequences[ship].values():
                all_vals.extend([t[dim] for t in seq_turns])
            dim_avgs.append(np.mean(all_vals) if all_vals else 0)
        matrix_linear.append(dim_avgs)

    matrix_linear = np.array(matrix_linear)

    # Convert to dB
    matrix_dB = np.zeros_like(matrix_linear)
    for col in range(matrix_linear.shape[1]):
        col_data = matrix_linear[:, col]
        ref = np.mean(col_data[col_data > 0]) if np.any(col_data > 0) else 1.0
        for row in range(matrix_linear.shape[0]):
            matrix_dB[row, col] = to_dB(matrix_linear[row, col], ref, floor=-40)

    # Create side-by-side comparison
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 12))

    # Linear scale (original)
    matrix_norm = (matrix_linear - matrix_linear.min(axis=0)) / (matrix_linear.max(axis=0) - matrix_linear.min(axis=0) + 0.001)
    im1 = ax1.imshow(matrix_norm, cmap='RdYlGn_r', aspect='auto')
    ax1.set_title('LINEAR SCALE\n(Normalized 0-1)', fontsize=12, fontweight='bold')
    ax1.set_xticks(range(len(dims)))
    ax1.set_xticklabels(['Pole', 'Zero', 'Meta', 'Identity', 'Hedging'])
    ax1.set_yticks(range(len(sorted_ships)))
    ax1.set_yticklabels(sorted_ships, fontsize=7)
    plt.colorbar(im1, ax=ax1, label='Normalized (0=min, 1=max)')

    # dB scale
    im2 = ax2.imshow(matrix_dB, cmap='magma', aspect='auto', vmin=-40, vmax=10)
    ax2.set_title('DECIBEL SCALE (dB)\n(20·log₁₀ relative to mean)', fontsize=12, fontweight='bold')
    ax2.set_xticks(range(len(dims)))
    ax2.set_xticklabels(['Pole', 'Zero', 'Meta', 'Identity', 'Hedging'])
    ax2.set_yticks(range(len(sorted_ships)))
    ax2.set_yticklabels(sorted_ships, fontsize=7)
    cbar2 = plt.colorbar(im2, ax=ax2, label='dB (0 = mean, +10 = 3x, -20 = 0.1x)')

    fig.suptitle('RUN 008: 5D Dimension Heatmap — Linear vs dB Scale\nShips sorted by stability (top=most stable)',
                fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_heatmap_dB_comparison.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_heatmap_dB_comparison.png")
    plt.close()

# =============================================================================
# VISUALIZATION 2: Phase Portrait / Vector Field ("The Drain")
# =============================================================================
def plot_phase_portrait(data):
    """
    Create phase portrait showing the DIRECTION of identity drift.
    This is the "water going down the drain" visualization.

    Shows velocity vectors in identity space — where is each point MOVING TO?
    """
    ship_sequences = extract_sequences_by_ship(data)

    fig, axes = plt.subplots(2, 2, figsize=(16, 14))

    # Collect all transitions (point → next point)
    transitions = []

    for ship, seqs in ship_sequences.items():
        provider = get_provider(ship)
        for seq_name, turns in seqs.items():
            sorted_turns = sorted(turns, key=lambda x: x['turn'])
            for i in range(len(sorted_turns) - 1):
                t1, t2 = sorted_turns[i], sorted_turns[i+1]
                transitions.append({
                    'x1': t1['A'], 'y1': t1['B'],
                    'x2': t2['A'], 'y2': t2['B'],
                    'z1': t1['C'], 'z2': t2['C'],
                    'd1': t1['drift'], 'd2': t2['drift'],
                    'provider': provider,
                    'ship': ship,
                })

    # Plot 1: Pole-Zero flow field
    ax = axes[0, 0]
    for trans in transitions:
        dx = trans['x2'] - trans['x1']
        dy = trans['y2'] - trans['y1']
        color = PROVIDER_COLORS.get(trans['provider'], 'gray')
        ax.arrow(trans['x1'], trans['y1'], dx*0.8, dy*0.8,
                head_width=0.02, head_length=0.01, fc=color, ec=color, alpha=0.3)

    ax.set_xlabel('Pole Density (A)')
    ax.set_ylabel('Zero Density (B)')
    ax.set_title('PHASE PORTRAIT: Pole-Zero Flow\n(Where identity MOVES each turn)', fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 2: Drift trajectory (scatter with arrows)
    ax = axes[0, 1]
    for trans in transitions:
        color = PROVIDER_COLORS.get(trans['provider'], 'gray')
        # Draw from (d1) → (d2) in a time series
        ax.scatter([trans['d1']], [trans['d2']], c=color, alpha=0.4, s=20)

    # Identity line (no change)
    ax.plot([0, 4], [0, 4], 'k--', alpha=0.5, label='No change')
    ax.set_xlabel('Drift at Turn N')
    ax.set_ylabel('Drift at Turn N+1')
    ax.set_title('DRIFT ATTRACTOR MAP\n(Below line = recovering, Above = drifting more)', fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 3: Spiral visualization (polar coordinates)
    ax = axes[1, 0]
    for trans in transitions:
        # Convert to polar-like coordinates
        r1 = np.sqrt(trans['x1']**2 + trans['y1']**2)
        r2 = np.sqrt(trans['x2']**2 + trans['y2']**2)
        theta1 = np.arctan2(trans['y1'], trans['x1'])
        theta2 = np.arctan2(trans['y2'], trans['x2'])

        color = PROVIDER_COLORS.get(trans['provider'], 'gray')
        ax.plot([theta1, theta2], [r1, r2], c=color, alpha=0.3, linewidth=0.5)

    ax.set_xlabel('Angle (Pole-Zero ratio)')
    ax.set_ylabel('Radius (Identity magnitude)')
    ax.set_title('SPIRAL DYNAMICS\n(Drain pattern in polar coordinates)', fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 4: Vector magnitude histogram (dB scale)
    ax = axes[1, 1]
    magnitudes = []
    for trans in transitions:
        dx = trans['x2'] - trans['x1']
        dy = trans['y2'] - trans['y1']
        mag = np.sqrt(dx**2 + dy**2)
        magnitudes.append(mag)

    # Convert to dB
    magnitudes = np.array(magnitudes)
    magnitudes_dB = to_dB_array(magnitudes + 0.001, reference=np.median(magnitudes))

    ax.hist(magnitudes_dB, bins=50, color='#2a9d8f', edgecolor='white', alpha=0.8)
    ax.axvline(x=0, color='red', linestyle='--', label='Median (0 dB)')
    ax.set_xlabel('Movement Magnitude (dB)')
    ax.set_ylabel('Count')
    ax.set_title('VELOCITY DISTRIBUTION (dB)\n(How fast identity changes per turn)', fontweight='bold')
    ax.legend()

    fig.suptitle('RUN 008: PHASE PORTRAITS — The Identity Attractor Basin\n"Water Going Down the Drain"',
                fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_phase_portrait.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_phase_portrait.png")
    plt.close()

# =============================================================================
# VISUALIZATION 3: FFT Spectral Analyzer
# =============================================================================
def plot_spectral_analysis(data):
    """
    FFT spectral decomposition of turn-by-turn drift.
    Like a spectrum analyzer showing frequency content of identity fluctuations.

    Low frequency = slow drift (gradual erosion)
    High frequency = rapid oscillation (instability)
    """
    ship_sequences = extract_sequences_by_ship(data)

    fig, axes = plt.subplots(2, 3, figsize=(18, 12))

    # Collect drift sequences by provider
    provider_sequences = defaultdict(list)

    for ship, seqs in ship_sequences.items():
        provider = get_provider(ship)
        for seq_name, turns in seqs.items():
            sorted_turns = sorted(turns, key=lambda x: x['turn'])
            drift_seq = [t['drift'] for t in sorted_turns]
            if len(drift_seq) >= 4:  # Need enough points for FFT
                provider_sequences[provider].append({
                    'ship': ship,
                    'sequence': seq_name,
                    'drifts': drift_seq
                })

    # Plot 1-4: Provider-specific spectra
    for idx, provider in enumerate(['claude', 'gpt', 'gemini']):
        ax = axes.flat[idx]
        seqs = provider_sequences.get(provider, [])

        if not seqs:
            ax.text(0.5, 0.5, f"No data for {provider}", ha='center', va='center')
            continue

        # Average spectrum across all sequences
        all_magnitudes = []

        for seq_data in seqs:
            drifts = np.array(seq_data['drifts'])
            n = len(drifts)

            # Compute FFT
            yf = fft(drifts - np.mean(drifts))  # Remove DC component
            xf = fftfreq(n, d=1)[:n//2]  # Frequency bins (1 sample = 1 turn)
            magnitudes = 2.0/n * np.abs(yf[0:n//2])

            # Convert to dB
            magnitudes_dB = to_dB_array(magnitudes + 0.0001, reference=1.0)

            if len(magnitudes_dB) > 0:
                all_magnitudes.append(magnitudes_dB)

        if all_magnitudes:
            # Pad to same length and average
            max_len = max(len(m) for m in all_magnitudes)
            padded = []
            for m in all_magnitudes:
                if len(m) < max_len:
                    m = np.pad(m, (0, max_len - len(m)), constant_values=-60)
                padded.append(m)

            avg_spectrum = np.mean(padded, axis=0)
            freqs = np.linspace(0, 0.5, len(avg_spectrum))  # 0 to Nyquist

            ax.bar(freqs, avg_spectrum, width=0.02, color=PROVIDER_COLORS[provider], alpha=0.8)
            ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
            ax.set_ylim(-50, 20)

        ax.set_xlabel('Frequency (cycles/turn)')
        ax.set_ylabel('Magnitude (dB)')
        ax.set_title(f'{provider.upper()}\n({len(seqs)} sequences)', fontweight='bold')
        ax.grid(True, alpha=0.3)

    # Plot 5: Combined overlay
    ax = axes[1, 0]
    for provider in ['claude', 'gpt', 'gemini']:
        seqs = provider_sequences.get(provider, [])
        if not seqs:
            continue

        all_magnitudes = []
        for seq_data in seqs:
            drifts = np.array(seq_data['drifts'])
            n = len(drifts)
            yf = fft(drifts - np.mean(drifts))
            magnitudes = 2.0/n * np.abs(yf[0:n//2])
            magnitudes_dB = to_dB_array(magnitudes + 0.0001)
            if len(magnitudes_dB) > 0:
                all_magnitudes.append(magnitudes_dB)

        if all_magnitudes:
            max_len = max(len(m) for m in all_magnitudes)
            padded = [np.pad(m, (0, max_len - len(m)), constant_values=-60) for m in all_magnitudes]
            avg_spectrum = np.mean(padded, axis=0)
            freqs = np.linspace(0, 0.5, len(avg_spectrum))
            ax.plot(freqs, avg_spectrum, color=PROVIDER_COLORS[provider], linewidth=2, label=provider.title())

    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)
    ax.set_xlabel('Frequency (cycles/turn)')
    ax.set_ylabel('Magnitude (dB)')
    ax.set_title('COMBINED SPECTRUM OVERLAY', fontweight='bold')
    ax.legend()
    ax.grid(True, alpha=0.3)
    ax.set_ylim(-50, 20)

    # Plot 6: Interpretation guide
    ax = axes[1, 2]
    ax.text(0.5, 0.9, 'FREQUENCY INTERPRETATION', ha='center', fontsize=14, fontweight='bold', transform=ax.transAxes)
    ax.text(0.1, 0.75, '• Low freq (0.0-0.1): Slow drift (gradual erosion)', fontsize=11, transform=ax.transAxes)
    ax.text(0.1, 0.60, '• Mid freq (0.1-0.3): Turn-to-turn fluctuation', fontsize=11, transform=ax.transAxes)
    ax.text(0.1, 0.45, '• High freq (0.3-0.5): Rapid oscillation (unstable)', fontsize=11, transform=ax.transAxes)
    ax.text(0.1, 0.25, '• 0 dB = reference level', fontsize=10, transform=ax.transAxes)
    ax.text(0.1, 0.15, '• +20 dB = 10x stronger', fontsize=10, transform=ax.transAxes)
    ax.text(0.1, 0.05, '• -20 dB = 10x weaker', fontsize=10, transform=ax.transAxes)
    ax.axis('off')

    fig.suptitle('RUN 008: FFT SPECTRAL ANALYSIS — Identity Frequency Content\n(Spectrum Analyzer View)',
                fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_spectral_analysis.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_spectral_analysis.png")
    plt.close()

# =============================================================================
# VISUALIZATION 4: dB-Scale Drift Box Plot
# =============================================================================
def plot_drift_dB(data):
    """Box plot of drift in dB scale for enhanced dynamic range."""
    points = extract_all_points(data)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 8))

    provider_drifts = defaultdict(list)
    for p in points:
        provider_drifts[p['provider']].append(p['drift'])

    providers = ['claude', 'gpt', 'gemini']

    # Linear scale
    data_linear = [provider_drifts.get(p, []) for p in providers]
    bp1 = ax1.boxplot(data_linear, labels=[p.title() for p in providers], patch_artist=True)
    for patch, p in zip(bp1['boxes'], providers):
        patch.set_facecolor(PROVIDER_COLORS[p])
        patch.set_alpha(0.7)
    ax1.set_ylabel('Drift (linear)')
    ax1.set_title('LINEAR SCALE', fontweight='bold')
    ax1.grid(True, alpha=0.3)

    # dB scale
    all_drifts = [d for drifts in provider_drifts.values() for d in drifts]
    ref = np.median([d for d in all_drifts if d > 0])

    data_dB = []
    for p in providers:
        drifts = provider_drifts.get(p, [])
        drifts_dB = [to_dB(d + 0.001, ref) for d in drifts]
        data_dB.append(drifts_dB)

    bp2 = ax2.boxplot(data_dB, labels=[p.title() for p in providers], patch_artist=True)
    for patch, p in zip(bp2['boxes'], providers):
        patch.set_facecolor(PROVIDER_COLORS[p])
        patch.set_alpha(0.7)
    ax2.axhline(y=0, color='red', linestyle='--', alpha=0.5, label='Median (0 dB)')
    ax2.set_ylabel('Drift (dB)')
    ax2.set_title('DECIBEL SCALE (dB)\n(0 dB = median drift)', fontweight='bold')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    fig.suptitle('RUN 008: Drift Distribution by Provider — Linear vs dB',
                fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_drift_dB_comparison.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_drift_dB_comparison.png")
    plt.close()

# =============================================================================
# VISUALIZATION 5: 3-6-9 Harmonic Analysis
# =============================================================================
def plot_369_harmonics(data):
    """
    Analyze drift patterns for 3-6-9 harmonic relationships.
    Looking for resonance at turns 3, 6, 9, 12, etc.
    """
    ship_sequences = extract_sequences_by_ship(data)

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # Collect all drift values by turn number
    turn_drifts = defaultdict(list)

    for ship, seqs in ship_sequences.items():
        for seq_name, turns in seqs.items():
            for t in turns:
                turn_drifts[t['turn']].append(t['drift'])

    turns = sorted(turn_drifts.keys())
    avg_by_turn = [np.mean(turn_drifts[t]) for t in turns]
    std_by_turn = [np.std(turn_drifts[t]) for t in turns]

    # Plot 1: Average drift by turn
    ax = axes[0, 0]
    ax.bar(turns, avg_by_turn, color='#2a9d8f', alpha=0.7, edgecolor='white')
    ax.errorbar(turns, avg_by_turn, yerr=std_by_turn, fmt='none', color='black', capsize=3)

    # Highlight 3-6-9 positions
    for t in turns:
        if t % 3 == 0 and t > 0:
            ax.axvline(x=t, color='red', linestyle='--', alpha=0.5)

    ax.set_xlabel('Turn Number')
    ax.set_ylabel('Average Drift')
    ax.set_title('DRIFT BY TURN\n(Red lines = 3-6-9 positions)', fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 2: Mod-3 grouping
    ax = axes[0, 1]
    mod3_groups = {0: [], 1: [], 2: []}
    for turn, drifts in turn_drifts.items():
        if turn > 0:
            mod3_groups[turn % 3].extend(drifts)

    labels = ['Turns 3,6,9,12...', 'Turns 1,4,7,10...', 'Turns 2,5,8,11...']
    data = [mod3_groups[0], mod3_groups[1], mod3_groups[2]]
    bp = ax.boxplot(data, labels=labels, patch_artist=True)
    colors = ['#e76f51', '#2a9d8f', '#264653']
    for patch, c in zip(bp['boxes'], colors):
        patch.set_facecolor(c)
        patch.set_alpha(0.7)

    ax.set_ylabel('Drift')
    ax.set_title('3-6-9 HARMONIC GROUPING\n(Is there resonance at mod-3 positions?)', fontweight='bold')
    ax.grid(True, alpha=0.3)

    # Plot 3: FFT of turn-averaged drift
    ax = axes[1, 0]
    if len(avg_by_turn) >= 4:
        signal_centered = np.array(avg_by_turn) - np.mean(avg_by_turn)
        n = len(signal_centered)
        yf = fft(signal_centered)
        xf = fftfreq(n, d=1)[:n//2]
        magnitudes = 2.0/n * np.abs(yf[0:n//2])
        magnitudes_dB = to_dB_array(magnitudes + 0.0001)

        ax.bar(xf, magnitudes_dB, width=0.02, color='#f4a261', alpha=0.8, edgecolor='white')

        # Mark expected 3-6-9 frequencies
        ax.axvline(x=1/3, color='red', linestyle='--', alpha=0.7, label='1/3 (every 3 turns)')
        ax.axvline(x=1/6, color='blue', linestyle='--', alpha=0.7, label='1/6 (every 6 turns)')
        ax.axvline(x=1/9, color='green', linestyle='--', alpha=0.7, label='1/9 (every 9 turns)')

        ax.set_xlabel('Frequency (cycles/turn)')
        ax.set_ylabel('Magnitude (dB)')
        ax.set_title('FFT OF TURN-AVERAGED DRIFT\n(Looking for 3-6-9 harmonics)', fontweight='bold')
        ax.legend(fontsize=9)
        ax.grid(True, alpha=0.3)

    # Plot 4: Summary text
    ax = axes[1, 1]

    # Calculate statistics
    mean_369 = np.mean(mod3_groups[0]) if mod3_groups[0] else 0
    mean_other = np.mean(mod3_groups[1] + mod3_groups[2]) if (mod3_groups[1] or mod3_groups[2]) else 0
    ratio = mean_369 / mean_other if mean_other > 0 else 0

    summary = f"""
3-6-9 HARMONIC ANALYSIS SUMMARY

Average drift at 3-6-9 positions: {mean_369:.4f}
Average drift at other positions: {mean_other:.4f}
Ratio (3-6-9 / other): {ratio:.2f}x

Interpretation:
• Ratio > 1.0 = More drift at harmonic positions
• Ratio < 1.0 = Less drift at harmonic positions
• Ratio ≈ 1.0 = No harmonic pattern

N turns analyzed: {len(turns)}
Total data points: {sum(len(d) for d in turn_drifts.values())}
"""
    ax.text(0.1, 0.9, summary, transform=ax.transAxes, fontsize=11,
           verticalalignment='top', fontfamily='monospace',
           bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    ax.axis('off')

    fig.suptitle('RUN 008: 3-6-9 HARMONIC ANALYSIS\n(Tesla\'s "Key to the Universe"?)',
                fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_369_harmonics.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_369_harmonics.png")
    plt.close()

# =============================================================================
# MAIN
# =============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("RUN 008 DECIBEL-SCALE VISUALIZATIONS")
    print("=" * 60)

    print("\nLoading Run 008 data...")
    data = load_run008_data()

    print("\nGenerating dB-scale visualizations...")
    print("-" * 40)

    plot_db_heatmap(data)
    plot_phase_portrait(data)
    plot_spectral_analysis(data)
    plot_drift_dB(data)
    plot_369_harmonics(data)

    print("-" * 40)
    print(f"\nAll dB visualizations saved to: {OUTPUT_DIR}")
    print("=" * 60)
