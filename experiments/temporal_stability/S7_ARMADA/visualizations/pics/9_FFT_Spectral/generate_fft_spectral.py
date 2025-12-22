#!/usr/bin/env python3
"""
9_FFT_Spectral: FFT Spectral Analysis of Identity Settling Dynamics
====================================================================
Generates FFT analysis visualizations showing frequency content of settling curves.

Data source: Run 023d (IRON CLAD Foundation - 750 experiments, 20+ probes)

Key insight: Different providers have characteristic "spectral fingerprints"
- Low frequency = gradual, smooth settling
- High frequency = rapid oscillations, "jitter"
- Multiple peaks = complex dynamics, resonance
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict
from scipy.fft import fft, fftfreq
from scipy import signal

# Paths
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
OUTPUT_DIR = Path(__file__).parent

# Provider colors (consistent with other visualizations)
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
}

PROVIDER_DISPLAY = {
    'anthropic': 'Anthropic',
    'openai': 'OpenAI',
    'google': 'Google',
    'xai': 'xAI',
    'together': 'Together.ai',
}


def load_data():
    """Load Run 023d results."""
    data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])


def extract_drift_timeseries(result):
    """Extract drift values from probe sequence."""
    probes = result.get('probe_sequence', [])
    return [p.get('drift', 0) for p in probes]


def generate_fft_spectral_plot(results):
    """
    Generate 4-panel FFT analysis visualization.

    Panels:
    1. FFT spectra by provider (averaged)
    2. Power spectral density comparison (bar chart)
    3. Spectrogram of example trajectory
    4. Dominant frequency by provider
    """
    print("Generating FFT Spectral Analysis...")

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.patch.set_facecolor('#0f0f1a')

    # Collect settling curves by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 4:  # Need minimum points for FFT
            by_provider[provider].append(drift_ts)

    print(f"  Providers found: {list(by_provider.keys())}")
    for p, trajs in by_provider.items():
        print(f"    {p}: {len(trajs)} trajectories")

    # =========================================================================
    # Panel 1: FFT Spectra by Provider
    # =========================================================================
    ax1 = axes[0, 0]
    ax1.set_facecolor('#1a1a2e')

    for provider, trajectories in by_provider.items():
        if len(trajectories) < 3:
            continue

        color = PROVIDER_COLORS.get(provider, '#888888')
        display_name = PROVIDER_DISPLAY.get(provider, provider)

        # Average FFT across trajectories
        all_ffts = []
        for drift_ts in trajectories[:50]:  # Limit for speed
            n = 16
            padded = np.zeros(n)
            length = min(len(drift_ts), n)
            padded[:length] = drift_ts[:length]

            # Apply Hanning window to reduce spectral leakage
            window = np.hanning(n)
            windowed = padded * window

            yf = np.abs(fft(windowed))[:n//2]
            xf = fftfreq(n, d=1.0)[:n//2]
            all_ffts.append(yf)

        if all_ffts:
            avg_fft = np.mean(all_ffts, axis=0)
            ax1.plot(xf, avg_fft, color=color, linewidth=2.5,
                    label=f"{display_name} (n={len(trajectories)})", alpha=0.9)

    ax1.set_xlabel('Frequency (cycles per probe)', fontsize=11, color='white')
    ax1.set_ylabel('Magnitude', fontsize=11, color='white')
    ax1.set_title('FFT Spectra by Provider\n(Averaged, Hanning windowed)',
                  fontsize=12, color='white', fontweight='bold')
    ax1.legend(loc='upper right', fontsize=9, facecolor='#1a1a2e',
               edgecolor='#333355', labelcolor='white')
    ax1.grid(True, alpha=0.3, color='#333355')
    ax1.set_xlim(0, 0.5)
    ax1.tick_params(colors='white')
    for spine in ax1.spines.values():
        spine.set_color('#333355')

    # =========================================================================
    # Panel 2: Power Spectral Density Comparison
    # =========================================================================
    ax2 = axes[0, 1]
    ax2.set_facecolor('#1a1a2e')

    provider_powers = []
    for provider, trajectories in by_provider.items():
        total_power = 0
        count = 0
        for drift_ts in trajectories[:50]:
            n = len(drift_ts)
            if n >= 4:
                yf = np.abs(fft(drift_ts))
                total_power += np.sum(yf**2) / n
                count += 1
        if count > 0:
            avg_power = total_power / count
            provider_powers.append((provider, avg_power))

    provider_powers.sort(key=lambda x: x[1], reverse=True)
    providers = [p[0] for p in provider_powers]
    powers = [p[1] for p in provider_powers]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]
    labels = [PROVIDER_DISPLAY.get(p, p) for p in providers]

    bars = ax2.bar(range(len(providers)), powers, color=colors, alpha=0.85,
                   edgecolor='white', linewidth=0.5)
    ax2.set_xticks(range(len(providers)))
    ax2.set_xticklabels(labels, rotation=45, ha='right', fontsize=10, color='white')
    ax2.set_ylabel('Total Spectral Power', fontsize=11, color='white')
    ax2.set_title('Settling Energy by Provider\n(Higher = more oscillation)',
                  fontsize=12, color='white', fontweight='bold')
    ax2.grid(True, alpha=0.3, axis='y', color='#333355')
    ax2.tick_params(colors='white')
    for spine in ax2.spines.values():
        spine.set_color('#333355')

    # =========================================================================
    # Panel 3: Spectrogram (Time-Frequency View)
    # =========================================================================
    ax3 = axes[1, 0]
    ax3.set_facecolor('#1a1a2e')

    # Find longest trajectory for detailed view
    best_trajectory = None
    best_provider = None
    best_length = 0

    for provider, trajectories in by_provider.items():
        for t in trajectories:
            if len(t) > best_length:
                best_trajectory = t
                best_provider = provider
                best_length = len(t)

    if best_trajectory is not None and best_length >= 8:
        nperseg = min(6, best_length // 2)
        if nperseg >= 2:
            f, t, Sxx = signal.spectrogram(
                np.array(best_trajectory),
                fs=1.0,
                nperseg=nperseg,
                noverlap=nperseg-1,
                mode='magnitude'
            )
            im = ax3.pcolormesh(t, f, Sxx, shading='gouraud', cmap='plasma')
            ax3.set_ylabel('Frequency', fontsize=11, color='white')
            ax3.set_xlabel('Probe Number (Time)', fontsize=11, color='white')
            display_name = PROVIDER_DISPLAY.get(best_provider, best_provider)
            ax3.set_title(f'Spectrogram: {display_name}\n(Time-frequency evolution)',
                         fontsize=12, color='white', fontweight='bold')
            cbar = plt.colorbar(im, ax=ax3)
            cbar.set_label('Magnitude', color='white')
            cbar.ax.yaxis.set_tick_params(color='white')
            plt.setp(plt.getp(cbar.ax.axes, 'yticklabels'), color='white')
    else:
        ax3.text(0.5, 0.5, 'Insufficient data\nfor spectrogram',
                ha='center', va='center', fontsize=14, color='white')
        ax3.set_title('Spectrogram (unavailable)', fontsize=12, color='white')

    ax3.tick_params(colors='white')
    for spine in ax3.spines.values():
        spine.set_color('#333355')

    # =========================================================================
    # Panel 4: Dominant Frequency by Provider
    # =========================================================================
    ax4 = axes[1, 1]
    ax4.set_facecolor('#1a1a2e')

    dom_freqs = []
    dom_labels = []
    dom_colors = []
    dom_stds = []

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
            dom_stds.append(np.std(all_dom))
            dom_labels.append(PROVIDER_DISPLAY.get(provider, provider))
            dom_colors.append(PROVIDER_COLORS.get(provider, '#888888'))

    x_pos = range(len(dom_labels))
    ax4.bar(x_pos, dom_freqs, yerr=dom_stds, color=dom_colors, alpha=0.85,
            edgecolor='white', linewidth=0.5, capsize=4, error_kw={'color': 'white', 'alpha': 0.7})
    ax4.set_xticks(x_pos)
    ax4.set_xticklabels(dom_labels, rotation=45, ha='right', fontsize=10, color='white')
    ax4.set_ylabel('Dominant Frequency', fontsize=11, color='white')
    ax4.set_title('Settling "Pitch" by Provider\n(Higher = faster oscillation)',
                  fontsize=12, color='white', fontweight='bold')
    ax4.grid(True, alpha=0.3, axis='y', color='#333355')
    ax4.tick_params(colors='white')
    for spine in ax4.spines.values():
        spine.set_color('#333355')

    # =========================================================================
    # Overall Title and Layout
    # =========================================================================
    plt.suptitle('FFT SPECTRAL ANALYSIS: Frequency Content of Identity Settling\n' +
                 'Run 023d: IRON CLAD Foundation (750 experiments, 20+ probes)',
                 fontsize=14, fontweight='bold', color='white', y=1.02)

    plt.tight_layout()

    # Save outputs
    for ext in ['png', 'svg']:
        output_path = OUTPUT_DIR / f'fft_spectral_analysis.{ext}'
        plt.savefig(output_path, dpi=150, bbox_inches='tight',
                    facecolor=fig.get_facecolor(), edgecolor='none')
        print(f"  Saved: {output_path}")

    plt.close()


def print_summary(results):
    """Print summary statistics."""
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        drift_ts = extract_drift_timeseries(r)
        if len(drift_ts) >= 4:
            by_provider[provider].append(drift_ts)

    print("\n" + "="*60)
    print("FFT SPECTRAL SUMMARY")
    print("="*60)

    for provider, trajectories in sorted(by_provider.items()):
        total_power = 0
        dom_freqs = []

        for drift_ts in trajectories[:50]:
            n = len(drift_ts)
            if n >= 4:
                yf = np.abs(fft(drift_ts))
                total_power += np.sum(yf**2) / n

                # Dominant freq
                n_fft = 16
                padded = np.zeros(n_fft)
                length = min(len(drift_ts), n_fft)
                padded[:length] = drift_ts[:length]
                yf2 = np.abs(fft(padded))[:n_fft//2]
                xf = fftfreq(n_fft, d=1.0)[:n_fft//2]
                if len(yf2) > 1:
                    dom_idx = np.argmax(yf2[1:]) + 1
                    dom_freqs.append(xf[dom_idx])

        avg_power = total_power / max(len(trajectories[:50]), 1)
        avg_dom = np.mean(dom_freqs) if dom_freqs else 0

        display = PROVIDER_DISPLAY.get(provider, provider)
        print(f"\n{display} ({len(trajectories)} trajectories):")
        print(f"  Avg Spectral Power: {avg_power:.4f}")
        print(f"  Dominant Frequency: {avg_dom:.4f} cycles/probe")


def main():
    print("Loading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    print("\nGenerating FFT Spectral Analysis...")
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    generate_fft_spectral_plot(results)
    print_summary(results)

    print("\n" + "="*60)
    print("FFT SPECTRAL ANALYSIS COMPLETE")
    print("="*60)


if __name__ == "__main__":
    main()
