#!/usr/bin/env python3
"""
Run 018 Recursive Learnings Visualizations
==========================================
Local visualization script for Run 018 data. Designed to be called from
the master visualize_armada.py or run standalone.

USAGE:
    py visualize_run018.py                      # Generate all visualizations
    py visualize_run018.py --experiment threshold
    py visualize_run018.py --experiment architecture
    py visualize_run018.py --experiment nyquist
    py visualize_run018.py --experiment gravity
    py visualize_run018.py --interactive        # Launch interactive dashboard

VISUALIZATIONS (by experiment):
    018a: Multi-threshold validation
        - threshold_zones        - Drift by escalation level with zone coloring
        - threshold_trajectories - Individual recovery trajectories by zone

    018b: Cross-architecture drift signatures
        - architecture_signatures - Peak drift, settling time, ringbacks by provider
        - architecture_trajectories - Representative curves per architecture

    018c: Nyquist sampling frequency
        - nyquist_comparison     - Final drift by sampling rate (high/low/none)
        - nyquist_statistics     - ANOVA results and effect sizes

    018d: Identity gravity dynamics
        - gravity_trajectories   - Recovery curves by anchor level (minimal/full)
        - gravity_parameters     - Fitted damped oscillator parameters (lambda, omega)

DRIFT MEASUREMENT NOTE:
    Run 018 uses PFI (Persona Fidelity Index) as the PRIMARY drift calculation:

        PFI = ||E(response) - E(baseline)||

    Where E = text-embedding-3-large (3072 dimensions).
    This IS mathematically sqrt(A^2+B^2+C^2+...) across all 3072 dimensions.

    PFI was validated in EXP-PFI-A (Cohen's d = 0.977).
    Keyword density (5 dimensions) is only a FALLBACK when embeddings unavailable.

INTEGRATION WITH visualize_armada.py:
    This script exports functions that can be called from the master visualizer:

    from experiments.temporal_stability.S7_ARMADA.11_CONTEXT_DAMPING.visualize_run018 import (
        generate_all_run018_visualizations,
        get_run018_data,
        VISUALIZATION_TYPES
    )

Author: Claude (with Lisan Al Gaib)
Date: December 12, 2025
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Optional, Tuple
import argparse
import warnings
warnings.filterwarnings('ignore')

import numpy as np
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
from scipy import stats

# Optional imports
try:
    import seaborn as sns
    HAS_SEABORN = True
except ImportError:
    HAS_SEABORN = False

try:
    import plotly.graph_objects as go
    HAS_PLOTLY = True
except ImportError:
    HAS_PLOTLY = False

# =============================================================================
# PATHS
# =============================================================================
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
# Store visualizations in central location: S7_ARMADA/visualizations/run018/
PICS_DIR = ARMADA_DIR / "visualizations" / "run018"
CANONICAL_RESULTS_DIR = ARMADA_DIR / "0_results" / "runs"

# Ensure output directory exists
PICS_DIR.mkdir(parents=True, exist_ok=True)

# =============================================================================
# EXPORTED CONSTANTS (for master visualizer integration)
# =============================================================================
VISUALIZATION_TYPES = ['threshold', 'architecture', 'nyquist', 'gravity', 'all']

# Threshold zones from design
THRESHOLD_ZONES = {
    "SAFE": (0, 0.9),
    "WARNING": (0.9, 1.23),
    "CRITICAL": (1.23, 1.8),
    "CATASTROPHIC": (1.8, float("inf"))
}

# Colors for zones
ZONE_COLORS = {
    "SAFE": "#2ecc71",       # Green
    "WARNING": "#f39c12",    # Orange
    "CRITICAL": "#e74c3c",   # Red
    "CATASTROPHIC": "#8e44ad" # Purple
}


def load_results(pattern: str) -> List[Dict]:
    """Load all result files matching a pattern."""
    results = []
    for f in RESULTS_DIR.glob(pattern):
        try:
            with open(f, 'r', encoding='utf-8') as fp:
                data = json.load(fp)
                data['_filename'] = f.name
                results.append(data)
        except Exception as e:
            print(f"Warning: Could not load {f}: {e}")
    return results


def get_zone(drift: float) -> str:
    """Get threshold zone for a drift value."""
    for zone, (low, high) in THRESHOLD_ZONES.items():
        if low <= drift < high:
            return zone
    return "CATASTROPHIC"


def damped_oscillator(t, A, lam, omega, phi, D_settled):
    """Damped oscillator model for recovery curves."""
    return A * np.exp(-lam * t) * np.cos(omega * t + phi) + D_settled


# =============================================================================
# 018a: Multi-Threshold Validation
# =============================================================================

def visualize_threshold(results: List[Dict]):
    """Visualize multi-threshold validation results."""
    if not results:
        print("No threshold results found")
        return

    print(f"\n=== 018a: Multi-Threshold Validation ({len(results)} files) ===")

    # Collect all drift values with their escalation levels
    all_drifts = []  # (level, drift, persona)
    zone_counts = {zone: 0 for zone in THRESHOLD_ZONES}

    for r in results:
        if 'sessions' in r:
            for session in r['sessions']:
                if 'probes' in session:
                    for probe in session['probes']:
                        level = probe.get('escalation_level', 0)
                        drift = probe.get('drift', 0)
                        persona = session.get('persona', 'unknown')
                        all_drifts.append((level, drift, persona))
                        zone_counts[get_zone(drift)] += 1

    if not all_drifts:
        print("No drift data found in threshold results")
        return

    # Figure 1: Drift by Escalation Level
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Scatter plot of drift vs escalation level
    ax1 = axes[0, 0]
    levels = [d[0] for d in all_drifts]
    drifts = [d[1] for d in all_drifts]

    # Color by zone
    colors = [ZONE_COLORS[get_zone(d)] for d in drifts]
    ax1.scatter(levels, drifts, c=colors, alpha=0.6, s=50)

    # Add threshold lines
    for zone, (low, high) in THRESHOLD_ZONES.items():
        if high < 3:
            ax1.axhline(y=low, color=ZONE_COLORS[zone], linestyle='--', alpha=0.5, label=f"{zone} ({low})")

    ax1.set_xlabel("Escalation Level")
    ax1.set_ylabel("Drift (PFI)")
    ax1.set_title("Drift by Escalation Level")
    ax1.legend(loc='upper left')
    ax1.set_ylim(0, max(drifts) * 1.1 if drifts else 2)

    # Plot 2: Zone distribution pie chart
    ax2 = axes[0, 1]
    zone_labels = [z for z in zone_counts if zone_counts[z] > 0]
    zone_values = [zone_counts[z] for z in zone_labels]
    zone_cols = [ZONE_COLORS[z] for z in zone_labels]
    ax2.pie(zone_values, labels=zone_labels, colors=zone_cols, autopct='%1.1f%%')
    ax2.set_title("Distribution Across Threshold Zones")

    # Plot 3: Box plot by escalation level
    ax3 = axes[1, 0]
    level_groups = {}
    for level, drift, _ in all_drifts:
        if level not in level_groups:
            level_groups[level] = []
        level_groups[level].append(drift)

    if level_groups:
        positions = sorted(level_groups.keys())
        data = [level_groups[p] for p in positions]
        bp = ax3.boxplot(data, positions=positions, widths=0.6)
        ax3.set_xlabel("Escalation Level")
        ax3.set_ylabel("Drift (PFI)")
        ax3.set_title("Drift Distribution by Level")

        # Add threshold lines
        for zone, (low, high) in THRESHOLD_ZONES.items():
            if high < 3:
                ax3.axhline(y=low, color=ZONE_COLORS[zone], linestyle='--', alpha=0.3)

    # Plot 4: Recovery dynamics by zone
    ax4 = axes[1, 1]
    # Group by persona and show trajectory
    persona_trajectories = {}
    for r in results:
        if 'sessions' in r:
            for session in r['sessions']:
                persona = session.get('persona', 'unknown')
                if 'probes' in session:
                    trajectory = [(p.get('escalation_level', 0), p.get('drift', 0))
                                  for p in session['probes']]
                    trajectory.sort(key=lambda x: x[0])
                    if persona not in persona_trajectories:
                        persona_trajectories[persona] = []
                    persona_trajectories[persona].append(trajectory)

    for persona, trajectories in list(persona_trajectories.items())[:5]:  # Limit to 5
        for traj in trajectories:
            if traj:
                x = [t[0] for t in traj]
                y = [t[1] for t in traj]
                ax4.plot(x, y, alpha=0.5, linewidth=1)

    # Add threshold lines
    for zone, (low, high) in THRESHOLD_ZONES.items():
        if high < 3:
            ax4.axhline(y=low, color=ZONE_COLORS[zone], linestyle='--', alpha=0.3, label=zone)

    ax4.set_xlabel("Escalation Level")
    ax4.set_ylabel("Drift (PFI)")
    ax4.set_title("Individual Trajectories")
    ax4.legend(loc='upper left')

    plt.suptitle("Run 018a: Multi-Threshold Validation", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run018a_threshold_validation.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary statistics
    print(f"\nZone Distribution:")
    for zone, count in zone_counts.items():
        pct = count / len(all_drifts) * 100 if all_drifts else 0
        print(f"  {zone}: {count} ({pct:.1f}%)")


# =============================================================================
# 018b: Cross-Architecture Drift Signatures
# =============================================================================

def visualize_architecture(results: List[Dict]):
    """Visualize cross-architecture drift signatures."""
    if not results:
        print("No architecture results found")
        return

    print(f"\n=== 018b: Cross-Architecture Drift Signatures ({len(results)} files) ===")

    # Collect metrics by provider
    provider_metrics = {}  # provider -> {peak_drift, settling_time, ringbacks, etc.}

    for r in results:
        provider = r.get('provider', 'unknown')
        if provider not in provider_metrics:
            provider_metrics[provider] = {
                'peak_drifts': [],
                'settling_times': [],
                'ringback_counts': [],
                'trajectories': []
            }

        if 'sessions' in r:
            for session in r['sessions']:
                if 'probes' in session:
                    drifts = [p.get('drift', 0) for p in session['probes']]
                    if drifts:
                        provider_metrics[provider]['peak_drifts'].append(max(drifts))
                        provider_metrics[provider]['trajectories'].append(drifts)

                if 'settling_time' in session:
                    provider_metrics[provider]['settling_times'].append(session['settling_time'])
                if 'ringback_count' in session:
                    provider_metrics[provider]['ringback_counts'].append(session['ringback_count'])

    if not provider_metrics:
        print("No provider data found")
        return

    # Figure: Architecture comparison
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    providers = list(provider_metrics.keys())
    colors = plt.cm.Set2(np.linspace(0, 1, len(providers)))

    # Plot 1: Peak drift by provider
    ax1 = axes[0, 0]
    peak_means = []
    peak_stds = []
    for p in providers:
        peaks = provider_metrics[p]['peak_drifts']
        peak_means.append(np.mean(peaks) if peaks else 0)
        peak_stds.append(np.std(peaks) if peaks else 0)

    bars = ax1.bar(providers, peak_means, yerr=peak_stds, color=colors, capsize=5)
    ax1.axhline(y=1.23, color='red', linestyle='--', alpha=0.5, label='Event Horizon')
    ax1.set_ylabel("Peak Drift (PFI)")
    ax1.set_title("Peak Drift by Architecture")
    ax1.legend()
    plt.setp(ax1.xaxis.get_majorticklabels(), rotation=45, ha='right')

    # Plot 2: Settling time by provider
    ax2 = axes[0, 1]
    settle_means = []
    settle_stds = []
    for p in providers:
        settles = provider_metrics[p]['settling_times']
        settle_means.append(np.mean(settles) if settles else 0)
        settle_stds.append(np.std(settles) if settles else 0)

    ax2.bar(providers, settle_means, yerr=settle_stds, color=colors, capsize=5)
    ax2.set_ylabel("Settling Time (probes)")
    ax2.set_title("Settling Time by Architecture")
    plt.setp(ax2.xaxis.get_majorticklabels(), rotation=45, ha='right')

    # Plot 3: Representative trajectories
    ax3 = axes[1, 0]
    for i, provider in enumerate(providers):
        trajectories = provider_metrics[provider]['trajectories']
        if trajectories:
            # Plot first trajectory as representative
            traj = trajectories[0]
            ax3.plot(range(len(traj)), traj, color=colors[i], label=provider, linewidth=2, alpha=0.8)

    ax3.axhline(y=1.23, color='red', linestyle='--', alpha=0.3, label='Event Horizon')
    ax3.set_xlabel("Probe Number")
    ax3.set_ylabel("Drift (PFI)")
    ax3.set_title("Representative Recovery Trajectories")
    ax3.legend(loc='upper right', fontsize=8)

    # Plot 4: Ringback count by provider
    ax4 = axes[1, 1]
    ring_means = []
    ring_stds = []
    for p in providers:
        rings = provider_metrics[p]['ringback_counts']
        ring_means.append(np.mean(rings) if rings else 0)
        ring_stds.append(np.std(rings) if rings else 0)

    ax4.bar(providers, ring_means, yerr=ring_stds, color=colors, capsize=5)
    ax4.set_ylabel("Ringback Count")
    ax4.set_title("Oscillation (Ringbacks) by Architecture")
    plt.setp(ax4.xaxis.get_majorticklabels(), rotation=45, ha='right')

    plt.suptitle("Run 018b: Cross-Architecture Drift Signatures", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run018b_architecture_signatures.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary
    print(f"\nArchitecture Summary:")
    print(f"{'Provider':<15} {'Peak Drift':<12} {'Settle Time':<12} {'Ringbacks':<10}")
    print("-" * 50)
    for i, p in enumerate(providers):
        print(f"{p:<15} {peak_means[i]:<12.3f} {settle_means[i]:<12.1f} {ring_means[i]:<10.1f}")


# =============================================================================
# 018c: Nyquist Sampling Frequency
# =============================================================================

def visualize_nyquist(results: List[Dict]):
    """Visualize Nyquist sampling frequency results."""
    if not results:
        print("No nyquist results found")
        return

    print(f"\n=== 018c: Nyquist Sampling Frequency ({len(results)} files) ===")

    # Group by sampling rate
    rate_data = {'high': [], 'low': [], 'none': []}

    for r in results:
        rate = r.get('sampling_rate', 'unknown')
        if rate in rate_data and 'sessions' in r:
            for session in r['sessions']:
                final_drift = session.get('final_drift', 0)
                cumulative_drift = session.get('cumulative_drift', 0)
                rate_data[rate].append({
                    'final': final_drift,
                    'cumulative': cumulative_drift,
                    'checkpoints': session.get('checkpoint_count', 0)
                })

    if not any(rate_data.values()):
        print("No sampling rate data found")
        return

    # Figure: Nyquist comparison
    fig, axes = plt.subplots(1, 3, figsize=(14, 5))

    colors = {'high': '#2ecc71', 'low': '#f39c12', 'none': '#e74c3c'}
    labels = {'high': 'High (every 5)', 'low': 'Low (every 20)', 'none': 'None (control)'}

    # Plot 1: Final drift comparison
    ax1 = axes[0]
    rates = ['high', 'low', 'none']
    final_means = []
    final_stds = []
    for rate in rates:
        finals = [d['final'] for d in rate_data[rate]]
        final_means.append(np.mean(finals) if finals else 0)
        final_stds.append(np.std(finals) if finals else 0)

    bars = ax1.bar([labels[r] for r in rates], final_means, yerr=final_stds,
                   color=[colors[r] for r in rates], capsize=5)
    ax1.axhline(y=1.23, color='red', linestyle='--', alpha=0.5, label='Event Horizon')
    ax1.set_ylabel("Final Drift (PFI)")
    ax1.set_title("Final Drift by Sampling Rate")
    ax1.legend()

    # Plot 2: Box plot comparison
    ax2 = axes[1]
    data_to_plot = []
    for rate in rates:
        finals = [d['final'] for d in rate_data[rate]]
        data_to_plot.append(finals if finals else [0])

    bp = ax2.boxplot(data_to_plot, labels=[labels[r] for r in rates], patch_artist=True)
    for patch, rate in zip(bp['boxes'], rates):
        patch.set_facecolor(colors[rate])
        patch.set_alpha(0.7)

    ax2.axhline(y=1.23, color='red', linestyle='--', alpha=0.3)
    ax2.set_ylabel("Final Drift (PFI)")
    ax2.set_title("Drift Distribution by Sampling Rate")

    # Plot 3: Statistical test
    ax3 = axes[2]
    # Perform ANOVA if we have enough data
    groups = [np.array([d['final'] for d in rate_data[r]]) for r in rates if rate_data[r]]

    if len(groups) >= 2 and all(len(g) >= 2 for g in groups):
        f_stat, p_value = stats.f_oneway(*groups)

        # Effect size (eta-squared)
        all_data = np.concatenate(groups)
        grand_mean = np.mean(all_data)
        ss_between = sum(len(g) * (np.mean(g) - grand_mean)**2 for g in groups)
        ss_total = np.sum((all_data - grand_mean)**2)
        eta_sq = ss_between / ss_total if ss_total > 0 else 0

        ax3.text(0.5, 0.7, f"ANOVA Results", fontsize=14, fontweight='bold',
                 ha='center', transform=ax3.transAxes)
        ax3.text(0.5, 0.5, f"F-statistic: {f_stat:.3f}", fontsize=12,
                 ha='center', transform=ax3.transAxes)
        ax3.text(0.5, 0.35, f"p-value: {p_value:.4f}", fontsize=12,
                 ha='center', transform=ax3.transAxes)
        ax3.text(0.5, 0.2, f"Effect size (η²): {eta_sq:.3f}", fontsize=12,
                 ha='center', transform=ax3.transAxes)

        sig = "SIGNIFICANT" if p_value < 0.05 else "Not significant"
        color = 'green' if p_value < 0.05 else 'red'
        ax3.text(0.5, 0.05, sig, fontsize=14, fontweight='bold', color=color,
                 ha='center', transform=ax3.transAxes)
    else:
        ax3.text(0.5, 0.5, "Insufficient data\nfor statistical test",
                 fontsize=12, ha='center', transform=ax3.transAxes)

    ax3.axis('off')
    ax3.set_title("Statistical Analysis")

    plt.suptitle("Run 018c: Nyquist Sampling Frequency", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run018c_nyquist_sampling.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary
    print(f"\nSampling Rate Comparison:")
    print(f"{'Rate':<20} {'Mean Drift':<12} {'Std Dev':<10} {'N':<5}")
    print("-" * 50)
    for i, rate in enumerate(rates):
        n = len(rate_data[rate])
        print(f"{labels[rate]:<20} {final_means[i]:<12.3f} {final_stds[i]:<10.3f} {n:<5}")


# =============================================================================
# 018d: Identity Gravity Dynamics
# =============================================================================

def visualize_gravity(results: List[Dict]):
    """Visualize identity gravity dynamics results."""
    if not results:
        print("No gravity results found")
        return

    print(f"\n=== 018d: Identity Gravity Dynamics ({len(results)} files) ===")

    # Group by anchor level
    anchor_data = {'minimal': [], 'full': []}
    fitted_params = {'minimal': [], 'full': []}

    for r in results:
        level = r.get('anchor_level', 'unknown')
        if level in anchor_data and 'sessions' in r:
            for session in r['sessions']:
                if 'probes' in session:
                    drifts = [p.get('drift', 0) for p in session['probes']]
                    anchor_data[level].append(drifts)

                    # Try to fit damped oscillator
                    if len(drifts) >= 5:
                        try:
                            t = np.arange(len(drifts))
                            # Initial guesses
                            A0 = max(drifts) - min(drifts)
                            D_settled0 = drifts[-1]

                            popt, _ = curve_fit(
                                damped_oscillator, t, drifts,
                                p0=[A0, 0.2, 1.0, 0, D_settled0],
                                bounds=([0, 0, 0, -np.pi, 0], [5, 2, 5, np.pi, 3]),
                                maxfev=5000
                            )
                            fitted_params[level].append({
                                'A': popt[0], 'lambda': popt[1],
                                'omega': popt[2], 'phi': popt[3],
                                'D_settled': popt[4]
                            })
                        except Exception:
                            pass

    if not any(anchor_data.values()):
        print("No anchor data found")
        return

    # Figure: Gravity dynamics
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    colors = {'minimal': '#e74c3c', 'full': '#2ecc71'}

    # Plot 1: Recovery trajectories by anchor level
    ax1 = axes[0, 0]
    for level in ['minimal', 'full']:
        for traj in anchor_data[level][:5]:  # Limit to 5 per level
            ax1.plot(range(len(traj)), traj, color=colors[level], alpha=0.4, linewidth=1)
        # Plot mean
        if anchor_data[level]:
            max_len = max(len(t) for t in anchor_data[level])
            padded = [t + [t[-1]] * (max_len - len(t)) for t in anchor_data[level]]
            mean_traj = np.mean(padded, axis=0)
            ax1.plot(range(len(mean_traj)), mean_traj, color=colors[level],
                     linewidth=3, label=f"{level.capitalize()} (mean)")

    ax1.axhline(y=1.23, color='gray', linestyle='--', alpha=0.3)
    ax1.set_xlabel("Probe Number")
    ax1.set_ylabel("Drift (PFI)")
    ax1.set_title("Recovery Trajectories by Anchor Level")
    ax1.legend()

    # Plot 2: Fitted parameters comparison
    ax2 = axes[0, 1]
    params = ['lambda', 'omega']
    x = np.arange(len(params))
    width = 0.35

    minimal_vals = []
    full_vals = []
    for param in params:
        m_vals = [p[param] for p in fitted_params['minimal']]
        f_vals = [p[param] for p in fitted_params['full']]
        minimal_vals.append(np.mean(m_vals) if m_vals else 0)
        full_vals.append(np.mean(f_vals) if f_vals else 0)

    bars1 = ax2.bar(x - width/2, minimal_vals, width, label='Minimal', color=colors['minimal'])
    bars2 = ax2.bar(x + width/2, full_vals, width, label='Full', color=colors['full'])
    ax2.set_xticks(x)
    ax2.set_xticklabels(['λ (damping)', 'ω (frequency)'])
    ax2.set_ylabel("Parameter Value")
    ax2.set_title("Fitted Oscillator Parameters")
    ax2.legend()

    # Plot 3: Gravity strength (γ) proxy - inverse settling time
    ax3 = axes[1, 0]
    gravity_proxy = {'minimal': [], 'full': []}
    for level in ['minimal', 'full']:
        for traj in anchor_data[level]:
            if len(traj) >= 3:
                # Proxy: rate of initial decay
                if traj[0] > 0:
                    decay_rate = (traj[0] - traj[2]) / traj[0] if traj[0] != 0 else 0
                    gravity_proxy[level].append(decay_rate)

    data_to_plot = [gravity_proxy['minimal'], gravity_proxy['full']]
    bp = ax3.boxplot(data_to_plot, labels=['Minimal', 'Full'], patch_artist=True)
    for patch, level in zip(bp['boxes'], ['minimal', 'full']):
        patch.set_facecolor(colors[level])
        patch.set_alpha(0.7)

    ax3.set_ylabel("Gravity Proxy (initial decay rate)")
    ax3.set_title("Identity Gravity Strength by Anchor Level")

    # Plot 4: Model fit quality (R²)
    ax4 = axes[1, 1]
    r_squared = {'minimal': [], 'full': []}

    for level in ['minimal', 'full']:
        for i, traj in enumerate(anchor_data[level]):
            if i < len(fitted_params[level]) and len(traj) >= 5:
                params = fitted_params[level][i]
                t = np.arange(len(traj))
                predicted = damped_oscillator(t, params['A'], params['lambda'],
                                               params['omega'], params['phi'],
                                               params['D_settled'])
                ss_res = np.sum((np.array(traj) - predicted)**2)
                ss_tot = np.sum((np.array(traj) - np.mean(traj))**2)
                r2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0
                r_squared[level].append(r2)

    if any(r_squared.values()):
        data_to_plot = [r_squared['minimal'] or [0], r_squared['full'] or [0]]
        bp = ax4.boxplot(data_to_plot, labels=['Minimal', 'Full'], patch_artist=True)
        for patch, level in zip(bp['boxes'], ['minimal', 'full']):
            patch.set_facecolor(colors[level])
            patch.set_alpha(0.7)

        ax4.axhline(y=0.8, color='green', linestyle='--', alpha=0.5, label='Target R²=0.8')
        ax4.set_ylabel("R² (model fit)")
        ax4.set_title("Damped Oscillator Model Fit Quality")
        ax4.legend()
    else:
        ax4.text(0.5, 0.5, "Insufficient data\nfor model fitting",
                 fontsize=12, ha='center', transform=ax4.transAxes)
        ax4.axis('off')

    plt.suptitle("Run 018d: Identity Gravity Dynamics", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run018d_gravity_dynamics.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary
    print(f"\nGravity Dynamics Summary:")
    for level in ['minimal', 'full']:
        n = len(anchor_data[level])
        n_fitted = len(fitted_params[level])
        mean_r2 = np.mean(r_squared[level]) if r_squared[level] else 0
        print(f"\n{level.capitalize()} anchor:")
        print(f"  Trajectories: {n}")
        print(f"  Fitted: {n_fitted}")
        print(f"  Mean R²: {mean_r2:.3f}")
        if fitted_params[level]:
            mean_lambda = np.mean([p['lambda'] for p in fitted_params[level]])
            mean_omega = np.mean([p['omega'] for p in fitted_params[level]])
            print(f"  Mean λ: {mean_lambda:.3f}")
            print(f"  Mean ω: {mean_omega:.3f}")


# =============================================================================
# EXPORTED FUNCTIONS (for master visualizer integration)
# =============================================================================

def get_run018_data() -> Dict[str, List[Dict]]:
    """Load all Run 018 data, organized by experiment type.

    Returns:
        Dict with keys: 'threshold', 'architecture', 'nyquist', 'gravity'
        Each value is a list of result dictionaries.
    """
    return {
        'threshold': load_results("run018a_threshold_*.json"),
        'architecture': load_results("run018b_architecture_*.json"),
        'nyquist': load_results("run018c_nyquist_*.json"),
        'gravity': load_results("run018d_gravity_*.json"),
    }


def generate_all_run018_visualizations(experiment: str = 'all') -> None:
    """Generate Run 018 visualizations.

    This is the main entry point for the master visualize_armada.py script.

    Args:
        experiment: Which experiment to visualize ('threshold', 'architecture',
                   'nyquist', 'gravity', or 'all')
    """
    print("=" * 60)
    print("RUN 018 VISUALIZATION: Recursive Learnings")
    print("=" * 60)
    print(f"Results directory: {RESULTS_DIR}")
    print(f"Output directory: {PICS_DIR}")

    data = get_run018_data()

    if experiment in ['threshold', 'all']:
        visualize_threshold(data['threshold'])

    if experiment in ['architecture', 'all']:
        visualize_architecture(data['architecture'])

    if experiment in ['nyquist', 'all']:
        visualize_nyquist(data['nyquist'])

    if experiment in ['gravity', 'all']:
        visualize_gravity(data['gravity'])

    print("\n" + "=" * 60)
    print("Visualization complete!")
    print("=" * 60)


# =============================================================================
# Main
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Visualize Run 018 results")
    parser.add_argument("--experiment", "-e",
                        choices=['threshold', 'architecture', 'nyquist', 'gravity', 'all'],
                        default='all', help="Which experiment to visualize")
    parser.add_argument("--interactive", action='store_true',
                        help="Launch interactive dashboard (requires plotly)")
    args = parser.parse_args()

    if args.interactive:
        if not HAS_PLOTLY:
            print("ERROR: Interactive mode requires plotly. Install with: pip install plotly")
            return
        print("Interactive dashboard not yet implemented for Run 018")
        return

    print("=" * 60)
    print("RUN 018 VISUALIZATION: Recursive Learnings")
    print("=" * 60)
    print(f"Results directory: {RESULTS_DIR}")
    print(f"Output directory: {PICS_DIR}")

    if args.experiment in ['threshold', 'all']:
        results = load_results("run018a_threshold_*.json")
        visualize_threshold(results)

    if args.experiment in ['architecture', 'all']:
        results = load_results("run018b_architecture_*.json")
        visualize_architecture(results)

    if args.experiment in ['nyquist', 'all']:
        results = load_results("run018c_nyquist_*.json")
        visualize_nyquist(results)

    if args.experiment in ['gravity', 'all']:
        results = load_results("run018d_gravity_*.json")
        visualize_gravity(results)

    print("\n" + "=" * 60)
    print("Visualization complete!")
    print("=" * 60)


if __name__ == "__main__":
    main()
