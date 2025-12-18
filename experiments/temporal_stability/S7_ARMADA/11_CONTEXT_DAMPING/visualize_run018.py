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
# Store visualizations in central location: S7_ARMADA/visualizations/pics/run018/
PICS_DIR = ARMADA_DIR / "visualizations" / "pics" / "run018"
CANONICAL_RESULTS_DIR = ARMADA_DIR / "0_results" / "runs"
MANIFEST_DIR = ARMADA_DIR / "0_results" / "manifests"

# Ensure output directory exists
PICS_DIR.mkdir(parents=True, exist_ok=True)

# =============================================================================
# EXPORTED CONSTANTS (for master visualizer integration)
# =============================================================================
VISUALIZATION_TYPES = ['threshold', 'architecture', 'nyquist', 'gravity', 'model_breakdown', 'provider_variance', 'all']

# Maximum valid drift (above this = corrupted embedding data)
# Random vectors produce ~78.4 drift, validated data should be < 5.0
MAX_VALID_DRIFT = 5.0

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
    """Load all result files matching a pattern.

    Skips files prefixed with _CORRUPTED_ (known bad data).
    """
    results = []
    for f in RESULTS_DIR.glob(pattern):
        # Skip corrupted files (marked with _CORRUPTED_ prefix)
        if f.name.startswith('_CORRUPTED_'):
            continue
        try:
            with open(f, 'r', encoding='utf-8') as fp:
                data = json.load(fp)
                data['_filename'] = f.name
                results.append(data)
        except Exception as e:
            print(f"Warning: Could not load {f}: {e}")
    return results


def load_from_manifest(run_number: str = "018") -> Optional[Dict]:
    """Load the consolidated drift manifest.

    Returns:
        Dict with 'experiments' containing threshold/nyquist/gravity data,
        or None if manifest doesn't exist.
    """
    manifest_file = MANIFEST_DIR / f"RUN_{run_number}_DRIFT_MANIFEST.json"
    if not manifest_file.exists():
        print(f"Warning: Manifest not found at {manifest_file}")
        return None

    try:
        with open(manifest_file, 'r', encoding='utf-8') as f:
            return json.load(f)
    except Exception as e:
        print(f"Warning: Could not load manifest: {e}")
        return None


def get_manifest_experiment_data(manifest: Dict, experiment: str) -> List[Dict]:
    """Extract all runs for an experiment from manifest.

    The manifest stores data as:
        manifest["experiments"][experiment][model_name] = [list of run entries]

    Each run entry has: drift, max_drift, timestamp, file, i_am, probe_count, catastrophic

    Returns list of dicts with model name added to each entry.
    """
    results = []
    experiments = manifest.get("experiments", {})
    exp_data = experiments.get(experiment, {})

    for model, runs in exp_data.items():
        for run in runs:
            entry = run.copy()
            entry["model"] = model
            entry["_source"] = "manifest"
            results.append(entry)

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
    """Visualize multi-threshold validation results.

    Clean 2-panel layout showing:
    1. Drift distribution histogram with threshold zones
    2. Zone distribution pie chart

    From manifest data we have: drift, max_drift, model for each run.
    """
    if not results:
        print("No threshold results found")
        return

    print(f"\n=== 018a: Multi-Threshold Validation ({len(results)} entries) ===")

    # Collect all drift values and count zones
    all_drifts = []
    zone_counts = {zone: 0 for zone in THRESHOLD_ZONES}
    model_drifts = {}  # model -> list of drifts

    for r in results:
        # Manifest format (flat entry with direct drift values)
        if '_source' in r and r['_source'] == 'manifest':
            drift = r.get('drift', 0)
            max_drift = r.get('peak_drift', 0)
            model = r.get('model', 'unknown')

            all_drifts.append(drift)
            zone_counts[get_zone(drift)] += 1

            if model not in model_drifts:
                model_drifts[model] = []
            model_drifts[model].append(drift)

            # Also count max_drift if different
            if max_drift != drift and max_drift > 0:
                all_drifts.append(max_drift)
                zone_counts[get_zone(max_drift)] += 1

        # Original file format
        elif 'sessions' in r:
            for session in r['sessions']:
                if 'probes' in session:
                    for probe in session['probes']:
                        drift = probe.get('drift', 0)
                        all_drifts.append(drift)
                        zone_counts[get_zone(drift)] += 1

    if not all_drifts:
        print("No drift data found in threshold results")
        return

    # Create clean 2-panel figure
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    # Panel 1: Drift Distribution Histogram with Threshold Zones
    # Filter to reasonable range for visualization (exclude extreme outliers)
    plot_drifts = [d for d in all_drifts if d < 5.0]  # Focus on meaningful range

    # Create histogram
    bins = np.linspace(0, 3, 31)  # 0 to 3 in 0.1 increments
    n, bins_out, patches = ax1.hist(plot_drifts, bins=bins, edgecolor='black', alpha=0.7)

    # Color bars by zone
    for patch, left_edge in zip(patches, bins_out[:-1]):
        zone = get_zone(left_edge + 0.05)  # Use bin center
        patch.set_facecolor(ZONE_COLORS[zone])

    # Add vertical threshold lines
    ax1.axvline(x=0.9, color='orange', linestyle='--', linewidth=2, label='WARNING threshold (0.9)')
    ax1.axvline(x=1.23, color='red', linestyle='--', linewidth=2, label='CRITICAL threshold (1.23)')

    # Add zone labels
    ax1.axvspan(0, 0.9, alpha=0.1, color='green', label='SAFE zone')
    ax1.axvspan(0.9, 1.23, alpha=0.1, color='orange', label='WARNING zone')
    ax1.axvspan(1.23, 3.0, alpha=0.1, color='red', label='CRITICAL+ zone')

    ax1.set_xlabel("Drift (PFI)", fontsize=12)
    ax1.set_ylabel("Count", fontsize=12)
    ax1.set_title("Drift Distribution Across Threshold Zones", fontsize=13, fontweight='bold')
    ax1.legend(loc='upper right', fontsize=9)
    ax1.set_xlim(0, 3)

    # Add statistics annotation
    safe_count = zone_counts.get('SAFE', 0)
    warning_count = zone_counts.get('WARNING', 0)
    critical_count = zone_counts.get('CRITICAL', 0)
    catastrophic_count = zone_counts.get('CATASTROPHIC', 0)
    total = safe_count + warning_count + critical_count + catastrophic_count

    stats_text = f"N={total} measurements\n"
    stats_text += f"Mean: {np.mean(all_drifts):.3f}\n"
    stats_text += f"Median: {np.median(all_drifts):.3f}\n"
    stats_text += f"Std: {np.std(all_drifts):.3f}"
    ax1.text(0.98, 0.45, stats_text, transform=ax1.transAxes, fontsize=10,
             verticalalignment='top', horizontalalignment='right',
             bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    # Panel 2: Zone Distribution Pie Chart
    zone_labels = []
    zone_values = []
    zone_cols = []
    for zone in ['SAFE', 'WARNING', 'CRITICAL', 'CATASTROPHIC']:
        if zone_counts.get(zone, 0) > 0:
            zone_labels.append(zone)
            zone_values.append(zone_counts[zone])
            zone_cols.append(ZONE_COLORS[zone])

    wedges, texts, autotexts = ax2.pie(zone_values, labels=zone_labels, colors=zone_cols,
                                        autopct='%1.1f%%', startangle=90,
                                        textprops={'fontsize': 11})
    ax2.set_title("Zone Distribution\n(Event Horizon Analysis)", fontsize=13, fontweight='bold')

    # Add interpretation text
    interp_text = "Key Finding:\n"
    if warning_count / total < 0.1 if total > 0 else False:
        interp_text += "Minimal WARNING zone (~5%)\n"
        interp_text += "→ Binary behavior: SAFE or CRITICAL\n"
        interp_text += "→ Sharp threshold at D≈1.23"
    else:
        interp_text += f"WARNING: {warning_count/total*100:.1f}%\n"
        interp_text += "Gradual transition between zones"

    ax2.text(0.5, -0.22, interp_text, transform=ax2.transAxes, fontsize=10,
             verticalalignment='top', horizontalalignment='center',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    plt.suptitle("Run 018a: Multi-Threshold Validation\n51 Models × 3 Experiments = Event Horizon Discovery",
                 fontsize=14, fontweight='bold')
    plt.tight_layout(rect=[0, 0.05, 1, 0.93])

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

def get_provider_family(model_or_provider: str) -> str:
    """Map model names to provider families for aggregation."""
    name = model_or_provider.lower()

    if any(x in name for x in ['claude', 'anthropic']):
        return 'Anthropic'
    elif any(x in name for x in ['gpt', 'o3', 'o4', 'openai']):
        return 'OpenAI'
    elif any(x in name for x in ['gemini', 'google']):
        return 'Google'
    elif any(x in name for x in ['grok', 'xai']):
        return 'xAI'
    elif any(x in name for x in ['llama', 'meta']):
        return 'Meta'
    elif any(x in name for x in ['mistral', 'mixtral']):
        return 'Mistral'
    elif any(x in name for x in ['deepseek']):
        return 'DeepSeek'
    elif any(x in name for x in ['qwen']):
        return 'Alibaba'
    elif any(x in name for x in ['kimi']):
        return 'Moonshot'
    elif any(x in name for x in ['nemotron']):
        return 'NVIDIA'
    elif 'together' in name:
        return 'Together'
    else:
        return 'Other'


def visualize_architecture(results: List[Dict]):
    """Visualize cross-architecture drift signatures.

    Aggregates by provider FAMILY (Anthropic, OpenAI, Google, etc.)
    not by individual model, for cleaner visualization.
    """
    if not results:
        print("No architecture results found")
        return

    print(f"\n=== 018b: Cross-Architecture Drift Signatures ({len(results)} files) ===")

    # Collect metrics by PROVIDER FAMILY (not individual model)
    family_metrics = {}

    for r in results:
        # NEW FORMAT: Data is in 'subjects' array with provider per subject
        if 'subjects' in r:
            for subject in r['subjects']:
                raw_provider = subject.get('provider', 'unknown')
                family = get_provider_family(raw_provider)

                if family not in family_metrics:
                    family_metrics[family] = {
                        'peak_drifts': [],
                        'settling_times': [],
                        'ringback_counts': [],
                        'trajectories': [],
                        'models': set(),
                        'model_metrics': {}  # Per-model breakdown
                    }

                family_metrics[family]['models'].add(raw_provider)

                # Track per-model metrics for intra-provider visualization
                if raw_provider not in family_metrics[family]['model_metrics']:
                    family_metrics[family]['model_metrics'][raw_provider] = {
                        'peak_drifts': [], 'settling_times': [], 'ringback_counts': []
                    }

                if 'peak_drift' in subject and subject['peak_drift'] < MAX_VALID_DRIFT:
                    family_metrics[family]['peak_drifts'].append(subject['peak_drift'])
                    family_metrics[family]['model_metrics'][raw_provider]['peak_drifts'].append(subject['peak_drift'])
                if 'settling_time' in subject:
                    family_metrics[family]['settling_times'].append(subject['settling_time'])
                    family_metrics[family]['model_metrics'][raw_provider]['settling_times'].append(subject['settling_time'])
                if 'ringback_count' in subject:
                    family_metrics[family]['ringback_counts'].append(subject['ringback_count'])
                    family_metrics[family]['model_metrics'][raw_provider]['ringback_counts'].append(subject['ringback_count'])

                if 'full_recovery_curve' in subject:
                    family_metrics[family]['trajectories'].append(subject['full_recovery_curve'])
                elif 'probe_sequence' in subject:
                    drifts = [p.get('drift', 0) for p in subject['probe_sequence']]
                    if drifts:
                        family_metrics[family]['trajectories'].append(drifts)

        # LEGACY FORMAT
        elif 'sessions' in r:
            raw_provider = r.get('provider', 'unknown')
            family = get_provider_family(raw_provider)

            if family not in family_metrics:
                family_metrics[family] = {
                    'peak_drifts': [],
                    'settling_times': [],
                    'ringback_counts': [],
                    'trajectories': [],
                    'models': set(),
                    'model_metrics': {}
                }

            family_metrics[family]['models'].add(raw_provider)

            if raw_provider not in family_metrics[family]['model_metrics']:
                family_metrics[family]['model_metrics'][raw_provider] = {
                    'peak_drifts': [], 'settling_times': [], 'ringback_counts': []
                }

            for session in r['sessions']:
                if 'probes' in session:
                    drifts = [p.get('drift', 0) for p in session['probes']]
                    if drifts:
                        peak = max(drifts)
                        # Only include valid drift values (< MAX_VALID_DRIFT)
                        if peak < MAX_VALID_DRIFT:
                            family_metrics[family]['peak_drifts'].append(peak)
                            family_metrics[family]['model_metrics'][raw_provider]['peak_drifts'].append(peak)
                            family_metrics[family]['trajectories'].append(drifts)

                if 'settling_time' in session:
                    family_metrics[family]['settling_times'].append(session['settling_time'])
                    family_metrics[family]['model_metrics'][raw_provider]['settling_times'].append(session['settling_time'])
                if 'ringback_count' in session:
                    family_metrics[family]['ringback_counts'].append(session['ringback_count'])

    if not family_metrics:
        print("No provider data found")
        return

    # Filter out families with insufficient data (n < 3) to remove noise
    MIN_SAMPLES = 3
    filtered_metrics = {f: v for f, v in family_metrics.items()
                        if len(v['peak_drifts']) >= MIN_SAMPLES}

    if not filtered_metrics:
        print("No provider families with sufficient data (n >= 3)")
        return

    # Sort families by number of data points (most data first)
    families = sorted(filtered_metrics.keys(),
                      key=lambda f: len(filtered_metrics[f]['peak_drifts']),
                      reverse=True)

    # Use filtered metrics from here on
    family_metrics = filtered_metrics

    # Use a nice color palette
    family_colors = {
        'Anthropic': '#D4A574',   # Warm tan
        'OpenAI': '#74B49B',      # Sage green
        'Google': '#4285F4',      # Google blue
        'xAI': '#1DA1F2',         # Twitter blue
        'Meta': '#0668E1',        # Meta blue
        'Mistral': '#FF6B35',     # Orange
        'DeepSeek': '#7C3AED',    # Purple
        'Alibaba': '#FF6A00',     # Alibaba orange
        'Moonshot': '#EC4899',    # Pink
        'NVIDIA': '#76B900',      # NVIDIA green
        'Together': '#6366F1',    # Indigo
        'Other': '#9CA3AF'        # Gray
    }

    colors = [family_colors.get(f, '#9CA3AF') for f in families]

    # Create clean 2x2 figure
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Calculate means and stds for each family
    peak_means = []
    peak_stds = []
    settle_means = []
    settle_stds = []
    ring_means = []
    ring_stds = []
    sample_counts = []

    for f in families:
        peaks = family_metrics[f]['peak_drifts']
        settles = family_metrics[f]['settling_times']
        rings = family_metrics[f]['ringback_counts']

        peak_means.append(np.mean(peaks) if peaks else 0)
        peak_stds.append(np.std(peaks) if len(peaks) > 1 else 0)
        settle_means.append(np.mean(settles) if settles else 0)
        settle_stds.append(np.std(settles) if len(settles) > 1 else 0)
        ring_means.append(np.mean(rings) if rings else 0)
        ring_stds.append(np.std(rings) if len(rings) > 1 else 0)
        sample_counts.append(len(peaks))

    # Plot 1: Peak drift by provider family (horizontal bar for readability)
    ax1 = axes[0, 0]
    y_pos = np.arange(len(families))
    bars = ax1.barh(y_pos, peak_means, xerr=peak_stds, color=colors, capsize=3, alpha=0.8)
    ax1.axvline(x=1.23, color='red', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon (1.23)')
    ax1.set_yticks(y_pos)
    ax1.set_yticklabels([f"{f}\n(n={sample_counts[i]})" for i, f in enumerate(families)], fontsize=9)
    ax1.set_xlabel("Peak Drift (PFI)", fontsize=11)
    ax1.set_title("Peak Drift by Provider Family", fontsize=12, fontweight='bold')
    ax1.legend(loc='lower right', fontsize=9)
    # Extend x-axis to show event horizon line for context
    ax1.set_xlim(0, max(1.4, max(peak_means) * 1.3) if peak_means else 1.5)

    # Plot 2: Settling time comparison (horizontal bar)
    # Note: Max probes in experiment was 6, so values at 6.0 may indicate ceiling effect
    ax2 = axes[0, 1]
    # Clip error bars to prevent negative values (can't have negative settling time)
    settle_err_lower = [min(std, mean) for mean, std in zip(settle_means, settle_stds)]
    settle_err_upper = settle_stds
    bars2 = ax2.barh(y_pos, settle_means, xerr=[settle_err_lower, settle_err_upper],
                     color=colors, capsize=3, alpha=0.8)
    ax2.set_yticks(y_pos)
    ax2.set_yticklabels(families, fontsize=9)
    ax2.set_xlabel("Settling Time (probes)", fontsize=11)
    ax2.set_title("Recovery Speed by Provider Family\n(max probes = 6)", fontsize=12, fontweight='bold')
    ax2.set_xlim(0, 7)  # Show full range up to max

    # Plot 3: Drift stability scatter (mean vs std)
    ax3 = axes[1, 0]
    for i, f in enumerate(families):
        ax3.scatter(peak_means[i], peak_stds[i], c=[colors[i]], s=sample_counts[i]*3 + 50,
                   alpha=0.7, edgecolors='black', linewidth=1)
    ax3.axvline(x=1.23, color='red', linestyle='--', alpha=0.5)
    ax3.set_xlabel("Mean Peak Drift", fontsize=11)
    ax3.set_ylabel("Drift Variability (Std)", fontsize=11)
    ax3.set_title("Stability Profile: Mean vs Variance\n(bubble size = sample count)", fontsize=12, fontweight='bold')
    # Extend x-axis to show event horizon for context
    ax3.set_xlim(0, max(1.4, max(peak_means) * 1.3) if peak_means else 1.5)
    # Create custom legend with simple line markers (not bubbles)
    from matplotlib.lines import Line2D
    legend_elements = [Line2D([0], [0], color=colors[i], linewidth=3, label=f)
                       for i, f in enumerate(families)]
    ax3.legend(handles=legend_elements, loc='upper right', fontsize=6, ncol=2, framealpha=0.9)

    # Plot 4: Ringback oscillation comparison
    ax4 = axes[1, 1]
    # Clip error bars to prevent negative values
    ring_err_lower = [min(std, mean) for mean, std in zip(ring_means, ring_stds)]
    ring_err_upper = ring_stds
    bars4 = ax4.barh(y_pos, ring_means, xerr=[ring_err_lower, ring_err_upper],
                     color=colors, capsize=3, alpha=0.8)
    ax4.set_yticks(y_pos)
    ax4.set_yticklabels(families, fontsize=9)
    ax4.set_xlabel("Ringback Count (oscillations)", fontsize=11)
    ax4.set_title("Identity Oscillation by Provider Family", fontsize=12, fontweight='bold')
    ax4.set_xlim(0, None)  # Ensure starts at 0

    plt.suptitle("Run 018b: Cross-Architecture Drift Signatures\nProvider Family Comparison (51 models aggregated)",
                 fontsize=14, fontweight='bold')
    plt.tight_layout(rect=[0, 0, 1, 0.95])

    outfile = PICS_DIR / "run018b_architecture_signatures.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary
    print(f"\nArchitecture Summary (by Provider Family):")
    print(f"{'Family':<12} {'N':<5} {'Peak Drift':<12} {'Settle Time':<12} {'Ringbacks':<10}")
    print("-" * 55)
    for i, f in enumerate(families):
        print(f"{f:<12} {sample_counts[i]:<5} {peak_means[i]:<12.3f} {settle_means[i]:<12.1f} {ring_means[i]:<10.1f}")

    # Generate intra-provider breakdown visualizations
    visualize_architecture_intra(family_metrics, family_colors)


def visualize_architecture_intra(family_metrics: Dict, family_colors: Dict):
    """Generate per-provider model breakdown visualizations.

    Creates separate figures showing model-level signatures within each provider family.
    Shows horizontal bar chart of peak drift for each model within a provider.

    Layout strategy:
    - Figure _2: Top 4 providers (OpenAI, Anthropic, xAI, Google) - 2x2 grid
    - Figure _3: Open-source/Together.ai ecosystem (Meta, DeepSeek, Mistral, Alibaba, Moonshot) - combined view
    """
    # Only generate for families with multiple models AND per-model data
    families_with_models = {f: v for f, v in family_metrics.items()
                           if len(v.get('models', set())) > 1 and
                           'model_metrics' in v and len(v['model_metrics']) > 1}

    if not families_with_models:
        print("No families with per-model breakdown data")
        return

    # Sort by total sample count
    all_families = sorted(families_with_models.keys(),
                         key=lambda f: len(family_metrics[f]['peak_drifts']),
                         reverse=True)

    # Split into major providers vs open-source ecosystem
    major_providers = ['OpenAI', 'Anthropic', 'xAI', 'Google']
    opensource_families = ['Meta', 'DeepSeek', 'Mistral', 'Alibaba', 'Moonshot', 'Together']

    major = [f for f in all_families if f in major_providers]
    opensource = [f for f in all_families if f in opensource_families]

    # Pastel color palette - soft, inviting, professional
    pastel_colors = {
        'OpenAI': {'base': '#98D8AA', 'dark': '#5BB381', 'light': '#C5EBCF', 'accent': '#2E7D4A', 'bg': '#F0FFF4'},
        'Anthropic': {'base': '#F7C59F', 'dark': '#E8A66D', 'light': '#FDDFC2', 'accent': '#B8723B', 'bg': '#FFFAF5'},
        'Google': {'base': '#A8D4F0', 'dark': '#6BB3DE', 'light': '#D0E8F7', 'accent': '#2E6B8A', 'bg': '#F5FAFF'},
        'xAI': {'base': '#B8C5F2', 'dark': '#8A9DE0', 'light': '#D8E0F8', 'accent': '#4A5899', 'bg': '#F8F9FF'},
    }

    # Figure _2: Major providers (2x2 grid) - PASTEL VERSION
    if major:
        n_plots = len(major)
        if n_plots == 1:
            nrows, ncols = 1, 1
        elif n_plots == 2:
            nrows, ncols = 1, 2
        else:
            nrows, ncols = 2, 2

        # Set up pastel style with light background
        plt.style.use('default')
        fig, axes = plt.subplots(nrows, ncols, figsize=(14, 10 if nrows == 2 else 5),
                                  facecolor='#FAFBFC')

        if n_plots == 1:
            axes = np.array([axes])
        axes = axes.flatten()

        for idx, family in enumerate(major):
            ax = axes[idx]

            colors = pastel_colors.get(family, {'base': '#C4C4C4', 'dark': '#888888', 'light': '#E8E8E8', 'accent': '#444444', 'bg': '#F8F8F8'})
            ax.set_facecolor(colors['bg'])

            model_metrics = family_metrics[family].get('model_metrics', {})

            # Filter out models with zero or no data (corrupted entries)
            valid_models = {m: v for m, v in model_metrics.items()
                          if v['peak_drifts'] and np.mean(v['peak_drifts']) > 0}

            # Sort models by mean peak drift
            models = sorted(valid_models.keys(),
                          key=lambda m: np.mean(valid_models[m]['peak_drifts']))

            # Limit to top 15 models if too many (increased from 12)
            if len(models) > 15:
                models = models[:15]

            # Use valid_models for data
            model_metrics = valid_models

            y_pos = np.arange(len(models))
            means = [np.mean(model_metrics[m]['peak_drifts']) if model_metrics[m]['peak_drifts'] else 0 for m in models]
            stds = [np.std(model_metrics[m]['peak_drifts']) if len(model_metrics[m]['peak_drifts']) > 1 else 0 for m in models]
            counts = [len(model_metrics[m]['peak_drifts']) for m in models]

            # Clip error bars to prevent negative values (drift can't be negative)
            err_lower = [min(std, mean) for mean, std in zip(means, stds)]
            err_upper = stds

            # Create soft gradient effect - lighter colors for lower drift, base for higher
            bar_colors = []
            for mean in means:
                # Interpolate between light and base based on drift
                intensity = min(mean / 1.2, 1.0)  # Normalize to 0-1
                r1, g1, b1 = int(colors['light'][1:3], 16), int(colors['light'][3:5], 16), int(colors['light'][5:7], 16)
                r2, g2, b2 = int(colors['base'][1:3], 16), int(colors['base'][3:5], 16), int(colors['base'][5:7], 16)
                r = int(r1 + (r2 - r1) * intensity)
                g = int(g1 + (g2 - g1) * intensity)
                b = int(b1 + (b2 - b1) * intensity)
                bar_colors.append(f'#{r:02x}{g:02x}{b:02x}')

            # Draw bars with soft shadow effect
            for i, (y, mean, err_l, err_u, bar_color) in enumerate(zip(y_pos, means, err_lower, err_upper, bar_colors)):
                # Soft shadow layer (offset slightly)
                ax.barh(y + 0.02, mean, height=0.65, color='#000000', alpha=0.08, zorder=1)
                # Main bar with rounded appearance (using alpha gradient)
                ax.barh(y, mean, height=0.6, color=bar_color, alpha=0.85, zorder=2,
                       edgecolor=colors['dark'], linewidth=1.0)
                # Highlight strip at top of bar for 3D effect
                ax.barh(y + 0.15, mean, height=0.15, color='#FFFFFF', alpha=0.3, zorder=3)
                # Error bar
                ax.errorbar(mean, y, xerr=[[err_l], [err_u]], fmt='none',
                           color=colors['accent'], capsize=4, capthick=1.5, zorder=4, alpha=0.8)

            # Event horizon line - softer coral red
            ax.axvline(x=1.23, color='#E57373', linestyle='--', linewidth=2.5, alpha=0.7, zorder=5)
            ax.axvspan(1.23, max(1.5, max(means) * 1.3) if means else 1.5, alpha=0.08, color='#FFCDD2', zorder=0)

            ax.set_xlim(0, max(1.4, max(means) * 1.3) if means else 1.5)

            # Clean model names for display
            clean_names = [m.replace('claude-', '').replace('gpt-', '').replace('gemini-', '')
                          .replace('grok-', '').replace('llama', 'L').replace('mistral-', '')
                          for m in models]
            ax.set_yticks(y_pos)
            ax.set_yticklabels([f"{n} (n={counts[i]})" for i, n in enumerate(clean_names)],
                              fontsize=9, color='#000000', fontweight='medium')
            ax.set_xlabel("Peak Drift (PFI)", fontsize=11, color='#000000', fontweight='bold')
            ax.set_title(f"{family} Models", fontsize=14, fontweight='bold', color=colors['accent'],
                        pad=12)

            # Soft grid styling
            ax.grid(axis='x', alpha=0.3, color='#CCCCCC', linestyle='-', linewidth=0.5)
            ax.tick_params(colors='#000000', length=4)
            ax.set_axisbelow(True)  # Grid behind bars

            # Subtle spines
            for spine in ['top', 'right']:
                ax.spines[spine].set_visible(False)
            for spine in ['bottom', 'left']:
                ax.spines[spine].set_color('#CCCCCC')
                ax.spines[spine].set_linewidth(0.8)

        # Hide unused subplots
        for idx in range(len(major), len(axes)):
            axes[idx].axis('off')

        # Clean title
        fig.suptitle("Run 018: Intra-Provider Model Signatures (Part 1)\nModel-Level Drift Comparison",
                     fontsize=16, fontweight='bold', color='#2C3E50', y=0.98)

        # Subtle footer
        fig.text(0.5, 0.01, "Event Horizon (D=1.23) marks identity collapse threshold  |  PFI = Persona Fidelity Index",
                fontsize=9, ha='center', color='#888888', style='italic')

        plt.tight_layout(rect=[0, 0.03, 1, 0.95])

        outfile = PICS_DIR / "run018b_architecture_signatures_2.png"
        plt.savefig(outfile, dpi=200, bbox_inches='tight', facecolor='#FAFBFC', edgecolor='none')
        print(f"Saved: {outfile}")
        plt.close()

        # Reset style for other plots
        plt.style.use('default')

    # Figure _3: Open-source ecosystem (all models from Meta, DeepSeek, Mistral, etc.)
    if opensource:
        # Collect all models across open-source families
        all_opensource_models = []
        for family in opensource:
            model_metrics = family_metrics[family].get('model_metrics', {})
            base_color = family_colors.get(family, '#9CA3AF')
            for model, metrics in model_metrics.items():
                # Filter out models with no valid drift data (all zeros = corrupted runs)
                valid_drifts = [d for d in metrics['peak_drifts'] if d > 0]
                if valid_drifts:
                    all_opensource_models.append({
                        'model': model,
                        'family': family,
                        'color': base_color,
                        'mean': np.mean(valid_drifts),
                        'std': np.std(valid_drifts) if len(valid_drifts) > 1 else 0,
                        'count': len(valid_drifts)  # Only count valid runs
                    })

        # Sort by mean peak drift DESCENDING (highest drift at top)
        all_opensource_models.sort(key=lambda x: x['mean'], reverse=True)

        if all_opensource_models:
            # Create single comprehensive figure
            n_models = len(all_opensource_models)
            fig_height = max(8, n_models * 0.4)
            fig, ax = plt.subplots(figsize=(12, fig_height))

            y_pos = np.arange(n_models)
            means = [m['mean'] for m in all_opensource_models]
            stds = [m['std'] for m in all_opensource_models]
            colors = [m['color'] for m in all_opensource_models]
            counts = [m['count'] for m in all_opensource_models]
            families_list = [m['family'] for m in all_opensource_models]

            # Clip error bars
            err_lower = [min(std, mean) for mean, std in zip(means, stds)]
            err_upper = stds

            # Create bars with family colors
            bars = ax.barh(y_pos, means, xerr=[err_lower, err_upper], color=colors, alpha=0.7, capsize=2)
            ax.axvline(x=1.23, color='red', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon (1.23)')
            ax.set_xlim(0, max(1.4, max(means) * 1.3) if means else 1.5)

            # Clean model names and add family tag
            labels = []
            for m in all_opensource_models:
                clean = m['model'].replace('meta-llama/', '').replace('deepseek-ai/', '')
                clean = clean.replace('mistralai/', '').replace('Qwen/', '')
                labels.append(f"{clean} [{m['family']}] (n={m['count']})")

            ax.set_yticks(y_pos)
            ax.set_yticklabels(labels, fontsize=8)
            ax.set_xlabel("Peak Drift (PFI)", fontsize=11)
            ax.set_title("Open-Source Ecosystem Models (sorted by drift)", fontsize=12, fontweight='bold')
            ax.legend(loc='lower right', fontsize=9)

            plt.suptitle("Run 018b: Open-Source / Together.ai Ecosystem\nMeta, DeepSeek, Mistral, Alibaba, Moonshot Models",
                         fontsize=13, fontweight='bold')
            plt.tight_layout(rect=[0, 0, 1, 0.95])

            outfile = PICS_DIR / "run018b_architecture_signatures_3.png"
            plt.savefig(outfile, dpi=150, bbox_inches='tight')
            print(f"Saved: {outfile}")
            plt.close()

    # Figure _4: Cross-provider comparison (1 representative model per provider)
    # Shows peak drift, settling time, and ringback count side-by-side
    visualize_architecture_cross_provider(family_metrics, family_colors)


def visualize_architecture_cross_provider(family_metrics: Dict, family_colors: Dict):
    """Generate cross-provider comparison with 1 representative model per provider.

    Shows ONLY peak drift (the only unconstrained metric).
    Settling time and ringback data have ceiling effects (max 6 probes)
    making them unreliable for cross-provider comparison.

    Picks the model with the most data points from each provider family.
    """
    # Collect 1 representative model per provider (the one with most data)
    representatives = []

    for family, metrics in family_metrics.items():
        model_metrics = metrics.get('model_metrics', {})
        if not model_metrics:
            continue

        # Find model with most data points
        best_model = None
        best_count = 0
        for model, m in model_metrics.items():
            count = len(m.get('peak_drifts', []))
            if count > best_count:
                best_count = count
                best_model = model

        if best_model and best_count > 0:
            m = model_metrics[best_model]
            representatives.append({
                'family': family,
                'model': best_model,
                'color': family_colors.get(family, '#9CA3AF'),
                'peak_drift': np.mean(m['peak_drifts']) if m['peak_drifts'] else 0,
                'peak_std': np.std(m['peak_drifts']) if len(m['peak_drifts']) > 1 else 0,
                'count': best_count
            })

    if not representatives:
        print("No representative models found for cross-provider comparison")
        return

    # Sort by peak drift (descending - highest at top)
    representatives.sort(key=lambda x: x['peak_drift'], reverse=True)

    # Create single-panel figure (peak drift only - other metrics have ceiling effects)
    fig, ax = plt.subplots(figsize=(12, max(6, len(representatives) * 0.5)))

    y_pos = np.arange(len(representatives))
    colors = [r['color'] for r in representatives]

    # Clean labels: "family: model (n=X)"
    labels = []
    for r in representatives:
        clean_model = r['model'].replace('claude-', '').replace('gpt-', '').replace('gemini-', '')
        clean_model = clean_model.replace('grok-', '').replace('meta-llama/', '').replace('deepseek-ai/', '')
        clean_model = clean_model.replace('mistralai/', '').replace('Qwen/', '')
        labels.append(f"{r['family']}: {clean_model} (n={r['count']})")

    # Peak Drift comparison
    peak_drifts = [r['peak_drift'] for r in representatives]
    peak_stds = [r['peak_std'] for r in representatives]
    err_lower = [min(std, mean) for mean, std in zip(peak_drifts, peak_stds)]

    bars = ax.barh(y_pos, peak_drifts, xerr=[err_lower, peak_stds], color=colors, alpha=0.7, capsize=3)
    ax.axvline(x=1.23, color='red', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon (1.23)')
    ax.set_yticks(y_pos)
    ax.set_yticklabels(labels, fontsize=10)
    ax.set_xlabel("Peak Drift (PFI)", fontsize=12)
    ax.set_title("Peak Drift by Provider Family\n(1 representative model each, sorted by drift)", fontsize=12, fontweight='bold')
    ax.set_xlim(0, max(1.4, max(peak_drifts) * 1.3) if peak_drifts else 1.5)
    ax.legend(loc='lower right', fontsize=9)

    # Add caveat note
    caveat = "Note: Settling time and ringback metrics excluded due to\nceiling effects (max 6 probes in architecture experiment)"
    ax.text(0.98, 0.02, caveat, transform=ax.transAxes, fontsize=8,
            verticalalignment='bottom', horizontalalignment='right',
            bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    plt.suptitle("Run 018b: Cross-Provider Model Comparison\n1 Representative Model per Provider Family",
                 fontsize=14, fontweight='bold')
    plt.tight_layout(rect=[0, 0, 1, 0.93])

    outfile = PICS_DIR / "run018b_architecture_signatures_4.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()


# =============================================================================
# 018c: Nyquist Sampling Frequency
# =============================================================================

def visualize_nyquist(results: List[Dict]):
    """Visualize Nyquist sampling frequency results.

    Uses manifest data which now includes sampling_rate field.
    Falls back to file loading only if manifest data doesn't have sampling_rate.
    """
    print(f"\n=== 018c: Nyquist Sampling Frequency ===")

    # Group by sampling rate
    rate_data = {'high': [], 'low': [], 'none': []}

    # First try using manifest data (which now includes sampling_rate)
    for r in results:
        # Manifest format: flat entry with _source='manifest'
        if r.get('_source') == 'manifest':
            rate = r.get('sampling_rate', 'unknown')
            drift = r.get('drift', 0)
            max_drift = r.get('peak_drift', 0)

            # Skip corrupted entries (drift=0 with max_drift > 5.0)
            if drift == 0 and max_drift > MAX_VALID_DRIFT:
                continue

            if rate in rate_data:
                rate_data[rate].append({
                    'final': drift,
                    'cumulative': 0,  # Not stored in manifest
                    'checkpoints': r.get('probe_count', 0),
                    'peak': max_drift,
                    'aliasing': r.get('aliasing_index', 0) > 0.5
                })

        # File format: subjects array
        elif 'subjects' in r:
            for subject in r['subjects']:
                rate = subject.get('sampling_rate', 'unknown')
                if rate in rate_data:
                    rate_data[rate].append({
                        'final': subject.get('final_drift', 0),
                        'cumulative': subject.get('cumulative_drift', 0),
                        'checkpoints': subject.get('checkpoint_interval', 0),
                        'peak': subject.get('peak_drift', 0),
                        'aliasing': subject.get('aliasing_detected', False)
                    })

    # If no data from passed results, load directly from canonical files as fallback
    if not any(rate_data.values()):
        print("  Loading from canonical nyquist files (fallback)...")
        nyquist_files = list(CANONICAL_RESULTS_DIR.glob("S7_run_018_nyquist_*.json"))
        for f in nyquist_files:
            try:
                with open(f, 'r', encoding='utf-8') as fp:
                    data = json.load(fp)
                    if 'subjects' in data:
                        for subject in data['subjects']:
                            rate = subject.get('sampling_rate', 'unknown')
                            if rate in rate_data:
                                rate_data[rate].append({
                                    'final': subject.get('final_drift', 0),
                                    'cumulative': subject.get('cumulative_drift', 0),
                                    'checkpoints': subject.get('checkpoint_interval', 0),
                                    'peak': subject.get('peak_drift', 0),
                                    'aliasing': subject.get('aliasing_detected', False)
                                })
            except Exception as e:
                print(f"  Warning: Could not load {f.name}: {e}")

    total = sum(len(v) for v in rate_data.values())
    print(f"  Loaded {total} entries: high={len(rate_data['high'])}, low={len(rate_data['low'])}, none={len(rate_data['none'])}")

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
    """Visualize identity gravity dynamics results.

    The manifest contains pre-fitted parameters: gamma, lambda, omega, r_squared.
    These are derived from the damped oscillator model fit during experiment execution.
    """
    if not results:
        print("No gravity results found")
        return

    print(f"\n=== 018d: Identity Gravity Dynamics ({len(results)} entries) ===")

    # Collect fitted parameters from manifest data
    # Manifest has: drift, max_drift, gamma, lambda, omega, r_squared
    model_params = []  # List of {model, drift, gamma, lambda, omega, r_squared}

    for r in results:
        # Manifest format - contains pre-fitted parameters
        if '_source' in r and r['_source'] == 'manifest':
            model = r.get('model', 'unknown')
            drift = r.get('drift', 0)
            gamma = r.get('gamma', None)
            lam = r.get('lambda', None)
            omega = r.get('omega', None)
            r_sq = r.get('r_squared', None)

            # Only include entries with valid fitted parameters
            if gamma is not None and lam is not None and omega is not None:
                model_params.append({
                    'model': model,
                    'drift': drift,
                    'gamma': gamma,
                    'lambda': lam,
                    'omega': omega,
                    'r_squared': r_sq if r_sq is not None else 0
                })

    print(f"  Found {len(model_params)} entries with fitted parameters")

    if not model_params:
        print("No gravity parameter data found in manifest")
        print("  (Manifest should contain gamma, lambda, omega fields)")
        return

    # Categorize into high/low gravity based on gamma (damping strength)
    all_gammas = [p['gamma'] for p in model_params if p['gamma'] > 0]
    median_gamma = np.median(all_gammas) if all_gammas else 0.5

    high_gravity = [p for p in model_params if p['gamma'] >= median_gamma]
    low_gravity = [p for p in model_params if p['gamma'] < median_gamma]

    print(f"  High gravity (gamma>={median_gamma:.2f}): {len(high_gravity)} entries")
    print(f"  Low gravity (gamma<{median_gamma:.2f}): {len(low_gravity)} entries")

    # Figure: Gravity dynamics using manifest fitted parameters
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    colors = {'high': '#2ecc71', 'low': '#e74c3c'}  # Green=high gravity (strong), Red=low gravity (weak)

    # Plot 1: Gamma (γ) distribution by model - horizontal bar chart
    ax1 = axes[0, 0]
    # Group by model
    model_gammas = {}
    for p in model_params:
        model = p['model']
        if model not in model_gammas:
            model_gammas[model] = []
        model_gammas[model].append(p['gamma'])

    # Calculate means and sort
    model_means = [(m, np.mean(gs), np.std(gs) if len(gs) > 1 else 0)
                   for m, gs in model_gammas.items()]
    model_means.sort(key=lambda x: x[1], reverse=True)

    # Plot top 20 models
    top_models = model_means[:20]
    models = [m[0][:25] for m in top_models]
    means = [m[1] for m in top_models]
    stds = [m[2] for m in top_models]
    bar_colors = ['#2ecc71' if m >= median_gamma else '#e74c3c' for m in means]

    y_pos = np.arange(len(models))
    ax1.barh(y_pos, means, xerr=stds, color=bar_colors, alpha=0.8, capsize=3)
    ax1.axvline(x=median_gamma, color='gray', linestyle='--', alpha=0.5, label=f'Median γ={median_gamma:.2f}')
    ax1.set_yticks(y_pos)
    ax1.set_yticklabels(models, fontsize=8)
    ax1.set_xlabel('Gamma (γ) - Identity Gravity Strength')
    ax1.set_title('Top 20 Models by Gravity Strength')
    ax1.legend(loc='lower right')
    ax1.invert_yaxis()

    # Plot 2: Lambda (λ) vs Omega (ω) scatter plot
    ax2 = axes[0, 1]
    lambdas = [p['lambda'] for p in model_params]
    omegas = [p['omega'] for p in model_params]
    gammas = [p['gamma'] for p in model_params]

    scatter = ax2.scatter(lambdas, omegas, c=gammas, cmap='RdYlGn', alpha=0.7, s=50)
    ax2.set_xlabel('Lambda (λ) - Damping Rate')
    ax2.set_ylabel('Omega (ω) - Oscillation Frequency')
    ax2.set_title('Damped Oscillator Parameter Space')
    cbar = plt.colorbar(scatter, ax=ax2)
    cbar.set_label('Gamma (γ)')

    # Plot 3: Gamma distribution histogram
    ax3 = axes[1, 0]
    high_gammas = [p['gamma'] for p in high_gravity]
    low_gammas = [p['gamma'] for p in low_gravity]

    ax3.hist(low_gammas, bins=15, alpha=0.7, label=f'Low Gravity (N={len(low_gammas)})',
             color=colors['low'], edgecolor='black')
    ax3.hist(high_gammas, bins=15, alpha=0.7, label=f'High Gravity (N={len(high_gammas)})',
             color=colors['high'], edgecolor='black')
    ax3.axvline(x=median_gamma, color='gray', linestyle='--', linewidth=2)
    ax3.set_xlabel('Gamma (γ)')
    ax3.set_ylabel('Count')
    ax3.set_title('Distribution of Identity Gravity Strength')
    ax3.legend()

    # Plot 4: Drift vs Gamma correlation
    ax4 = axes[1, 1]
    drifts = [p['drift'] for p in model_params]
    gammas = [p['gamma'] for p in model_params]

    ax4.scatter(gammas, drifts, alpha=0.6, c=['#2ecc71' if g >= median_gamma else '#e74c3c' for g in gammas])
    ax4.axhline(y=1.23, color='red', linestyle='--', alpha=0.3, label='Event Horizon')
    ax4.axvline(x=median_gamma, color='gray', linestyle='--', alpha=0.3)

    # Add correlation
    if len(gammas) > 2:
        corr = np.corrcoef(gammas, drifts)[0, 1]
        ax4.text(0.05, 0.95, f'r = {corr:.3f}', transform=ax4.transAxes, fontsize=10,
                 verticalalignment='top', bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    ax4.set_xlabel('Gamma (γ) - Gravity Strength')
    ax4.set_ylabel('Final Drift (PFI)')
    ax4.set_title('Gravity Strength vs Final Drift')
    ax4.legend(loc='upper right')

    plt.suptitle("Run 018d: Identity Gravity Dynamics", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run018d_gravity_dynamics.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    print(f"Saved: {outfile}")

    # Also save PDF
    pdf_path = PICS_DIR / "run018d_gravity_dynamics.pdf"
    plt.savefig(pdf_path, bbox_inches='tight')
    print(f"Saved: {pdf_path}")
    plt.close()

    # Print summary
    print(f"\nGravity Dynamics Summary:")
    print(f"  Total entries: {len(model_params)}")
    print(f"  Median gamma: {median_gamma:.3f}")
    print(f"  Mean lambda: {np.mean(lambdas):.3f}")
    print(f"  Mean omega: {np.mean(omegas):.3f}")
    print(f"  High gravity models: {len(high_gravity)}")
    print(f"  Low gravity models: {len(low_gravity)}")


# =============================================================================
# EXPORTED FUNCTIONS (for master visualizer integration)
# =============================================================================
# 018e: Model Breakdown Analysis (NEW)
# =============================================================================

def visualize_model_breakdown(all_data: Dict[str, List[Dict]]):
    """Visualize drift statistics for all 62 models tested in Run 018.

    Creates:
    - run018e_model_breakdown.png: Horizontal bar chart of all models by drift
    - run018e_model_table.md: Markdown table for publication
    """
    print("\n=== 018e: Model Breakdown Analysis ===")

    # Aggregate data across all experiments
    model_stats = {}  # model -> {'drifts': [], 'max_drifts': [], 'experiments': set()}

    for exp_name, results in all_data.items():
        if exp_name == 'architecture':
            continue  # Handle separately

        for r in results:
            model = r.get('model', 'unknown')
            drift = r.get('drift', 0)
            max_drift = r.get('peak_drift', 0)

            if model not in model_stats:
                model_stats[model] = {'drifts': [], 'max_drifts': [], 'experiments': set()}

            if drift > 0:
                model_stats[model]['drifts'].append(drift)
            if max_drift > 0:
                model_stats[model]['max_drifts'].append(max_drift)
            model_stats[model]['experiments'].add(exp_name)

    if not model_stats:
        print("No model data found")
        return

    # Calculate statistics for each model
    model_summary = []
    for model, stats in sorted(model_stats.items()):
        if stats['drifts']:
            mean_drift = np.mean(stats['drifts'])
            std_drift = np.std(stats['drifts']) if len(stats['drifts']) > 1 else 0
            n = len(stats['drifts'])
            mean_max = np.mean(stats['max_drifts']) if stats['max_drifts'] else 0
            model_summary.append({
                'model': model,
                'mean_drift': mean_drift,
                'std_drift': std_drift,
                'mean_max_drift': mean_max,
                'n': n,
                'experiments': len(stats['experiments'])
            })

    # Sort by mean drift
    model_summary.sort(key=lambda x: x['mean_drift'], reverse=True)

    print(f"Found {len(model_summary)} models with data")

    # Create visualization
    fig, ax = plt.subplots(figsize=(12, max(8, len(model_summary) * 0.25)))

    models = [m['model'][:30] for m in model_summary]  # Truncate long names
    drifts = [m['mean_drift'] for m in model_summary]
    errors = [m['std_drift'] for m in model_summary]

    # Color by provider family
    colors = []
    for m in model_summary:
        name = m['model'].lower()
        if 'claude' in name or 'anthropic' in name:
            colors.append('#8B4513')  # Brown for Anthropic
        elif 'gpt' in name or 'openai' in name:
            colors.append('#10A37F')  # Green for OpenAI
        elif 'gemini' in name or 'google' in name:
            colors.append('#4285F4')  # Blue for Google
        elif 'grok' in name or 'xai' in name:
            colors.append('#000000')  # Black for xAI
        elif 'llama' in name or 'meta' in name:
            colors.append('#0668E1')  # Meta blue
        elif 'mistral' in name or 'mixtral' in name:
            colors.append('#FF7000')  # Orange for Mistral
        elif 'qwen' in name:
            colors.append('#6E4AE2')  # Purple for Qwen
        elif 'deepseek' in name:
            colors.append('#00D4AA')  # Teal for DeepSeek
        elif 'kimi' in name:
            colors.append('#FF69B4')  # Pink for Kimi
        elif 'nemotron' in name or 'nvidia' in name:
            colors.append('#76B900')  # Nvidia green
        else:
            colors.append('#888888')  # Gray for unknown

    y_pos = np.arange(len(models))
    ax.barh(y_pos, drifts, xerr=errors, color=colors, alpha=0.8, capsize=3)
    ax.set_yticks(y_pos)
    ax.set_yticklabels(models, fontsize=8)
    ax.set_xlabel('Mean Drift (PFI)')
    ax.set_title(f'Run 018: Drift by Model (N={len(model_summary)} models)')
    ax.axvline(x=1.23, color='red', linestyle='--', label='Event Horizon (D=1.23)')
    ax.legend(loc='lower right')

    plt.tight_layout()
    output_path = PICS_DIR / "run018e_model_breakdown.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"Saved: {output_path}")

    # Also save PDF
    pdf_path = PICS_DIR / "run018e_model_breakdown.pdf"
    fig, ax = plt.subplots(figsize=(12, max(8, len(model_summary) * 0.25)))
    ax.barh(y_pos, drifts, xerr=errors, color=colors, alpha=0.8, capsize=3)
    ax.set_yticks(y_pos)
    ax.set_yticklabels(models, fontsize=8)
    ax.set_xlabel('Mean Drift (PFI)')
    ax.set_title(f'Run 018: Drift by Model (N={len(model_summary)} models)')
    ax.axvline(x=1.23, color='red', linestyle='--', label='Event Horizon (D=1.23)')
    ax.legend(loc='lower right')
    plt.tight_layout()
    plt.savefig(pdf_path, bbox_inches='tight')
    plt.close()
    print(f"Saved: {pdf_path}")

    # Note: Model statistics are stored in the manifest, not a separate markdown file
    # See RUN_018_DRIFT_MANIFEST.json for complete model statistics

    return model_summary


# =============================================================================
# 018f: Provider Family Variance Analysis (NEW)
# =============================================================================

def visualize_provider_variance(all_data: Dict[str, List[Dict]]):
    """Analyze variance breakdown by provider family.

    Creates:
    - run018f_provider_variance.png: Box plots of drift by provider family
    - run018f_variance_table.md: σ² breakdown for publication
    """
    print("\n=== 018f: Provider Family Variance Analysis ===")

    # Map models to provider families
    def get_provider_family(model_name: str) -> str:
        name = model_name.lower()
        if 'claude' in name or 'anthropic' in name:
            return 'Anthropic'
        elif 'gpt' in name or 'openai' in name:
            return 'OpenAI'
        elif 'gemini' in name or 'google' in name:
            return 'Google'
        elif 'grok' in name or 'xai' in name:
            return 'xAI'
        elif 'llama' in name or 'meta' in name:
            return 'Meta/Llama'
        elif 'mistral' in name or 'mixtral' in name:
            return 'Mistral'
        elif 'qwen' in name:
            return 'Qwen'
        elif 'deepseek' in name:
            return 'DeepSeek'
        elif 'kimi' in name:
            return 'Kimi'
        elif 'nemotron' in name or 'nvidia' in name:
            return 'NVIDIA'
        else:
            return 'Other'

    # Aggregate drifts by provider family
    provider_drifts = {}  # provider -> [drifts]

    for exp_name, results in all_data.items():
        for r in results:
            # Handle architecture data differently (has 'subjects' array in file format)
            if exp_name == 'architecture' and 'subjects' in r:
                for subject in r.get('subjects', []):
                    raw_provider = subject.get('provider', subject.get('model', 'unknown'))
                    peak_drift = subject.get('peak_drift', 0)

                    # Skip invalid/corrupted data
                    if peak_drift <= 0 or peak_drift > MAX_VALID_DRIFT:
                        continue

                    provider = get_provider_family(raw_provider)
                    if provider not in provider_drifts:
                        provider_drifts[provider] = []
                    provider_drifts[provider].append(peak_drift)
            else:
                # Standard manifest format
                model = r.get('model', 'unknown')
                drift = r.get('drift', 0)

                if drift <= 0:
                    continue

                provider = get_provider_family(model)
                if provider not in provider_drifts:
                    provider_drifts[provider] = []
                provider_drifts[provider].append(drift)

    if not provider_drifts:
        print("No provider data found")
        return

    # Calculate statistics
    provider_stats = []
    for provider, drifts in sorted(provider_drifts.items()):
        if len(drifts) >= 2:
            variance = np.var(drifts)
            mean = np.mean(drifts)
            std = np.std(drifts)
            n = len(drifts)
            provider_stats.append({
                'provider': provider,
                'variance': variance,
                'mean': mean,
                'std': std,
                'n': n,
                'drifts': drifts
            })

    # Sort by sample size
    provider_stats.sort(key=lambda x: x['n'], reverse=True)

    print(f"Found {len(provider_stats)} provider families with sufficient data")
    for ps in provider_stats:
        print(f"  - {ps['provider']}: n={ps['n']}, mean={ps['mean']:.3f}")

    # Calculate overall variance for comparison
    all_drifts = []
    for p in provider_stats:
        all_drifts.extend(p['drifts'])
    overall_variance = np.var(all_drifts)

    print(f"Overall variance: sigma^2 = {overall_variance:.6f}")

    # Create box plot
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    # Box plot
    providers = [p['provider'] for p in provider_stats]
    data = [p['drifts'] for p in provider_stats]

    bp = ax1.boxplot(data, labels=providers, patch_artist=True)

    # Color boxes
    colors = ['#8B4513', '#10A37F', '#4285F4', '#000000', '#0668E1',
              '#FF7000', '#6E4AE2', '#00D4AA', '#FF69B4', '#76B900', '#888888']
    for patch, color in zip(bp['boxes'], colors[:len(bp['boxes'])]):
        patch.set_facecolor(color)
        patch.set_alpha(0.6)

    ax1.axhline(y=1.23, color='red', linestyle='--', label='Event Horizon')
    ax1.set_ylabel('Drift (PFI)')
    ax1.set_xlabel('Provider Family')
    ax1.set_title('Drift Distribution by Provider Family')
    ax1.set_xticklabels(providers, rotation=45, ha='right')
    ax1.legend()

    # Variance bar chart
    variances = [p['variance'] for p in provider_stats]
    colors_bar = colors[:len(provider_stats)]
    ax2.bar(providers, variances, color=colors_bar, alpha=0.7)
    ax2.axhline(y=overall_variance, color='red', linestyle='--',
                label=f'Overall σ²={overall_variance:.5f}')
    ax2.set_ylabel('Variance (σ²)')
    ax2.set_xlabel('Provider Family')
    ax2.set_title('Within-Provider Variance')
    ax2.set_xticklabels(providers, rotation=45, ha='right')
    ax2.legend()

    plt.tight_layout()
    plt.subplots_adjust(bottom=0.15)  # Extra space for rotated labels
    output_path = PICS_DIR / "run018f_provider_variance.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"Saved: {output_path}")

    # Also save PDF
    pdf_path = PICS_DIR / "run018f_provider_variance.pdf"
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    bp = ax1.boxplot(data, labels=providers, patch_artist=True)
    for patch, color in zip(bp['boxes'], colors[:len(bp['boxes'])]):
        patch.set_facecolor(color)
        patch.set_alpha(0.6)
    ax1.axhline(y=1.23, color='red', linestyle='--', label='Event Horizon')
    ax1.set_ylabel('Drift (PFI)')
    ax1.set_xlabel('Provider Family')
    ax1.set_title('Drift Distribution by Provider Family')
    ax1.set_xticklabels(providers, rotation=45, ha='right')
    ax1.legend()
    ax2.bar(providers, variances, color=colors_bar, alpha=0.7)
    ax2.axhline(y=overall_variance, color='red', linestyle='--',
                label=f'Overall σ²={overall_variance:.5f}')
    ax2.set_ylabel('Variance (σ²)')
    ax2.set_xlabel('Provider Family')
    ax2.set_title('Within-Provider Variance')
    ax2.set_xticklabels(providers, rotation=45, ha='right')
    ax2.legend()
    plt.tight_layout()
    plt.subplots_adjust(bottom=0.15)
    plt.savefig(pdf_path, bbox_inches='tight')
    plt.close()
    print(f"Saved: {pdf_path}")

    # Note: Variance statistics are stored in the manifest, not a separate markdown file
    # See RUN_018_DRIFT_MANIFEST.json for complete provider variance data

    return provider_stats


# =============================================================================

def get_run018_data() -> Dict[str, List[Dict]]:
    """Load all Run 018 data, organized by experiment type.

    Data sources:
        - threshold, nyquist, gravity: From consolidated manifest (IRON CLAD data)
        - architecture: From local results directory (run018a_architecture_*.json)

    Returns:
        Dict with keys: 'threshold', 'architecture', 'nyquist', 'gravity'
        Each value is a list of result dictionaries.
    """
    # Load manifest for threshold/nyquist/gravity data
    manifest = load_from_manifest("018")

    data = {
        'threshold': [],
        'architecture': load_results("run018a_architecture_*.json"),
        'nyquist': [],
        'gravity': [],
    }

    if manifest:
        data['threshold'] = get_manifest_experiment_data(manifest, 'threshold')
        data['nyquist'] = get_manifest_experiment_data(manifest, 'nyquist')
        data['gravity'] = get_manifest_experiment_data(manifest, 'gravity')

        print(f"Loaded from manifest: threshold={len(data['threshold'])}, "
              f"nyquist={len(data['nyquist'])}, gravity={len(data['gravity'])}")
    else:
        # Fallback to local files if manifest not available
        data['threshold'] = load_results("run018a_threshold_*.json")
        data['nyquist'] = load_results("run018c_nyquist_*.json")
        data['gravity'] = load_results("run018d_gravity_*.json")
        print("Loaded from local files (manifest not found)")

    print(f"Loaded from local: architecture={len(data['architecture'])}")

    return data


def generate_all_run018_visualizations(experiment: str = 'all') -> None:
    """Generate Run 018 visualizations.

    This is the main entry point for the master visualize_armada.py script.

    Args:
        experiment: Which experiment to visualize ('threshold', 'architecture',
                   'nyquist', 'gravity', 'model_breakdown', 'provider_variance', or 'all')
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

    if experiment in ['model_breakdown', 'all']:
        visualize_model_breakdown(data)

    if experiment in ['provider_variance', 'all']:
        visualize_provider_variance(data)

    print("\n" + "=" * 60)
    print("Visualization complete!")
    print("=" * 60)


# =============================================================================
# Main
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Visualize Run 018 results")
    parser.add_argument("--experiment", "-e",
                        choices=VISUALIZATION_TYPES,
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

    # Use the consolidated data loader which reads from manifest
    generate_all_run018_visualizations(args.experiment)


if __name__ == "__main__":
    main()
