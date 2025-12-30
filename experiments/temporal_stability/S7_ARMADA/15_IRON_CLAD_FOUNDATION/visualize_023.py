"""
S7 RUN 023: UNIFIED VISUALIZATION GENERATOR (Cosine Era)
=========================================================
Consolidated visualizer for IRON CLAD Foundation data (run023 + run023_extended).

MODES:
    --mode simple        Quick charts: histogram, experiment, provider, volatility
    --mode comprehensive Full suite: stability basin, metrics, rescue, settling, dashboards
    --mode all           (Default) Generate everything

DATA SOURCES:
    --data foundation    S7_run_023_CURRENT.json (default)
    --data extended      S7_run_023_extended_CURRENT.json

USAGE:
    python visualize_023.py                    # All charts, foundation data
    python visualize_023.py --mode simple      # Quick charts only
    python visualize_023.py --data extended    # Extended settling data
    python visualize_023.py --folder 3_Stability  # Specific folder only

OUTPUT:
    results/pics/                        - Local simple charts
    ../visualizations/pics/{folder}/     - Comprehensive suite by category

METHODOLOGY:
    Uses COSINE DISTANCE drift values (EH=0.80, calibrated from run023)
    NOT the legacy keyword RMS (EH=1.23)

Author: Claude (VALIS Network)
Date: December 2025
"""

import os
import sys
import json
import argparse
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from typing import Optional, List, Dict, Tuple

# =============================================================================
# PATHS
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
LOCAL_OUTPUT_DIR = RESULTS_DIR / "pics"
VIZ_DIR = ARMADA_DIR / "visualizations"
COMPREHENSIVE_OUTPUT_DIR = VIZ_DIR / "pics"

# Data files
DATA_FILES = {
    "foundation": RESULTS_DIR / "S7_run_023_CURRENT.json",
    "extended": RESULTS_DIR / "S7_run_023_extended_CURRENT.json",
}

# =============================================================================
# CONSTANTS
# =============================================================================

# Cosine Event Horizon (calibrated 2025-12-20)
EVENT_HORIZON = 0.80
THRESHOLD_WARNING = 0.60
THRESHOLD_CATASTROPHIC = 1.20

# Provider colors
PROVIDER_COLORS = {
    "anthropic": "#7c3aed",  # Purple
    "openai": "#10a37f",     # Green
    "google": "#4285f4",     # Blue
    "xai": "#1a1a1a",        # Black
    "together": "#ff6b35",   # Orange
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
    "grok": "#1a1a1a",
    "meta-llama": "#FF6B6B",
    "mistralai": "#FFD93D",
    "deepseek": "#6BCB77",
    "Qwen": "#4D96FF",
    "moonshotai": "#9B59B6",
}

# Visualization folders (for comprehensive mode)
VIZ_FOLDERS = {
    "1_Vortex": "Drift spiral dynamics",
    "2_Boundary_Mapping": "Phase portraits + 3D basins",
    "3_Stability": "Pillar analysis + stability basins",
    "4_Rescue": "Recovery dynamics",
    "5_Settling": "Settling time curves",
    "6_Architecture": "Provider signatures",
    "8_Radar_Oscilloscope": "Radar + time-series drift views",
    "9_FFT_Spectral": "Frequency analysis",
    "10_PFI_Dimensional": "Conceptual explanations",
    "11_Unified_Dashboard": "Per-ship multi-panel dashboards",
    "12_Metrics_Summary": "Fleet-wide metrics comparison",
    "13_Model_Waveforms": "Per-model drift waveforms",
    "14_Ringback": "Ringback oscillation analysis",
    "15_Oobleck_Effect": "Prosecutor/Defense probing dynamics",
}

# =============================================================================
# DATA LOADING
# =============================================================================

def load_data(data_source: str = "foundation") -> dict:
    """Load run023 results JSON."""
    data_file = DATA_FILES.get(data_source)
    if not data_file:
        print(f"[ERROR] Unknown data source: {data_source}")
        print(f"  Available: {', '.join(DATA_FILES.keys())}")
        sys.exit(1)

    if not data_file.exists():
        print(f"[ERROR] Data file not found: {data_file}")
        print("  Run run023.py or run023_extended.py first to collect data.")
        sys.exit(1)

    print(f"[INFO] Loading: {data_file}")
    with open(data_file, 'r', encoding='utf-8') as f:
        data = json.load(f)

    print(f"[INFO] Loaded {len(data.get('results', []))} results")
    return data


def get_provider(model_name: str) -> str:
    """Extract provider from model name."""
    model_lower = model_name.lower()
    if "claude" in model_lower:
        return "claude"
    elif "gpt" in model_lower or "o1" in model_lower or "o3" in model_lower:
        return "gpt"
    elif "gemini" in model_lower:
        return "gemini"
    elif "grok" in model_lower:
        return "grok"
    elif "llama" in model_lower:
        return "meta-llama"
    elif "mistral" in model_lower or "mixtral" in model_lower:
        return "mistralai"
    elif "deepseek" in model_lower:
        return "deepseek"
    elif "qwen" in model_lower:
        return "Qwen"
    elif "kimi" in model_lower:
        return "moonshotai"
    return "other"


# =============================================================================
# SIMPLE MODE VISUALIZATIONS (from visualize_023b)
# =============================================================================

def generate_drift_distribution(results, output_dir):
    """Generate overall drift distribution histogram."""
    peak_drifts = [r['peak_drift'] for r in results if r.get('peak_drift')]

    if not peak_drifts:
        print("  [SKIP] No peak drift data found")
        return None

    fig, ax = plt.subplots(figsize=(12, 6))

    # Histogram
    bins = np.linspace(0, 1.0, 41)  # 0.025 bin width
    n, bins_out, patches = ax.hist(peak_drifts, bins=bins, edgecolor='white', alpha=0.7)

    # Color by zone
    for i, patch in enumerate(patches):
        bin_center = (bins_out[i] + bins_out[i+1]) / 2
        if bin_center >= EVENT_HORIZON:
            patch.set_facecolor('#ef4444')  # Red - VOLATILE
        elif bin_center >= THRESHOLD_WARNING:
            patch.set_facecolor('#f59e0b')  # Orange - WARNING
        else:
            patch.set_facecolor('#22c55e')  # Green - STABLE

    # Threshold lines
    ax.axvline(EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax.axvline(THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=2,
               label=f'Warning ({THRESHOLD_WARNING})')

    # Stats annotations
    mean = np.mean(peak_drifts)
    median = np.median(peak_drifts)
    p95 = np.percentile(peak_drifts, 95)

    ax.axvline(mean, color='blue', linestyle='-', linewidth=1.5, alpha=0.7,
               label=f'Mean ({mean:.3f})')
    ax.axvline(median, color='purple', linestyle='-', linewidth=1.5, alpha=0.7,
               label=f'Median ({median:.3f})')

    ax.set_xlabel('Peak Cosine Drift', fontsize=12)
    ax.set_ylabel('Count', fontsize=12)
    ax.set_title(f'Run 023: Cosine Drift Distribution (N={len(peak_drifts)})\n'
                 f'Mean={mean:.3f}, Median={median:.3f}, P95={p95:.3f}',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    output_path = output_dir / 'run023_drift_distribution.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")
    return output_path


def generate_by_experiment(results, output_dir):
    """Generate boxplot by experiment type."""
    by_exp = defaultdict(list)
    for r in results:
        if r.get('peak_drift'):
            by_exp[r.get('experiment', 'unknown')].append(r['peak_drift'])

    if not by_exp:
        print("  [SKIP] No experiment data found")
        return None

    exp_order = ['stability', 'boundary', 'event_horizon', 'recursive', 'rescue', 'settling']
    exp_data = [by_exp[e] for e in exp_order if e in by_exp]
    exp_labels = [e for e in exp_order if e in by_exp]

    if not exp_data:
        print("  [SKIP] No matching experiments found")
        return None

    fig, ax = plt.subplots(figsize=(12, 6))

    bp = ax.boxplot(exp_data, labels=exp_labels, patch_artist=True)

    # Color boxes
    colors = ['#22c55e', '#3b82f6', '#8b5cf6', '#ec4899', '#f59e0b', '#ef4444']
    for patch, color in zip(bp['boxes'], colors[:len(bp['boxes'])]):
        patch.set_facecolor(color)
        patch.set_alpha(0.6)

    # Threshold lines
    ax.axhline(EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax.axhline(THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5,
               label=f'Warning ({THRESHOLD_WARNING})')

    ax.set_xlabel('Experiment Type', fontsize=12)
    ax.set_ylabel('Peak Cosine Drift', fontsize=12)
    ax.set_title('Run 023: Drift by Experiment Type',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    output_path = output_dir / 'run023_by_experiment.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")
    return output_path


def generate_by_provider(results, output_dir):
    """Generate boxplot by provider."""
    by_provider = defaultdict(list)
    for r in results:
        if r.get('peak_drift'):
            provider = r.get('provider', get_provider(r.get('model', '')))
            by_provider[provider].append(r['peak_drift'])

    if not by_provider:
        print("  [SKIP] No provider data found")
        return None

    provider_order = ['anthropic', 'openai', 'google', 'xai', 'together']
    provider_data = [by_provider[p] for p in provider_order if p in by_provider]
    provider_labels = [p.upper() for p in provider_order if p in by_provider]
    provider_counts = [len(by_provider[p]) for p in provider_order if p in by_provider]
    provider_keys = [p for p in provider_order if p in by_provider]

    if not provider_data:
        print("  [SKIP] No matching providers found")
        return None

    fig, ax = plt.subplots(figsize=(12, 6))

    bp = ax.boxplot(provider_data, labels=[f'{l}\n(n={c})' for l, c in zip(provider_labels, provider_counts)],
                     patch_artist=True)

    # Color by provider
    for patch, provider in zip(bp['boxes'], provider_keys):
        patch.set_facecolor(PROVIDER_COLORS.get(provider, '#888888'))
        patch.set_alpha(0.6)

    # Threshold lines
    ax.axhline(EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax.axhline(THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5,
               label=f'Warning ({THRESHOLD_WARNING})')

    ax.set_xlabel('Provider', fontsize=12)
    ax.set_ylabel('Peak Cosine Drift', fontsize=12)
    ax.set_title('Run 023: Drift by Provider',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    output_path = output_dir / 'run023_by_provider.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")
    return output_path


def generate_volatility_counts(results, output_dir):
    """Generate bar chart of STABLE vs VOLATILE by provider."""
    by_provider = defaultdict(lambda: {'stable': 0, 'volatile': 0})

    for r in results:
        if r.get('peak_drift'):
            provider = r.get('provider', get_provider(r.get('model', '')))
            if r['peak_drift'] >= EVENT_HORIZON:
                by_provider[provider]['volatile'] += 1
            else:
                by_provider[provider]['stable'] += 1

    if not by_provider:
        print("  [SKIP] No provider data found")
        return None

    provider_order = ['anthropic', 'openai', 'google', 'xai', 'together']
    providers = [p for p in provider_order if p in by_provider]
    stable_counts = [by_provider[p]['stable'] for p in providers]
    volatile_counts = [by_provider[p]['volatile'] for p in providers]

    if not providers:
        print("  [SKIP] No matching providers found")
        return None

    fig, ax = plt.subplots(figsize=(12, 6))

    x = np.arange(len(providers))
    width = 0.35

    bars1 = ax.bar(x - width/2, stable_counts, width, label='STABLE', color='#22c55e', alpha=0.8)
    bars2 = ax.bar(x + width/2, volatile_counts, width, label='VOLATILE', color='#ef4444', alpha=0.8)

    ax.set_xlabel('Provider', fontsize=12)
    ax.set_ylabel('Count', fontsize=12)
    ax.set_title(f'Run 023: Stability Classification by Provider\n(Event Horizon = {EVENT_HORIZON})',
                 fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([p.upper() for p in providers])
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')

    # Add count labels on bars
    for bar in bars1:
        height = bar.get_height()
        ax.annotate(f'{int(height)}',
                    xy=(bar.get_x() + bar.get_width() / 2, height),
                    xytext=(0, 3), textcoords="offset points",
                    ha='center', va='bottom', fontsize=9)
    for bar in bars2:
        height = bar.get_height()
        if height > 0:
            ax.annotate(f'{int(height)}',
                        xy=(bar.get_x() + bar.get_width() / 2, height),
                        xytext=(0, 3), textcoords="offset points",
                        ha='center', va='bottom', fontsize=9)

    plt.tight_layout()
    output_path = output_dir / 'run023_volatility_counts.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"  Saved: {output_path.name}")
    return output_path


# =============================================================================
# COMPREHENSIVE MODE VISUALIZATIONS (from run023c_visualization_generator)
# =============================================================================

def generate_stability_basin(data: dict, output_dir: Path):
    """
    Generate stability basin visualization showing baseline vs peak drift.
    Output: 3_Stability/run023_stability_basin.png
    """
    print("\n[3_Stability] Generating stability basin...")

    results = data.get('results', [])

    # Group by model
    models = {}
    for result in results:
        model = result.get('model', 'unknown')
        if model not in models:
            models[model] = []
        models[model].append(result)

    fig, ax = plt.subplots(figsize=(14, 10))

    # Plot each model
    for model, model_results in models.items():
        provider = get_provider(model)
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Extract baseline and peak drifts
        baselines = []
        peaks = []
        for r in model_results:
            if 'baseline_drift' in r:
                baselines.append(r['baseline_drift'])
            elif 'probe_sequence' in r and r['probe_sequence']:
                baselines.append(r['probe_sequence'][0].get('drift', 0))

            if 'peak_drift' in r:
                peaks.append(r['peak_drift'])

        if baselines and peaks:
            mean_baseline = np.mean(baselines)
            mean_peak = np.mean(peaks)
            std_baseline = np.std(baselines)
            std_peak = np.std(peaks)

            ax.errorbar(mean_baseline, mean_peak,
                       xerr=std_baseline, yerr=std_peak,
                       marker='o', markersize=12,
                       color=color, alpha=0.7,
                       label=f"{model[:30]}...",
                       capsize=3)

    # Event Horizon lines
    ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon = {EVENT_HORIZON}')
    ax.axhline(y=THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5,
               alpha=0.7, label=f'Warning = {THRESHOLD_WARNING}')
    ax.axhline(y=THRESHOLD_CATASTROPHIC, color='darkred', linestyle=':', linewidth=1.5,
               alpha=0.7, label=f'Catastrophic = {THRESHOLD_CATASTROPHIC}')

    # Stability zones
    ax.axhspan(0, THRESHOLD_WARNING, alpha=0.1, color='green', label='STABLE zone')
    ax.axhspan(THRESHOLD_WARNING, EVENT_HORIZON, alpha=0.1, color='yellow')
    ax.axhspan(EVENT_HORIZON, THRESHOLD_CATASTROPHIC, alpha=0.1, color='orange')
    ax.axhspan(THRESHOLD_CATASTROPHIC, 2.0, alpha=0.1, color='red')

    ax.set_xlabel('Baseline Drift (Cosine Distance)', fontsize=12)
    ax.set_ylabel('Peak Drift (Cosine Distance)', fontsize=12)
    ax.set_title(f'Stability Basin: Run 023 ({len(models)} Ships)\n'
                 f'Event Horizon = {EVENT_HORIZON} (Cosine)', fontsize=14)
    ax.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_xlim(0, 1.0)
    ax.set_ylim(0, 1.5)

    plt.tight_layout()

    output_file = output_dir / "run023_stability_basin.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_metrics_summary(data: dict, output_dir: Path):
    """
    Generate fleet-wide metrics summary.
    Output: 12_Metrics_Summary/run023_metrics_summary.png
    """
    print("\n[12_Metrics_Summary] Generating metrics summary...")

    results = data.get('results', [])

    # Aggregate by model
    models = {}
    for result in results:
        model = result.get('model', 'unknown')
        if model not in models:
            models[model] = {
                'baseline_drifts': [],
                'peak_drifts': [],
                'final_drifts': [],
                'recovery_ratios': [],
            }

        if 'baseline_to_final_drift' in result and result['baseline_to_final_drift'] is not None:
            models[model]['baseline_drifts'].append(result['baseline_to_final_drift'])
        if 'peak_drift' in result and result['peak_drift'] is not None:
            models[model]['peak_drifts'].append(result['peak_drift'])
        if 'settled_drift' in result and result['settled_drift'] is not None:
            models[model]['final_drifts'].append(result['settled_drift'])

        peak = result.get('peak_drift', 0)
        settled = result.get('settled_drift', 0)
        if peak and peak > 0.01:
            recovery = max(0, 1 - (settled / peak))
            models[model]['recovery_ratios'].append(recovery)

    if not models:
        print("  [SKIP] No model data found")
        return None

    model_names = list(models.keys())
    metrics = ['Baseline\nDrift', 'Peak\nDrift', 'Final\nDrift', 'Recovery\nRatio']

    fig, ax = plt.subplots(figsize=(16, 8))

    x = np.arange(len(metrics))
    width = 0.8 / len(model_names)

    for i, model in enumerate(model_names):
        provider = get_provider(model)
        color = PROVIDER_COLORS.get(provider, '#888888')

        vals = [
            np.mean(models[model]['baseline_drifts']) if models[model]['baseline_drifts'] else 0,
            np.mean(models[model]['peak_drifts']) if models[model]['peak_drifts'] else 0,
            np.mean(models[model]['final_drifts']) if models[model]['final_drifts'] else 0,
            np.mean(models[model]['recovery_ratios']) if models[model]['recovery_ratios'] else 0,
        ]

        offset = (i - len(model_names)/2) * width + width/2
        short_name = model.split('/')[-1][:15]
        ax.bar(x + offset, vals, width, label=short_name, color=color, alpha=0.8)

    ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon = {EVENT_HORIZON}')

    ax.set_xticks(x)
    ax.set_xticklabels(metrics, fontsize=11)
    ax.set_ylabel('Value (Cosine Distance)', fontsize=12)
    ax.set_title(f'Run 023 Metrics Summary: Fleet Comparison\n'
                 f'Event Horizon = {EVENT_HORIZON} (Cosine) | {len(model_names)} Ships', fontsize=14)
    ax.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=7, ncol=2)
    ax.grid(True, alpha=0.3, axis='y')
    ax.set_ylim(0, 1.5)

    plt.tight_layout()

    output_file = output_dir / "run023_metrics_summary.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_rescue_dynamics(data: dict, output_dir: Path):
    """
    Generate rescue/recovery dynamics visualization.
    Output: 4_Rescue/rescue_dynamics.png
    """
    print("\n[4_Rescue] Generating rescue dynamics...")

    rescue_results = [r for r in data.get('results', []) if r.get('experiment') == 'rescue']

    if not rescue_results:
        print("  [SKIP] No rescue experiment data found")
        return None

    # Group by model
    models = {}
    for result in rescue_results:
        model = result.get('model', 'unknown')
        if model not in models:
            models[model] = []
        models[model].append(result)

    fig, axes = plt.subplots(1, 2, figsize=(16, 6))

    # Panel 1: Recovery ratio by model
    ax1 = axes[0]
    model_names = []
    recovery_means = []
    recovery_stds = []
    colors = []

    for model, results in models.items():
        recoveries = []
        for r in results:
            peak = r.get('peak_drift', 0)
            settled = r.get('settled_drift', r.get('final_drift', peak))
            if peak > 0.01:
                recovery = max(0, 1 - (settled / peak))
                recoveries.append(recovery)

        if recoveries:
            model_names.append(model.split('/')[-1][:15])
            recovery_means.append(np.mean(recoveries))
            recovery_stds.append(np.std(recoveries))
            colors.append(PROVIDER_COLORS.get(get_provider(model), '#888'))

    if model_names:
        x_pos = np.arange(len(model_names))
        bars = ax1.bar(x_pos, recovery_means, yerr=recovery_stds, capsize=3,
                      color=colors, alpha=0.8, edgecolor='black')

        ax1.axhline(y=0.8, color='green', linestyle='--', linewidth=2, label='Good Recovery (0.8)')
        ax1.axhline(y=0.5, color='orange', linestyle=':', linewidth=1.5, label='Marginal (0.5)')

        ax1.set_xticks(x_pos)
        ax1.set_xticklabels(model_names, rotation=45, ha='right', fontsize=8)
        ax1.set_ylabel('Recovery Ratio', fontsize=11)
        ax1.set_title('Recovery Ratio by Model (Rescue Experiment)', fontsize=12)
        ax1.legend(loc='upper right', fontsize=9)
        ax1.set_ylim(0, 1.2)
        ax1.grid(True, alpha=0.3, axis='y')

    # Panel 2: Peak vs Final drift
    ax2 = axes[1]

    for model, results in models.items():
        provider = get_provider(model)
        color = PROVIDER_COLORS.get(provider, '#888888')

        peaks = []
        finals = []
        for r in results:
            if 'peak_drift' in r:
                peaks.append(r['peak_drift'])
                finals.append(r.get('settled_drift', r.get('final_drift', r['peak_drift'])))

        if peaks and finals:
            ax2.scatter(peaks, finals, color=color, alpha=0.5, s=30,
                       label=f"{model.split('/')[-1][:12]}")

    ax2.plot([0, 1.5], [0, 1.5], 'k--', alpha=0.3, label='No Recovery')
    ax2.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, alpha=0.7)
    ax2.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, alpha=0.7)

    ax2.set_xlabel('Peak Drift (Cosine Distance)', fontsize=11)
    ax2.set_ylabel('Final Drift (Cosine Distance)', fontsize=11)
    ax2.set_title('Recovery Trajectory: Peak vs Final Drift', fontsize=12)
    ax2.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=7, ncol=2)
    ax2.set_xlim(0, 1.2)
    ax2.set_ylim(0, 1.2)
    ax2.grid(True, alpha=0.3)

    plt.suptitle(f'Rescue Protocol Dynamics: Run 023\n'
                f'{len(rescue_results)} Results | EH={EVENT_HORIZON}', fontsize=14)
    plt.tight_layout(rect=[0, 0, 1, 0.93])

    output_file = output_dir / "rescue_dynamics.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_settling_curves(data: dict, output_dir: Path):
    """
    Generate settling time curve visualization.
    Output: 5_Settling/settling_curves.png
    """
    print("\n[5_Settling] Generating settling curves...")

    settling_results = [r for r in data.get('results', []) if r.get('experiment') == 'settling']

    if not settling_results:
        print("  [SKIP] No settling experiment data found")
        return None

    print(f"  Found {len(settling_results)} settling results")

    # Group by provider
    providers = {}
    for result in settling_results:
        model = result.get('model', 'unknown')
        provider = get_provider(model)
        if provider not in providers:
            providers[provider] = []
        providers[provider].append(result)

    fig = plt.figure(figsize=(18, 6))

    # Panel 1: Step Response
    ax1 = fig.add_subplot(1, 3, 1)

    for provider, results in providers.items():
        color = PROVIDER_COLORS.get(provider, '#888888')

        for i, result in enumerate(results[:5]):
            probe_seq = result.get('probe_sequence', [])
            if probe_seq:
                probe_nums = list(range(len(probe_seq)))
                drift_values = [p.get('drift', p.get('peak_drift', 0)) for p in probe_seq]

                if drift_values:
                    alpha = 0.3 if i > 0 else 0.8
                    label = provider if i == 0 else None
                    ax1.plot(probe_nums, drift_values, 'o-', color=color, alpha=alpha,
                            linewidth=1.5, markersize=4, label=label)

    ax1.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, label='EH=0.80')
    ax1.axhline(y=THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5, alpha=0.7)
    ax1.set_xlabel('Probe Number (Time)', fontsize=11)
    ax1.set_ylabel('Drift (Cosine Distance)', fontsize=11)
    ax1.set_title('Step Response: Drift Over Probe Sequence', fontsize=12)
    ax1.legend(loc='upper right', fontsize=8, ncol=2)
    ax1.grid(True, alpha=0.3)
    ax1.set_ylim(0, 1.2)

    # Panel 2: Settling Performance
    ax2 = fig.add_subplot(1, 3, 2)

    provider_names = []
    settling_means = []
    settling_stds = []
    colors = []

    for provider, results in providers.items():
        settling_metrics = []
        for r in results:
            peak = r.get('peak_drift', 0)
            settled = r.get('settled_drift', r.get('final_drift', r.get('baseline_to_final_drift', peak)))
            if peak > 0.01:
                settling_metrics.append(peak - settled)

        if settling_metrics:
            provider_names.append(provider)
            settling_means.append(np.mean(settling_metrics))
            settling_stds.append(np.std(settling_metrics))
            colors.append(PROVIDER_COLORS.get(provider, '#888'))

    if provider_names:
        x_pos = np.arange(len(provider_names))
        bars = ax2.bar(x_pos, settling_means, yerr=settling_stds, capsize=3,
                      color=colors, alpha=0.8, edgecolor='black')

        for bar, mean in zip(bars, settling_means):
            ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.01,
                    f'{mean:.3f}', ha='center', fontsize=8)

        ax2.set_xticks(x_pos)
        ax2.set_xticklabels(provider_names, rotation=45, ha='right', fontsize=10)
        ax2.set_ylabel('Drift Reduction (Peak - Settled)', fontsize=11)
        ax2.set_title('Settling Performance by Provider', fontsize=12)
        ax2.grid(True, alpha=0.3, axis='y')
        ax2.axhline(y=0, color='black', linewidth=0.5)

    # Panel 3: Peak vs Settled Trajectory
    ax3 = fig.add_subplot(1, 3, 3)

    provider_list = list(providers.keys())
    for idx, (provider, results) in enumerate(providers.items()):
        color = PROVIDER_COLORS.get(provider, '#888888')

        peaks = [r.get('peak_drift', 0) for r in results if 'peak_drift' in r]
        settleds = []
        for r in results:
            settled = r.get('settled_drift', r.get('final_drift', r.get('baseline_to_final_drift')))
            if settled is not None:
                settleds.append(settled)

        if peaks and settleds:
            mean_peak = np.mean(peaks)
            mean_settled = np.mean(settleds)

            y_pos = idx * 0.08 + 0.1

            ax3.annotate('', xy=(mean_settled, y_pos),
                        xytext=(mean_peak, y_pos),
                        arrowprops=dict(arrowstyle='->', color=color, lw=2.5))

            ax3.scatter([mean_peak], [y_pos], color=color, s=120, marker='o',
                       edgecolors='black', linewidths=1, zorder=5)
            ax3.scatter([mean_settled], [y_pos], color=color, s=120, marker='s',
                       edgecolors='black', linewidths=1, zorder=5)

            ax3.text(0.02, y_pos, provider, fontsize=9, va='center', fontweight='bold')

    ax3.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, label='EH=0.80')
    ax3.axvline(x=THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5, label='Warning=0.60')

    ax3.set_xlabel('Drift (Cosine Distance)', fontsize=11)
    ax3.set_ylabel('Provider', fontsize=11)
    ax3.set_title('Settling Trajectory: Peak (o) -> Settled ([])', fontsize=12)
    ax3.set_xlim(0, 1.1)
    ax3.set_ylim(0, len(provider_list) * 0.08 + 0.15)
    ax3.set_yticks([])
    ax3.legend(loc='upper right', fontsize=9)
    ax3.grid(True, alpha=0.3, axis='x')

    plt.suptitle(f'Settling Time Analysis: Run 023\n'
                f'{len(settling_results)} Results | EH={EVENT_HORIZON}', fontsize=14, fontweight='bold')
    plt.tight_layout(rect=[0, 0, 1, 0.93])

    output_file = output_dir / "settling_curves.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_provider_comparison(data: dict, output_dir: Path):
    """
    Generate provider comparison bar chart.
    Output: 6_Architecture/provider_comparison.png
    """
    print("\n[6_Architecture] Generating provider comparison...")

    results = data.get('results', [])

    # Group by provider
    providers = {}
    for result in results:
        model = result.get('model', 'unknown')
        provider = get_provider(model)
        if provider not in providers:
            providers[provider] = []
        if 'peak_drift' in result:
            providers[provider].append(result['peak_drift'])

    if not providers:
        print("  [SKIP] No provider data found")
        return None

    fig, ax = plt.subplots(figsize=(12, 6))

    provider_names = list(providers.keys())
    means = [np.mean(providers[p]) for p in provider_names]
    stds = [np.std(providers[p]) for p in provider_names]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in provider_names]

    bars = ax.bar(provider_names, means, yerr=stds, capsize=5,
                  color=colors, alpha=0.8, edgecolor='black')

    ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon = {EVENT_HORIZON}')

    for bar, mean in zip(bars, means):
        ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
                f'{mean:.3f}', ha='center', fontsize=10)

    ax.set_xlabel('Provider', fontsize=12)
    ax.set_ylabel('Mean Peak Drift (Cosine Distance)', fontsize=12)
    ax.set_title(f'Provider Comparison: Mean Peak Drift\n'
                 f'Run 023 ({len(set(r.get("model") for r in results))} Ships)', fontsize=14)
    ax.legend(loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')
    ax.set_ylim(0, 1.0)

    plt.tight_layout()

    output_file = output_dir / "provider_comparison.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# MAIN ORCHESTRATOR
# =============================================================================

def run_simple_mode(data: dict, output_dir: Path):
    """Generate simple quick charts."""
    print("\n" + "=" * 50)
    print("SIMPLE MODE: Quick Charts")
    print("=" * 50)

    results = data.get('results', [])
    generated = []

    output_dir.mkdir(parents=True, exist_ok=True)

    viz = generate_drift_distribution(results, output_dir)
    if viz:
        generated.append(viz)

    viz = generate_by_experiment(results, output_dir)
    if viz:
        generated.append(viz)

    viz = generate_by_provider(results, output_dir)
    if viz:
        generated.append(viz)

    viz = generate_volatility_counts(results, output_dir)
    if viz:
        generated.append(viz)

    return generated


def run_comprehensive_mode(data: dict, output_dir: Path, folder_filter: str = None):
    """Generate comprehensive visualization suite."""
    print("\n" + "=" * 50)
    print("COMPREHENSIVE MODE: Full Suite")
    print("=" * 50)

    generated = []

    if folder_filter:
        if folder_filter not in VIZ_FOLDERS:
            print(f"[ERROR] Unknown folder: {folder_filter}")
            print(f"  Available: {', '.join(VIZ_FOLDERS.keys())}")
            return []
        folders_to_generate = [folder_filter]
    else:
        folders_to_generate = list(VIZ_FOLDERS.keys())

    for folder in folders_to_generate:
        folder_path = output_dir / folder
        folder_path.mkdir(parents=True, exist_ok=True)

        if folder == "3_Stability":
            viz = generate_stability_basin(data, folder_path)
            if viz:
                generated.append(viz)

        elif folder == "4_Rescue":
            viz = generate_rescue_dynamics(data, folder_path)
            if viz:
                generated.append(viz)

        elif folder == "5_Settling":
            viz = generate_settling_curves(data, folder_path)
            if viz:
                generated.append(viz)

        elif folder == "6_Architecture":
            viz = generate_provider_comparison(data, folder_path)
            if viz:
                generated.append(viz)

        elif folder == "12_Metrics_Summary":
            viz = generate_metrics_summary(data, folder_path)
            if viz:
                generated.append(viz)

        else:
            print(f"\n[{folder}] Not yet implemented - placeholder")

    return generated


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description='Unified visualizer for Run 023 IRON CLAD Foundation data',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python visualize_023.py                       # All charts, foundation data
    python visualize_023.py --mode simple         # Quick charts only
    python visualize_023.py --mode comprehensive  # Full suite
    python visualize_023.py --data extended       # Extended settling data
    python visualize_023.py --folder 3_Stability  # Specific folder only
    python visualize_023.py --list                # List available folders
        """
    )
    parser.add_argument('--mode', choices=['simple', 'comprehensive', 'all'],
                        default='all', help='Visualization mode (default: all)')
    parser.add_argument('--data', choices=['foundation', 'extended'],
                        default='foundation', help='Data source (default: foundation)')
    parser.add_argument('--folder', type=str, help='Generate only specific folder (comprehensive mode)')
    parser.add_argument('--list', action='store_true', help='List available folders')
    args = parser.parse_args()

    print("=" * 70)
    print("RUN 023: UNIFIED VISUALIZATION GENERATOR (Cosine Era)")
    print("=" * 70)
    print(f"\nEvent Horizon: {EVENT_HORIZON} (Cosine Distance)")
    print(f"Warning: {THRESHOLD_WARNING}")
    print(f"Catastrophic: {THRESHOLD_CATASTROPHIC}")

    if args.list:
        print("\nAvailable visualization folders (comprehensive mode):")
        for folder, desc in VIZ_FOLDERS.items():
            print(f"  {folder}: {desc}")
        return 0

    # Load data
    data = load_data(args.data)

    generated = []

    # Run appropriate mode
    if args.mode in ['simple', 'all']:
        simple_output = LOCAL_OUTPUT_DIR
        simple_output.mkdir(parents=True, exist_ok=True)
        generated.extend(run_simple_mode(data, simple_output))

    if args.mode in ['comprehensive', 'all']:
        generated.extend(run_comprehensive_mode(data, COMPREHENSIVE_OUTPUT_DIR, args.folder))

    # Summary
    print("\n" + "=" * 70)
    print("GENERATION COMPLETE")
    print("=" * 70)
    print(f"\nGenerated {len(generated)} visualizations:")
    for viz in generated:
        print(f"  - {viz}")

    if args.mode in ['simple', 'all']:
        print(f"\nSimple charts: {LOCAL_OUTPUT_DIR}")
    if args.mode in ['comprehensive', 'all']:
        print(f"Comprehensive suite: {COMPREHENSIVE_OUTPUT_DIR}")

    return 0


if __name__ == '__main__':
    sys.exit(main())
