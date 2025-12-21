"""
S7 RUN 023c: VISUALIZATION GENERATOR (Cosine Era)
==================================================
Generates all visualizations from run023b data into the consolidated folder structure.

PURPOSE:
    run023b collected 4505 results (25 ships x 6 experiments x 30 iterations)
    This script generates visualizations from that data into:

    visualizations/pics/
        1_Vortex/           - Drift spiral dynamics
        2_Boundary_Mapping/ - Phase portraits + 3D basins
        3_Stability/        - Pillar analysis + stability basins
        4_Rescue/           - Recovery dynamics
        5_Settling/         - Settling time curves
        6_Architecture/     - Provider signatures
        7_Radar/            - PFI dimensional analysis
        8_Oscilloscope/     - Time-series drift views
        9_FFT_Spectral/     - Frequency analysis
        10_PFI_Dimensional/ - Conceptual explanations
        11_Unified_Dashboard/ - Per-ship multi-panel dashboards
        12_Metrics_Summary/ - Fleet-wide metrics comparison

METHODOLOGY:
    Uses COSINE DISTANCE drift values (EH=0.80, calibrated from run023b)
    NOT the legacy keyword RMS (EH=1.23)

USAGE:
    # Generate all visualizations
    python run023c_visualization_generator.py

    # Generate specific folder only
    python run023c_visualization_generator.py --folder 3_Stability

    # Pilot mode (test with 1 visualization per folder)
    python run023c_visualization_generator.py --pilot

Author: Claude (VALIS Network)
Date: December 20, 2025
"""

import os
import sys
import json
import subprocess
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from pathlib import Path
from datetime import datetime
from dataclasses import dataclass, asdict
from typing import Optional, List, Dict, Tuple

# Add parent paths for imports
sys.path.insert(0, str(Path(__file__).parent.parent))
sys.path.insert(0, str(Path(__file__).parent.parent / "visualizations"))

# =============================================================================
# PATHS
# =============================================================================

SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
VIZ_DIR = ARMADA_DIR / "visualizations"
OUTPUT_DIR = VIZ_DIR / "pics"

# Import constants from master visualizer
try:
    from visualize_armada import EVENT_HORIZON, PROVIDER_COLORS
except ImportError:
    # Fallback if import fails
    EVENT_HORIZON = 0.80
    PROVIDER_COLORS = {
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

# Thresholds (Cosine Distance - Calibrated 2025-12-20)
THRESHOLD_WARNING = 0.60
THRESHOLD_CATASTROPHIC = 1.20

# =============================================================================
# VISUALIZATION FOLDERS
# =============================================================================

VIZ_FOLDERS = {
    "1_Vortex": "Drift spiral dynamics",
    "2_Boundary_Mapping": "Phase portraits + 3D basins",
    "3_Stability": "Pillar analysis + stability basins",
    "4_Rescue": "Recovery dynamics",
    "5_Settling": "Settling time curves",
    "6_Architecture": "Provider signatures",
    "7_Radar": "PFI dimensional analysis",
    "8_Oscilloscope": "Time-series drift views",
    "9_FFT_Spectral": "Frequency analysis",
    "10_PFI_Dimensional": "Conceptual explanations",
    "11_Unified_Dashboard": "Per-ship multi-panel dashboards",
    "12_Metrics_Summary": "Fleet-wide metrics comparison",
}

# =============================================================================
# DATA LOADING
# =============================================================================

def load_run023b_data() -> dict:
    """Load the run023b results JSON."""
    data_file = RESULTS_DIR / "S7_run_023b_CURRENT.json"
    if not data_file.exists():
        print(f"[ERROR] Data file not found: {data_file}")
        print("  Run run023b_iron_clad_foundation.py first to collect data.")
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
# VISUALIZATION GENERATORS
# =============================================================================

def generate_stability_basin(data: dict, output_dir: Path):
    """
    Generate stability basin visualization showing baseline vs peak drift.
    Output: 3_Stability/run023b_stability_basin.png
    """
    print("\n[3_Stability] Generating stability basin...")

    # Group by model
    models = {}
    for result in data.get('results', []):
        model = result.get('model', 'unknown')
        if model not in models:
            models[model] = []
        models[model].append(result)

    fig, ax = plt.subplots(figsize=(14, 10))

    # Plot each model
    for model, results in models.items():
        provider = get_provider(model)
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Extract baseline and peak drifts
        baselines = []
        peaks = []
        for r in results:
            # Handle different data structures
            if 'baseline_drift' in r:
                baselines.append(r['baseline_drift'])
            elif 'probe_sequence' in r and r['probe_sequence']:
                baselines.append(r['probe_sequence'][0].get('drift', 0))

            if 'peak_drift' in r:
                peaks.append(r['peak_drift'])

        if baselines and peaks:
            # Plot mean point with error bars
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
    ax.set_title(f'Stability Basin: Run 023b (25 Ships, N=30)\n'
                 f'Event Horizon = {EVENT_HORIZON} (Cosine)', fontsize=14)
    ax.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_xlim(0, 1.0)
    ax.set_ylim(0, 1.5)

    plt.tight_layout()

    # Save
    output_file = output_dir / "run023b_stability_basin.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_metrics_summary(data: dict, output_dir: Path):
    """
    Generate fleet-wide metrics summary.
    Output: 12_Metrics_Summary/run023c_metrics_summary.png
    """
    print("\n[12_Metrics_Summary] Generating metrics summary...")

    # Aggregate by model
    models = {}
    for result in data.get('results', []):
        model = result.get('model', 'unknown')
        if model not in models:
            models[model] = {
                'baseline_drifts': [],
                'peak_drifts': [],
                'final_drifts': [],
                'recovery_ratios': [],
            }

        if 'baseline_drift' in result:
            models[model]['baseline_drifts'].append(result['baseline_drift'])
        if 'peak_drift' in result:
            models[model]['peak_drifts'].append(result['peak_drift'])
        if 'final_drift' in result:
            models[model]['final_drifts'].append(result['final_drift'])
        if 'recovery_ratio' in result:
            models[model]['recovery_ratios'].append(result['recovery_ratio'])

    # Prepare data for plotting
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
        short_name = model.split('/')[-1][:15]  # Shorten for display
        ax.bar(x + offset, vals, width, label=short_name, color=color, alpha=0.8)

    # Event Horizon reference
    ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon = {EVENT_HORIZON}')

    ax.set_xticks(x)
    ax.set_xticklabels(metrics, fontsize=11)
    ax.set_ylabel('Value (Cosine Distance)', fontsize=12)
    ax.set_title(f'Run 023c Metrics Summary: Fleet Comparison\n'
                 f'Event Horizon = {EVENT_HORIZON} (Cosine) | {len(model_names)} Ships', fontsize=14)
    ax.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=7, ncol=2)
    ax.grid(True, alpha=0.3, axis='y')
    ax.set_ylim(0, 1.5)

    plt.tight_layout()

    # Save
    output_file = output_dir / "run023c_metrics_summary.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_drift_histogram(data: dict, output_dir: Path):
    """
    Generate drift distribution histogram.
    Output: 3_Stability/run023b_drift_histogram.png
    """
    print("\n[3_Stability] Generating drift histogram...")

    # Collect all peak drifts
    peak_drifts = []
    for result in data.get('results', []):
        if 'peak_drift' in result:
            peak_drifts.append(result['peak_drift'])

    if not peak_drifts:
        print("  [SKIP] No peak drift data found")
        return None

    fig, ax = plt.subplots(figsize=(12, 6))

    # Histogram
    n, bins, patches = ax.hist(peak_drifts, bins=50, color='steelblue',
                               alpha=0.7, edgecolor='black')

    # Color bars by zone
    for i, (bin_start, patch) in enumerate(zip(bins[:-1], patches)):
        if bin_start < THRESHOLD_WARNING:
            patch.set_facecolor('green')
        elif bin_start < EVENT_HORIZON:
            patch.set_facecolor('yellow')
        elif bin_start < THRESHOLD_CATASTROPHIC:
            patch.set_facecolor('orange')
        else:
            patch.set_facecolor('red')
        patch.set_alpha(0.7)

    # Threshold lines
    ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon = {EVENT_HORIZON}')
    ax.axvline(x=THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5,
               label=f'Warning = {THRESHOLD_WARNING}')
    ax.axvline(x=THRESHOLD_CATASTROPHIC, color='darkred', linestyle=':', linewidth=1.5,
               label=f'Catastrophic = {THRESHOLD_CATASTROPHIC}')

    # Statistics
    mean_drift = np.mean(peak_drifts)
    p95 = np.percentile(peak_drifts, 95)
    ax.axvline(x=mean_drift, color='blue', linestyle='-', linewidth=2,
               label=f'Mean = {mean_drift:.3f}')
    ax.axvline(x=p95, color='purple', linestyle='-', linewidth=2,
               label=f'P95 = {p95:.3f}')

    ax.set_xlabel('Peak Drift (Cosine Distance)', fontsize=12)
    ax.set_ylabel('Count', fontsize=12)
    ax.set_title(f'Peak Drift Distribution: Run 023b (N={len(peak_drifts)})\n'
                 f'Mean={mean_drift:.3f}, P95={p95:.3f}, EH={EVENT_HORIZON}', fontsize=14)
    ax.legend(loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()

    # Save
    output_file = output_dir / "run023b_drift_histogram.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_unified_dashboard(data: dict, output_dir: Path, model_filter: str = None):
    """
    Generate per-ship unified dashboard (4-panel view).

    Panels:
    1. Drift trajectory over iterations (time series)
    2. Experiment type breakdown (stacked/grouped bars)
    3. Radar chart showing multi-dimensional stability metrics
    4. Summary metrics with pillar scores

    Output: 11_Unified_Dashboard/{ship}_unified_dashboard.png
    """
    print("\n[11_Unified_Dashboard] Generating unified dashboards...")

    # Group results by model
    models = {}
    for result in data.get('results', []):
        model = result.get('model', 'unknown')
        if model_filter and model_filter not in model:
            continue
        if model not in models:
            models[model] = {
                'stability': [], 'boundary': [], 'rescue': [],
                'settling': [], 'recursive': [], 'anchor': []
            }
        exp_type = result.get('experiment', 'unknown')
        if exp_type in models[model]:
            models[model][exp_type].append(result)

    if not models:
        print("  [SKIP] No model data found")
        return None

    generated = []

    for model, experiments in models.items():
        # Create 2x2 dashboard
        fig, axes = plt.subplots(2, 2, figsize=(16, 12))

        provider = get_provider(model)
        color = PROVIDER_COLORS.get(provider, '#888888')
        short_name = model.split('/')[-1] if '/' in model else model

        # Panel 1: Drift trajectory over iterations (top-left)
        ax1 = axes[0, 0]
        exp_colors = {
            'stability': '#2ecc71', 'boundary': '#3498db', 'rescue': '#e74c3c',
            'settling': '#9b59b6', 'recursive': '#f39c12', 'anchor': '#1abc9c'
        }

        for exp_type, results in experiments.items():
            if results:
                # Sort by iteration and extract peak drifts
                sorted_results = sorted(results, key=lambda x: x.get('iteration', 0))
                iterations = [r.get('iteration', i) for i, r in enumerate(sorted_results)]
                peak_drifts = [r.get('peak_drift', 0) for r in sorted_results]

                if peak_drifts:
                    ax1.plot(iterations, peak_drifts, 'o-',
                            color=exp_colors.get(exp_type, '#888'),
                            label=exp_type, alpha=0.7, markersize=4)

        ax1.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, label='EH=0.80')
        ax1.axhline(y=THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5, alpha=0.7)
        ax1.set_xlabel('Iteration', fontsize=10)
        ax1.set_ylabel('Peak Drift (Cosine)', fontsize=10)
        ax1.set_title('Drift Trajectory by Experiment Type', fontsize=11)
        ax1.legend(loc='upper right', fontsize=8, ncol=2)
        ax1.grid(True, alpha=0.3)
        ax1.set_ylim(0, 1.2)

        # Panel 2: Experiment breakdown (top-right)
        ax2 = axes[0, 1]
        exp_names = list(experiments.keys())
        exp_means = []
        exp_stds = []
        exp_counts = []
        bar_colors = []

        for exp_type in exp_names:
            results = experiments[exp_type]
            peaks = [r.get('peak_drift', 0) for r in results if 'peak_drift' in r]
            if peaks:
                exp_means.append(np.mean(peaks))
                exp_stds.append(np.std(peaks))
                exp_counts.append(len(peaks))
            else:
                exp_means.append(0)
                exp_stds.append(0)
                exp_counts.append(0)
            bar_colors.append(exp_colors.get(exp_type, '#888'))

        x_pos = np.arange(len(exp_names))
        bars = ax2.bar(x_pos, exp_means, yerr=exp_stds, capsize=3,
                      color=bar_colors, alpha=0.8, edgecolor='black')

        # Add count labels
        for i, (bar, count) in enumerate(zip(bars, exp_counts)):
            ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.03,
                    f'n={count}', ha='center', fontsize=8)

        ax2.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2)
        ax2.set_xticks(x_pos)
        ax2.set_xticklabels(exp_names, rotation=45, ha='right', fontsize=9)
        ax2.set_ylabel('Mean Peak Drift', fontsize=10)
        ax2.set_title('Performance by Experiment Type', fontsize=11)
        ax2.set_ylim(0, 1.2)
        ax2.grid(True, alpha=0.3, axis='y')

        # Panel 3: Radar chart (bottom-left)
        ax3 = axes[1, 0]

        # Calculate stability metrics for radar
        all_peaks = []
        all_recoveries = []
        all_baselines = []

        for results in experiments.values():
            for r in results:
                if 'peak_drift' in r:
                    all_peaks.append(r['peak_drift'])
                if 'recovery_ratio' in r:
                    all_recoveries.append(r['recovery_ratio'])
                if 'baseline_drift' in r:
                    all_baselines.append(r['baseline_drift'])

        # Radar dimensions (normalized 0-1, inverted for "good" metrics)
        radar_labels = ['Stability\n(1-peak)', 'Recovery', 'Baseline\nIntegrity',
                       'Consistency\n(1-std)', 'Sample\nSize']

        mean_peak = np.mean(all_peaks) if all_peaks else 0.5
        mean_recovery = np.mean(all_recoveries) if all_recoveries else 0.5
        mean_baseline = 1 - np.mean(all_baselines) if all_baselines else 0.5
        consistency = 1 - (np.std(all_peaks) if all_peaks else 0.5)
        sample_norm = min(len(all_peaks) / 180, 1.0)  # 180 = target per ship

        radar_values = [
            max(0, 1 - mean_peak),  # Inverted: lower drift = better
            mean_recovery,
            mean_baseline,
            max(0, consistency),
            sample_norm
        ]

        # Polar radar plot
        angles = np.linspace(0, 2*np.pi, len(radar_labels), endpoint=False).tolist()
        radar_values_closed = radar_values + [radar_values[0]]
        angles_closed = angles + [angles[0]]

        ax3.clear()
        ax3 = fig.add_subplot(2, 2, 3, projection='polar')
        ax3.plot(angles_closed, radar_values_closed, 'o-', color=color, linewidth=2)
        ax3.fill(angles_closed, radar_values_closed, color=color, alpha=0.25)
        ax3.set_xticks(angles)
        ax3.set_xticklabels(radar_labels, fontsize=9)
        ax3.set_ylim(0, 1)
        ax3.set_title('Stability Profile (Radar)', fontsize=11, pad=20)
        ax3.grid(True)

        # Panel 4: Summary metrics (bottom-right)
        ax4 = axes[1, 1]
        ax4.axis('off')

        # Calculate summary stats
        total_samples = len(all_peaks)
        above_eh = sum(1 for p in all_peaks if p >= EVENT_HORIZON)
        above_warning = sum(1 for p in all_peaks if p >= THRESHOLD_WARNING)

        summary_text = f"""
        SHIP: {short_name}
        Provider: {provider.upper()}

        SAMPLE SIZE
        Total Results: {total_samples}
        Per Experiment: {total_samples // 6 if total_samples > 0 else 0}

        DRIFT METRICS
        Mean Peak Drift: {mean_peak:.4f}
        Std Dev: {np.std(all_peaks):.4f}
        Min: {min(all_peaks) if all_peaks else 0:.4f}
        Max: {max(all_peaks) if all_peaks else 0:.4f}

        THRESHOLD VIOLATIONS
        Above Warning (0.60): {above_warning} ({100*above_warning/total_samples:.1f}%)
        Above Event Horizon: {above_eh} ({100*above_eh/total_samples:.1f}%)

        RECOVERY
        Mean Recovery Ratio: {mean_recovery:.4f}

        CLASSIFICATION: {'STABLE' if mean_peak < EVENT_HORIZON else 'VOLATILE'}
        """

        ax4.text(0.1, 0.95, summary_text, transform=ax4.transAxes,
                fontsize=10, verticalalignment='top', fontfamily='monospace',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

        # Overall title
        classification = 'STABLE' if mean_peak < EVENT_HORIZON else 'VOLATILE'
        fig.suptitle(f'Unified Dashboard: {short_name}\n'
                    f'Classification: {classification} | Mean Drift: {mean_peak:.3f} | EH: {EVENT_HORIZON}',
                    fontsize=14, fontweight='bold')

        plt.tight_layout(rect=[0, 0, 1, 0.95])

        # Save
        safe_name = short_name.replace('/', '_').replace(':', '_')
        output_file = output_dir / f"{safe_name}_unified_dashboard.png"
        plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
        plt.close()

        print(f"  Saved: {output_file}")
        generated.append(output_file)

    # Generate fleet comparison summary
    if len(models) > 1:
        print("  Generating fleet comparison...")
        fig, ax = plt.subplots(figsize=(16, 8))

        model_names = []
        model_means = []
        model_stds = []
        model_colors = []

        for model, experiments in models.items():
            all_peaks = []
            for results in experiments.values():
                for r in results:
                    if 'peak_drift' in r:
                        all_peaks.append(r['peak_drift'])

            if all_peaks:
                model_names.append(model.split('/')[-1][:20])
                model_means.append(np.mean(all_peaks))
                model_stds.append(np.std(all_peaks))
                model_colors.append(PROVIDER_COLORS.get(get_provider(model), '#888'))

        # Sort by mean drift
        sorted_idx = np.argsort(model_means)
        model_names = [model_names[i] for i in sorted_idx]
        model_means = [model_means[i] for i in sorted_idx]
        model_stds = [model_stds[i] for i in sorted_idx]
        model_colors = [model_colors[i] for i in sorted_idx]

        x_pos = np.arange(len(model_names))
        bars = ax.barh(x_pos, model_means, xerr=model_stds, capsize=3,
                      color=model_colors, alpha=0.8, edgecolor='black')

        ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, label='EH=0.80')
        ax.axvline(x=THRESHOLD_WARNING, color='orange', linestyle=':', linewidth=1.5, label='Warning=0.60')

        ax.set_yticks(x_pos)
        ax.set_yticklabels(model_names, fontsize=9)
        ax.set_xlabel('Mean Peak Drift (Cosine Distance)', fontsize=12)
        ax.set_title(f'Fleet Comparison: {len(model_names)} Ships Ranked by Stability\n'
                    f'Run 023b (N=30 per experiment)', fontsize=14)
        ax.legend(loc='lower right', fontsize=10)
        ax.grid(True, alpha=0.3, axis='x')
        ax.set_xlim(0, 1.0)

        plt.tight_layout()

        fleet_file = output_dir / "fleet_dimensional_comparison.png"
        plt.savefig(fleet_file, dpi=150, bbox_inches='tight', facecolor='white')
        plt.savefig(fleet_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
        plt.close()

        print(f"  Saved: {fleet_file}")
        generated.append(fleet_file)

    return generated


def generate_rescue_dynamics(data: dict, output_dir: Path):
    """
    Generate rescue/recovery dynamics visualization.
    Shows how models recover from drift perturbations.
    Output: 4_Rescue/rescue_dynamics.png
    """
    print("\n[4_Rescue] Generating rescue dynamics...")

    # Filter for rescue experiments
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
        # Calculate recovery ratio from available fields
        # recovery = 1 - (settled_drift / peak_drift) for peak > 0
        # Higher = better recovery (drift reduced more)
        recoveries = []
        for r in results:
            peak = r.get('peak_drift', 0)
            settled = r.get('settled_drift', r.get('final_drift', peak))
            if peak > 0.01:  # Avoid division by tiny values
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

        # Good recovery line
        ax1.axhline(y=0.8, color='green', linestyle='--', linewidth=2, label='Good Recovery (0.8)')
        ax1.axhline(y=0.5, color='orange', linestyle=':', linewidth=1.5, label='Marginal (0.5)')

        ax1.set_xticks(x_pos)
        ax1.set_xticklabels(model_names, rotation=45, ha='right', fontsize=8)
        ax1.set_ylabel('Recovery Ratio', fontsize=11)
        ax1.set_title('Recovery Ratio by Model (Rescue Experiment)', fontsize=12)
        ax1.legend(loc='lower right', fontsize=9)
        ax1.set_ylim(0, 1.2)
        ax1.grid(True, alpha=0.3, axis='y')

    # Panel 2: Peak vs Final drift (recovery trajectory)
    ax2 = axes[1]

    for model, results in models.items():
        provider = get_provider(model)
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Extract paired peak/settled data
        peaks = []
        finals = []
        for r in results:
            if 'peak_drift' in r:
                peaks.append(r['peak_drift'])
                # Use settled_drift as final, fallback to final_drift
                finals.append(r.get('settled_drift', r.get('final_drift', r['peak_drift'])))

        if peaks and finals:
            ax2.scatter(peaks, finals, color=color, alpha=0.5, s=30,
                       label=f"{model.split('/')[-1][:12]}")

    # Diagonal (no recovery)
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

    plt.suptitle(f'Rescue Protocol Dynamics: Run 023b\n'
                f'{len(rescue_results)} Results | EH={EVENT_HORIZON}', fontsize=14)
    plt.tight_layout(rect=[0, 0, 1, 0.93])

    # Save
    output_file = output_dir / "rescue_dynamics.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_settling_curves(data: dict, output_dir: Path):
    """
    Generate settling time curve visualization.
    Shows how drift settles over time after perturbation.
    Output: 5_Settling/settling_curves.png

    Three-panel view:
    1. Step Response (oscilloscope-style): Drift over probe sequence
    2. Settling Performance by Provider: Bar chart of drift reduction
    3. Peak vs Settled trajectory arrows
    """
    print("\n[5_Settling] Generating settling curves...")

    # Filter for settling experiments
    settling_results = [r for r in data.get('results', []) if r.get('experiment') == 'settling']

    if not settling_results:
        print("  [SKIP] No settling experiment data found")
        return None

    print(f"  Found {len(settling_results)} settling results")

    # Group by provider for cleaner visualization
    providers = {}
    for result in settling_results:
        model = result.get('model', 'unknown')
        provider = get_provider(model)
        if provider not in providers:
            providers[provider] = []
        providers[provider].append(result)

    # Create 3-panel figure
    fig = plt.figure(figsize=(18, 6))

    # =========================================================================
    # Panel 1: STEP RESPONSE (Oscilloscope-style)
    # Shows drift values across probe sequence - like an oscilloscope trace
    # =========================================================================
    ax1 = fig.add_subplot(1, 3, 1)

    for provider, results in providers.items():
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Extract probe sequences and plot each one
        for i, result in enumerate(results[:5]):  # Limit to 5 per provider for clarity
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

    # =========================================================================
    # Panel 2: SETTLING PERFORMANCE BY PROVIDER
    # Bar chart showing drift reduction (peak - settled)
    # =========================================================================
    ax2 = fig.add_subplot(1, 3, 2)

    provider_names = []
    settling_means = []
    settling_stds = []
    colors = []

    for provider, results in providers.items():
        # Use settled_drift (actual field name) or fall back to calculating from peak
        settling_metrics = []
        for r in results:
            peak = r.get('peak_drift', 0)
            # Try settled_drift first, then final_drift, then baseline_to_final_drift
            settled = r.get('settled_drift', r.get('final_drift', r.get('baseline_to_final_drift', peak)))
            if peak > 0.01:
                # Settling metric = how much drift was reduced (positive = good)
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

        # Add value labels on bars
        for bar, mean in zip(bars, settling_means):
            ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.01,
                    f'{mean:.3f}', ha='center', fontsize=8)

        ax2.set_xticks(x_pos)
        ax2.set_xticklabels(provider_names, rotation=45, ha='right', fontsize=10)
        ax2.set_ylabel('Drift Reduction (Peak - Settled)', fontsize=11)
        ax2.set_title('Settling Performance by Provider', fontsize=12)
        ax2.grid(True, alpha=0.3, axis='y')
        ax2.axhline(y=0, color='black', linewidth=0.5)

    # =========================================================================
    # Panel 3: PEAK vs SETTLED TRAJECTORY
    # Arrows showing recovery direction for each provider
    # =========================================================================
    ax3 = fig.add_subplot(1, 3, 3)

    provider_list = list(providers.keys())
    for idx, (provider, results) in enumerate(providers.items()):
        color = PROVIDER_COLORS.get(provider, '#888888')

        # Calculate mean peak and settled
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

            # Arrow from peak to settled
            ax3.annotate('', xy=(mean_settled, y_pos),
                        xytext=(mean_peak, y_pos),
                        arrowprops=dict(arrowstyle='->', color=color, lw=2.5))

            # Markers
            ax3.scatter([mean_peak], [y_pos], color=color, s=120, marker='o',
                       edgecolors='black', linewidths=1, zorder=5)
            ax3.scatter([mean_settled], [y_pos], color=color, s=120, marker='s',
                       edgecolors='black', linewidths=1, zorder=5)

            # Label
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

    # Overall title
    plt.suptitle(f'Settling Time Analysis: Run 023b\n'
                f'{len(settling_results)} Results | EH={EVENT_HORIZON}', fontsize=14, fontweight='bold')
    plt.tight_layout(rect=[0, 0, 1, 0.93])

    # Save
    output_file = output_dir / "settling_curves.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


def generate_provider_comparison(data: dict, output_dir: Path):
    """
    Generate provider comparison radar/bar chart.
    Output: 6_Architecture/provider_comparison.png
    """
    print("\n[6_Architecture] Generating provider comparison...")

    # Group by provider
    providers = {}
    for result in data.get('results', []):
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

    # Prepare data
    provider_names = list(providers.keys())
    means = [np.mean(providers[p]) for p in provider_names]
    stds = [np.std(providers[p]) for p in provider_names]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in provider_names]

    # Bar chart
    bars = ax.bar(provider_names, means, yerr=stds, capsize=5,
                  color=colors, alpha=0.8, edgecolor='black')

    # Event Horizon
    ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon = {EVENT_HORIZON}')

    # Value labels
    for bar, mean in zip(bars, means):
        ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
                f'{mean:.3f}', ha='center', fontsize=10)

    ax.set_xlabel('Provider', fontsize=12)
    ax.set_ylabel('Mean Peak Drift (Cosine Distance)', fontsize=12)
    ax.set_title(f'Provider Comparison: Mean Peak Drift\n'
                 f'Run 023b (25 Ships, N=30)', fontsize=14)
    ax.legend(loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')
    ax.set_ylim(0, 1.0)

    plt.tight_layout()

    # Save
    output_file = output_dir / "provider_comparison.png"
    plt.savefig(output_file, dpi=150, bbox_inches='tight', facecolor='white')
    plt.savefig(output_file.with_suffix('.svg'), format='svg', bbox_inches='tight')
    plt.close()

    print(f"  Saved: {output_file}")
    return output_file


# =============================================================================
# MAIN ORCHESTRATOR
# =============================================================================

def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(description='Generate visualizations from run023b data')
    parser.add_argument('--folder', type=str, help='Generate only specific folder (e.g., 3_Stability)')
    parser.add_argument('--pilot', action='store_true', help='Pilot mode: 1 viz per folder')
    parser.add_argument('--list', action='store_true', help='List available folders')
    args = parser.parse_args()

    print("=" * 70)
    print("RUN 023c: VISUALIZATION GENERATOR (Cosine Era)")
    print("=" * 70)
    print(f"\nEvent Horizon: {EVENT_HORIZON} (Cosine Distance)")
    print(f"Warning: {THRESHOLD_WARNING}")
    print(f"Catastrophic: {THRESHOLD_CATASTROPHIC}")

    if args.list:
        print("\nAvailable visualization folders:")
        for folder, desc in VIZ_FOLDERS.items():
            print(f"  {folder}: {desc}")
        return 0

    # Ensure output directories exist
    for folder in VIZ_FOLDERS.keys():
        (OUTPUT_DIR / folder).mkdir(parents=True, exist_ok=True)

    # Load data
    data = load_run023b_data()

    # Generate visualizations
    generated = []

    if args.folder:
        # Specific folder only
        if args.folder not in VIZ_FOLDERS:
            print(f"[ERROR] Unknown folder: {args.folder}")
            print(f"  Available: {', '.join(VIZ_FOLDERS.keys())}")
            return 1
        folders_to_generate = [args.folder]
    else:
        folders_to_generate = list(VIZ_FOLDERS.keys())

    for folder in folders_to_generate:
        folder_path = OUTPUT_DIR / folder

        if folder == "3_Stability":
            viz = generate_stability_basin(data, folder_path)
            if viz:
                generated.append(viz)
            viz = generate_drift_histogram(data, folder_path)
            if viz:
                generated.append(viz)

        elif folder == "6_Architecture":
            viz = generate_provider_comparison(data, folder_path)
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

        elif folder == "11_Unified_Dashboard":
            vizs = generate_unified_dashboard(data, folder_path)
            if vizs:
                generated.extend(vizs)

        elif folder == "12_Metrics_Summary":
            viz = generate_metrics_summary(data, folder_path)
            if viz:
                generated.append(viz)

        else:
            print(f"\n[{folder}] Not yet implemented - placeholder")

    # Summary
    print("\n" + "=" * 70)
    print("GENERATION COMPLETE")
    print("=" * 70)
    print(f"\nGenerated {len(generated)} visualizations:")
    for viz in generated:
        print(f"  - {viz}")

    print(f"\nOutput directory: {OUTPUT_DIR}")
    print("\nNext steps:")
    print("  1. Review generated visualizations")
    print("  2. Run visualize_armada.py for additional types")
    print("  3. Update unified_dimensional_view.py for dashboard generation")

    return 0


if __name__ == '__main__':
    sys.exit(main())
