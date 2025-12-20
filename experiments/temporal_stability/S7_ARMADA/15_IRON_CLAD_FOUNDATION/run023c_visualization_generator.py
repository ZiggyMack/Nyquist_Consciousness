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
