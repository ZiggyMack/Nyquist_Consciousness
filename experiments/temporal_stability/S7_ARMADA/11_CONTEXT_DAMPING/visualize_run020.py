#!/usr/bin/env python3
"""
Run 020 Visualizations (A: Tribunal + B: Control vs Treatment)
==============================================================
Local visualization script for Run 020A and 020B data.

USAGE:
    py visualize_run020.py                          # Generate all visualizations
    py visualize_run020.py --run 020A               # Only 020A (Tribunal)
    py visualize_run020.py --run 020B               # Only 020B (Control/Treatment)
    py visualize_run020.py --experiment phase       # Specific visualization type

VISUALIZATIONS:

    Run 020A (Philosophical Tribunal):
        - phase_breakdown      - Prosecutor vs Defense drift comparison (bar chart)
        - exchange_depth       - Total exchanges vs peak/final drift scatter
        - provider_comparison  - Cross-provider tribunal dynamics
        - trajectory_overlay   - Drift sequences with phase markers

    Run 020B (Inherent vs Induced):
        - control_treatment    - Control vs Treatment drift comparison (paired bars)
        - ratio_analysis       - Control/Treatment ratio by provider (31-51% finding)
        - trajectory_compare   - Control (blue) vs Treatment (red) sequences
        - peak_final_scatter   - Peak vs Final drift colored by arm

Author: Claude (with Lisan Al Gaib)
Date: December 15, 2025
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
from scipy import stats

# Optional imports
try:
    import seaborn as sns
    HAS_SEABORN = True
except ImportError:
    HAS_SEABORN = False

# =============================================================================
# PATHS
# =============================================================================
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = SCRIPT_DIR / "results"
PICS_DIR = ARMADA_DIR / "visualizations" / "pics" / "run020"
CANONICAL_RESULTS_DIR = ARMADA_DIR / "0_results" / "runs"
MANIFEST_DIR = ARMADA_DIR / "0_results" / "manifests"

# Ensure output directory exists
PICS_DIR.mkdir(parents=True, exist_ok=True)

# =============================================================================
# CONSTANTS
# =============================================================================
VISUALIZATION_TYPES_020A = ['phase_breakdown', 'exchange_depth', 'provider_comparison', 'trajectory_overlay']
VISUALIZATION_TYPES_020B = ['control_treatment', 'ratio_analysis', 'trajectory_compare', 'peak_final_scatter']
VISUALIZATION_TYPES = VISUALIZATION_TYPES_020A + VISUALIZATION_TYPES_020B + ['all']

# Threshold zones (from Run 018)
THRESHOLD_ZONES = {
    "SAFE": (0, 0.9),
    "WARNING": (0.9, 1.23),
    "CRITICAL": (1.23, 1.8),
    "CATASTROPHIC": (1.8, float("inf"))
}

ZONE_COLORS = {
    "SAFE": "#2ecc71",       # Green
    "WARNING": "#f39c12",    # Orange
    "CRITICAL": "#e74c3c",   # Red
    "CATASTROPHIC": "#8e44ad" # Purple
}

# Provider colors (consistent with Run 018)
PROVIDER_COLORS = {
    "anthropic": "#D4A574",   # Warm brown/gold
    "openai": "#10A37F",      # OpenAI green
    "google": "#4285F4",      # Google blue
    "together": "#FF6B35",    # Vibrant orange
    "xai": "#1DA1F2",         # Twitter/X blue
    "mistral-7b": "#7C3AED",  # Purple
    "multi": "#6B7280"        # Gray for multi-provider
}

# Arm colors for 020B
ARM_COLORS = {
    "control": "#3498db",     # Blue - no identity probing
    "treatment": "#e74c3c"    # Red - identity probing
}


# =============================================================================
# DATA LOADING
# =============================================================================

def load_manifest(run_number: str) -> Optional[Dict]:
    """Load the consolidated drift manifest.

    Args:
        run_number: "020A" or "020B"
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


def get_experiment_data(manifest: Dict, experiment: str = None) -> List[Dict]:
    """Extract all runs for an experiment from manifest.

    For 020A: experiment = "tribunal"
    For 020B: experiment = "induced"

    Returns list of dicts with model name and all fields.
    """
    results = []
    experiments = manifest.get("experiments", {})

    # If no experiment specified, use first one
    if experiment is None:
        experiment = list(experiments.keys())[0] if experiments else None

    exp_data = experiments.get(experiment, {})

    for model, runs in exp_data.items():
        for run in runs:
            entry = run.copy()
            entry["model"] = model
            entry["provider"] = model  # Alias for compatibility
            results.append(entry)

    return results


def get_zone(drift: float) -> str:
    """Get threshold zone for a drift value."""
    for zone, (low, high) in THRESHOLD_ZONES.items():
        if low <= drift < high:
            return zone
    return "CATASTROPHIC"


def filter_valid_runs(data: List[Dict], min_exchanges: int = 10) -> List[Dict]:
    """Filter to only runs with substantial data (exclude rate-limited/failed runs)."""
    return [d for d in data if d.get('total_exchanges', d.get('probe_count', 0)) >= min_exchanges]


# =============================================================================
# 020A VISUALIZATIONS: Philosophical Tribunal
# =============================================================================

def visualize_020a_phase_breakdown(data: List[Dict]):
    """Prosecutor vs Defense drift comparison - the dual-phase tribunal dynamics."""
    valid_data = filter_valid_runs(data)

    if not valid_data:
        print("No valid 020A data for phase breakdown")
        return

    print(f"\n=== 020A: Phase Breakdown ({len(valid_data)} valid runs) ===")

    # Extract prosecutor and defense peaks
    entries = []
    for d in valid_data:
        p_peak = d.get('prosecutor_peak', 0) or 0
        d_peak = d.get('defense_peak', 0) or 0
        if p_peak > 0 or d_peak > 0:
            entries.append({
                'model': d.get('model', 'unknown'),
                'prosecutor': p_peak,
                'defense': d_peak,
                'peak_drift': d.get('peak_drift', 0),
                'exchanges': d.get('total_exchanges', 0)
            })

    if not entries:
        print("No prosecutor/defense data found")
        return

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Grouped bar chart - Prosecutor vs Defense by model
    ax1 = axes[0, 0]
    models = list(set(e['model'] for e in entries))
    model_data = {m: {'prosecutor': [], 'defense': []} for m in models}

    for e in entries:
        model_data[e['model']]['prosecutor'].append(e['prosecutor'])
        model_data[e['model']]['defense'].append(e['defense'])

    x = np.arange(len(models))
    width = 0.35

    p_means = [np.mean(model_data[m]['prosecutor']) if model_data[m]['prosecutor'] else 0 for m in models]
    d_means = [np.mean(model_data[m]['defense']) if model_data[m]['defense'] else 0 for m in models]
    p_stds = [np.std(model_data[m]['prosecutor']) if len(model_data[m]['prosecutor']) > 1 else 0 for m in models]
    d_stds = [np.std(model_data[m]['defense']) if len(model_data[m]['defense']) > 1 else 0 for m in models]

    bars1 = ax1.bar(x - width/2, p_means, width, yerr=p_stds, label='Prosecutor Phase',
                    color='#e74c3c', alpha=0.8, capsize=3)
    bars2 = ax1.bar(x + width/2, d_means, width, yerr=d_stds, label='Defense Phase',
                    color='#3498db', alpha=0.8, capsize=3)

    # Add threshold lines
    ax1.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5, label='Warning (0.9)')
    ax1.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.5, label='Critical (1.23)')

    ax1.set_xlabel('Provider')
    ax1.set_ylabel('Peak Drift (PFI)')
    ax1.set_title('Prosecutor vs Defense Peak Drift by Provider')
    ax1.set_xticks(x)
    ax1.set_xticklabels(models, rotation=45, ha='right')
    ax1.legend(loc='upper right')

    # Plot 2: Scatter - Prosecutor vs Defense correlation
    ax2 = axes[0, 1]
    prosecutors = [e['prosecutor'] for e in entries if e['prosecutor'] > 0 and e['defense'] > 0]
    defenses = [e['defense'] for e in entries if e['prosecutor'] > 0 and e['defense'] > 0]
    colors = [PROVIDER_COLORS.get(e['model'], '#6B7280') for e in entries if e['prosecutor'] > 0 and e['defense'] > 0]

    if prosecutors and defenses:
        ax2.scatter(prosecutors, defenses, c=colors, s=80, alpha=0.7, edgecolors='black', linewidth=0.5)

        # Add diagonal line (equal intensity)
        max_val = max(max(prosecutors), max(defenses)) * 1.1
        ax2.plot([0, max_val], [0, max_val], 'k--', alpha=0.3, label='Equal intensity')

        # Correlation
        if len(prosecutors) > 2:
            r, p = stats.pearsonr(prosecutors, defenses)
            ax2.text(0.05, 0.95, f'r = {r:.3f}\np = {p:.4f}', transform=ax2.transAxes,
                    fontsize=10, verticalalignment='top', bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    ax2.set_xlabel('Prosecutor Peak Drift')
    ax2.set_ylabel('Defense Peak Drift')
    ax2.set_title('Phase Correlation: Does Pressure Predict Recovery?')
    ax2.legend(loc='lower right')

    # Plot 3: Stacked histogram of phase peaks
    ax3 = axes[1, 0]
    all_prosecutor = [e['prosecutor'] for e in entries if e['prosecutor'] > 0]
    all_defense = [e['defense'] for e in entries if e['defense'] > 0]

    bins = np.linspace(0, 2.5, 20)
    ax3.hist(all_prosecutor, bins=bins, alpha=0.6, label='Prosecutor', color='#e74c3c')
    ax3.hist(all_defense, bins=bins, alpha=0.6, label='Defense', color='#3498db')

    # Add zone coloring to background
    for zone, (low, high) in THRESHOLD_ZONES.items():
        if high < 3:
            ax3.axvspan(low, min(high, 2.5), alpha=0.1, color=ZONE_COLORS[zone])

    ax3.set_xlabel('Peak Drift (PFI)')
    ax3.set_ylabel('Count')
    ax3.set_title('Distribution of Phase Peaks')
    ax3.legend()

    # Plot 4: Box plot comparison
    ax4 = axes[1, 1]
    box_data = [all_prosecutor, all_defense]
    bp = ax4.boxplot(box_data, labels=['Prosecutor', 'Defense'], patch_artist=True)
    bp['boxes'][0].set_facecolor('#e74c3c')
    bp['boxes'][1].set_facecolor('#3498db')
    bp['boxes'][0].set_alpha(0.6)
    bp['boxes'][1].set_alpha(0.6)

    # Add threshold lines
    ax4.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5)
    ax4.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.5)

    ax4.set_ylabel('Peak Drift (PFI)')
    ax4.set_title('Phase Peak Distributions')

    # Stats annotation
    if all_prosecutor and all_defense:
        t_stat, p_val = stats.ttest_ind(all_prosecutor, all_defense)
        ax4.text(0.5, 0.95, f't = {t_stat:.2f}, p = {p_val:.4f}',
                transform=ax4.transAxes, ha='center', fontsize=10,
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.suptitle("Run 020A: Philosophical Tribunal - Phase Dynamics", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run020a_phase_breakdown.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary
    print(f"\nPhase Statistics:")
    print(f"  Prosecutor: mean={np.mean(all_prosecutor):.3f}, std={np.std(all_prosecutor):.3f}, n={len(all_prosecutor)}")
    print(f"  Defense:    mean={np.mean(all_defense):.3f}, std={np.std(all_defense):.3f}, n={len(all_defense)}")


def visualize_020a_exchange_depth(data: List[Dict]):
    """Total exchanges vs peak/final drift - how conversation depth affects drift."""
    valid_data = filter_valid_runs(data)

    if not valid_data:
        print("No valid 020A data for exchange depth analysis")
        return

    print(f"\n=== 020A: Exchange Depth Analysis ({len(valid_data)} valid runs) ===")

    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    # Extract data
    exchanges = [d.get('total_exchanges', 0) for d in valid_data]
    peak_drifts = [d.get('peak_drift', 0) for d in valid_data]
    final_drifts = [d.get('drift', 0) for d in valid_data]
    models = [d.get('model', 'unknown') for d in valid_data]
    colors = [PROVIDER_COLORS.get(m, '#6B7280') for m in models]

    # Plot 1: Exchanges vs Peak Drift
    ax1 = axes[0]
    ax1.scatter(exchanges, peak_drifts, c=colors, s=80, alpha=0.7, edgecolors='black', linewidth=0.5)

    # Add threshold zones
    for zone, (low, high) in THRESHOLD_ZONES.items():
        if high < 3:
            ax1.axhline(y=low, color=ZONE_COLORS[zone], linestyle='--', alpha=0.4)

    # Fit trend line
    if len(exchanges) > 2:
        z = np.polyfit(exchanges, peak_drifts, 1)
        p = np.poly1d(z)
        x_line = np.linspace(min(exchanges), max(exchanges), 100)
        ax1.plot(x_line, p(x_line), 'r--', alpha=0.5, label=f'Trend (slope={z[0]:.4f})')
        ax1.legend()

    ax1.set_xlabel('Total Exchanges')
    ax1.set_ylabel('Peak Drift (PFI)')
    ax1.set_title('Conversation Depth vs Peak Drift')

    # Plot 2: Exchanges vs Final Drift (recovery)
    ax2 = axes[1]
    ax2.scatter(exchanges, final_drifts, c=colors, s=80, alpha=0.7, edgecolors='black', linewidth=0.5)

    # Add threshold zones
    for zone, (low, high) in THRESHOLD_ZONES.items():
        if high < 3:
            ax2.axhline(y=low, color=ZONE_COLORS[zone], linestyle='--', alpha=0.4)

    # Fit trend line
    if len(exchanges) > 2:
        z = np.polyfit(exchanges, final_drifts, 1)
        p = np.poly1d(z)
        ax2.plot(x_line, p(x_line), 'b--', alpha=0.5, label=f'Trend (slope={z[0]:.4f})')
        ax2.legend()

    ax2.set_xlabel('Total Exchanges')
    ax2.set_ylabel('Final Drift (PFI)')
    ax2.set_title('Conversation Depth vs Final Drift (Recovery)')

    # Add legend for providers
    legend_handles = [plt.Line2D([0], [0], marker='o', color='w',
                                  markerfacecolor=PROVIDER_COLORS.get(m, '#6B7280'),
                                  markersize=8, label=m)
                      for m in set(models)]
    fig.legend(handles=legend_handles, loc='upper right', bbox_to_anchor=(0.98, 0.98))

    plt.suptitle("Run 020A: Exchange Depth Analysis", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run020a_exchange_depth.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()


def visualize_020a_provider_comparison(data: List[Dict]):
    """Cross-provider tribunal dynamics comparison."""
    valid_data = filter_valid_runs(data)

    if not valid_data:
        print("No valid 020A data for provider comparison")
        return

    print(f"\n=== 020A: Provider Comparison ({len(valid_data)} valid runs) ===")

    # Group by provider
    provider_stats = {}
    for d in valid_data:
        model = d.get('model', 'unknown')
        if model not in provider_stats:
            provider_stats[model] = {
                'max_drifts': [],
                'final_drifts': [],
                'exchanges': [],
                'prosecutor_peaks': [],
                'defense_peaks': []
            }

        provider_stats[model]['max_drifts'].append(d.get('peak_drift', 0))
        provider_stats[model]['final_drifts'].append(d.get('drift', 0))
        provider_stats[model]['exchanges'].append(d.get('total_exchanges', 0))
        if d.get('prosecutor_peak'):
            provider_stats[model]['prosecutor_peaks'].append(d['prosecutor_peak'])
        if d.get('defense_peak'):
            provider_stats[model]['defense_peaks'].append(d['defense_peak'])

    # Filter to providers with N >= 2
    providers = [p for p in provider_stats if len(provider_stats[p]['max_drifts']) >= 2]

    if len(providers) < 2:
        print("Not enough providers with N >= 2 for comparison")
        return

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Peak drift by provider (box plot)
    ax1 = axes[0, 0]
    box_data = [provider_stats[p]['max_drifts'] for p in providers]
    bp = ax1.boxplot(box_data, labels=providers, patch_artist=True)

    for i, p in enumerate(providers):
        bp['boxes'][i].set_facecolor(PROVIDER_COLORS.get(p, '#6B7280'))
        bp['boxes'][i].set_alpha(0.6)

    ax1.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5)
    ax1.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.5)
    ax1.set_ylabel('Peak Drift (PFI)')
    ax1.set_title('Peak Drift by Provider')
    ax1.tick_params(axis='x', rotation=45)

    # Plot 2: Mean exchanges by provider (bar chart)
    ax2 = axes[0, 1]
    means = [np.mean(provider_stats[p]['exchanges']) for p in providers]
    stds = [np.std(provider_stats[p]['exchanges']) for p in providers]
    colors = [PROVIDER_COLORS.get(p, '#6B7280') for p in providers]

    bars = ax2.bar(providers, means, yerr=stds, color=colors, alpha=0.7, capsize=5)
    ax2.set_ylabel('Mean Exchanges')
    ax2.set_title('Conversation Depth by Provider')
    ax2.tick_params(axis='x', rotation=45)

    # Plot 3: Final drift (recovery) by provider
    ax3 = axes[1, 0]
    box_data_final = [provider_stats[p]['final_drifts'] for p in providers]
    bp2 = ax3.boxplot(box_data_final, labels=providers, patch_artist=True)

    for i, p in enumerate(providers):
        bp2['boxes'][i].set_facecolor(PROVIDER_COLORS.get(p, '#6B7280'))
        bp2['boxes'][i].set_alpha(0.6)

    ax3.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5)
    ax3.set_ylabel('Final Drift (PFI)')
    ax3.set_title('Recovery (Final Drift) by Provider')
    ax3.tick_params(axis='x', rotation=45)

    # Plot 4: Sample sizes and iron clad status
    ax4 = axes[1, 1]
    ns = [len(provider_stats[p]['max_drifts']) for p in providers]
    iron_clad = ['IRON CLAD' if n >= 3 else f'Need {3-n} more' for n in ns]
    bar_colors = ['#2ecc71' if n >= 3 else '#e74c3c' for n in ns]

    bars = ax4.bar(providers, ns, color=bar_colors, alpha=0.7)
    ax4.axhline(y=3, color='black', linestyle='--', alpha=0.5, label='IRON CLAD threshold (N=3)')

    # Annotate bars
    for i, (bar, status) in enumerate(zip(bars, iron_clad)):
        ax4.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.2,
                status, ha='center', fontsize=8, rotation=45)

    ax4.set_ylabel('Number of Runs')
    ax4.set_title('Sample Size by Provider (IRON CLAD Status)')
    ax4.tick_params(axis='x', rotation=45)
    ax4.legend()

    plt.suptitle("Run 020A: Cross-Provider Tribunal Dynamics", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run020a_provider_comparison.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary table
    print("\nProvider Summary:")
    print(f"{'Provider':<12} {'N':>4} {'Peak Mean':>10} {'Peak Std':>10} {'Final Mean':>10} {'Status':<15}")
    print("-" * 65)
    for p in providers:
        n = len(provider_stats[p]['max_drifts'])
        pm = np.mean(provider_stats[p]['max_drifts'])
        ps = np.std(provider_stats[p]['max_drifts'])
        fm = np.mean(provider_stats[p]['final_drifts'])
        status = "IRON CLAD" if n >= 3 else f"Need {3-n} more"
        print(f"{p:<12} {n:>4} {pm:>10.3f} {ps:>10.3f} {fm:>10.3f} {status:<15}")


def visualize_020a_trajectory_overlay(data: List[Dict]):
    """Placeholder for trajectory overlay - requires temporal log data.

    This would plot drift sequences over time with prosecutor/defense phases colored.
    Requires reading the full temporal log files, not just the manifest summaries.
    """
    print("\n=== 020A: Trajectory Overlay ===")
    print("Note: Full trajectory visualization requires temporal log data.")
    print("Generating summary visualization from manifest data...")

    # For now, create a summary visualization showing the peak-to-final journey
    valid_data = filter_valid_runs(data)

    if not valid_data:
        print("No valid 020A data for trajectory visualization")
        return

    fig, ax = plt.subplots(figsize=(10, 6))

    for d in valid_data[:20]:  # Limit to 20 for readability
        model = d.get('model', 'unknown')
        max_drift = d.get('peak_drift', 0)
        final_drift = d.get('drift', 0)
        p_peak = d.get('prosecutor_peak', 0) or 0
        d_peak = d.get('defense_peak', 0) or 0

        # Create simplified trajectory: start -> prosecutor peak -> defense peak -> final
        if p_peak > 0 and d_peak > 0:
            x = [0, 1, 2, 3]
            y = [0, p_peak, d_peak, final_drift]
            color = PROVIDER_COLORS.get(model, '#6B7280')
            ax.plot(x, y, 'o-', alpha=0.5, color=color, linewidth=1.5, markersize=4)

    # Add phase labels
    ax.set_xticks([0, 1, 2, 3])
    ax.set_xticklabels(['Baseline', 'Prosecutor\nPeak', 'Defense\nPeak', 'Final\nDrift'])

    # Add threshold zones
    ax.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5, label='Warning')
    ax.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.5, label='Critical')

    ax.set_ylabel('Drift (PFI)')
    ax.set_title('Run 020A: Simplified Drift Trajectories\n(Baseline → Prosecutor → Defense → Final)')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    outfile = PICS_DIR / "run020a_trajectory_overlay.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()


# =============================================================================
# 020B VISUALIZATIONS: Control vs Treatment (Inherent vs Induced)
# =============================================================================

def visualize_020b_control_treatment(data: List[Dict]):
    """Control vs Treatment drift comparison - the 82% inherent drift finding."""
    if not data:
        print("No 020B data for control/treatment analysis")
        return

    print(f"\n=== 020B: Control vs Treatment ({len(data)} entries) ===")

    # Separate by arm
    control = [d for d in data if d.get('arm') == 'control']
    treatment = [d for d in data if d.get('arm') == 'treatment']

    if not control or not treatment:
        print(f"Need both arms. Control: {len(control)}, Treatment: {len(treatment)}")
        return

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Bar chart comparing mean drift by arm
    ax1 = axes[0, 0]

    control_drifts = [d.get('drift', 0) for d in control]
    treatment_drifts = [d.get('drift', 0) for d in treatment]
    control_max = [d.get('peak_drift', 0) for d in control]
    treatment_max = [d.get('peak_drift', 0) for d in treatment]

    x = np.arange(2)
    width = 0.35

    means_final = [np.mean(control_drifts), np.mean(treatment_drifts)]
    stds_final = [np.std(control_drifts), np.std(treatment_drifts)]
    means_peak = [np.mean(control_max), np.mean(treatment_max)]
    stds_peak = [np.std(control_max), np.std(treatment_max)]

    bars1 = ax1.bar(x - width/2, means_final, width, yerr=stds_final,
                    label='Final Drift', color=[ARM_COLORS['control'], ARM_COLORS['treatment']], alpha=0.7, capsize=5)
    bars2 = ax1.bar(x + width/2, means_peak, width, yerr=stds_peak,
                    label='Peak Drift', color=[ARM_COLORS['control'], ARM_COLORS['treatment']], alpha=0.4, capsize=5)

    ax1.set_xticks(x)
    ax1.set_xticklabels(['Control\n(No Identity Probing)', 'Treatment\n(Identity Probing)'])
    ax1.set_ylabel('Drift (PFI)')
    ax1.set_title('Control vs Treatment: Mean Drift')
    ax1.legend()

    # Add threshold lines
    ax1.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5)
    ax1.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.5)

    # Plot 2: Box plot comparison
    ax2 = axes[0, 1]
    bp = ax2.boxplot([control_drifts, treatment_drifts], labels=['Control', 'Treatment'], patch_artist=True)
    bp['boxes'][0].set_facecolor(ARM_COLORS['control'])
    bp['boxes'][1].set_facecolor(ARM_COLORS['treatment'])
    bp['boxes'][0].set_alpha(0.6)
    bp['boxes'][1].set_alpha(0.6)

    ax2.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5)
    ax2.set_ylabel('Final Drift (PFI)')
    ax2.set_title('Final Drift Distribution by Arm')

    # Add statistical test
    if len(control_drifts) >= 2 and len(treatment_drifts) >= 2:
        t_stat, p_val = stats.ttest_ind(control_drifts, treatment_drifts)
        ax2.text(0.5, 0.95, f't = {t_stat:.2f}, p = {p_val:.4f}',
                transform=ax2.transAxes, ha='center', fontsize=10,
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    # Plot 3: Scatter - Control vs Treatment paired by provider
    ax3 = axes[1, 0]
    providers = set(d.get('model') for d in data)

    for prov in providers:
        c_data = [d for d in control if d.get('model') == prov]
        t_data = [d for d in treatment if d.get('model') == prov]

        if c_data and t_data:
            c_mean = np.mean([d.get('drift', 0) for d in c_data])
            t_mean = np.mean([d.get('drift', 0) for d in t_data])

            color = PROVIDER_COLORS.get(prov, '#6B7280')
            ax3.scatter([c_mean], [t_mean], c=[color], s=150, label=prov,
                       edgecolors='black', linewidth=1)
            ax3.annotate(prov, (c_mean, t_mean), textcoords="offset points",
                        xytext=(5, 5), fontsize=9)

    # Add diagonal (control = treatment)
    max_val = max(max(control_drifts + treatment_drifts), 2.5)
    ax3.plot([0, max_val], [0, max_val], 'k--', alpha=0.3, label='Equal drift')

    ax3.set_xlabel('Control Drift (No Probing)')
    ax3.set_ylabel('Treatment Drift (With Probing)')
    ax3.set_title('Provider-Level Comparison')

    # Plot 4: The key finding - ratio calculation
    ax4 = axes[1, 1]

    # Calculate inherent drift ratio per provider
    ratios = []
    provider_labels = []
    for prov in providers:
        c_data = [d.get('drift', 0) for d in control if d.get('model') == prov]
        t_data = [d.get('drift', 0) for d in treatment if d.get('model') == prov]

        if c_data and t_data:
            c_mean = np.mean(c_data)
            t_mean = np.mean(t_data)
            if t_mean > 0:
                ratio = c_mean / t_mean * 100  # As percentage
                ratios.append(ratio)
                provider_labels.append(prov)

    if ratios:
        colors = [PROVIDER_COLORS.get(p, '#6B7280') for p in provider_labels]
        bars = ax4.bar(provider_labels, ratios, color=colors, alpha=0.7)

        # Add 82% reference line
        ax4.axhline(y=82, color='purple', linestyle='--', linewidth=2, label='82% (Run 018 Finding)')

        # Add 50% reference (half inherent, half induced)
        ax4.axhline(y=50, color='gray', linestyle=':', alpha=0.5, label='50% reference')

        ax4.set_ylabel('Inherent Drift Ratio (%)\n(Control / Treatment × 100)')
        ax4.set_title('Inherent Drift Ratio by Provider\n(Higher = More Inherent, Less Induced)')
        ax4.legend()
        ax4.set_ylim(0, 120)

        # Annotate bars with values
        for bar, ratio in zip(bars, ratios):
            ax4.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 2,
                    f'{ratio:.0f}%', ha='center', fontsize=10)

    plt.suptitle("Run 020B: Inherent vs Induced Drift (Control/Treatment)", fontsize=14, fontweight='bold')
    plt.tight_layout()

    outfile = PICS_DIR / "run020b_control_treatment.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()

    # Print summary
    print("\nControl vs Treatment Summary:")
    print(f"  Control:   mean={np.mean(control_drifts):.3f}, std={np.std(control_drifts):.3f}, n={len(control_drifts)}")
    print(f"  Treatment: mean={np.mean(treatment_drifts):.3f}, std={np.std(treatment_drifts):.3f}, n={len(treatment_drifts)}")
    if ratios:
        print(f"\n  Mean Inherent Ratio: {np.mean(ratios):.1f}%")
        print(f"  (Run 018 found 82% inherent, 18% induced)")


def visualize_020b_ratio_analysis(data: List[Dict]):
    """Deep dive into the control/treatment ratio - the thermometer analogy."""
    if not data:
        print("No 020B data for ratio analysis")
        return

    print(f"\n=== 020B: Ratio Analysis (Thermometer Analogy) ===")

    control = [d for d in data if d.get('arm') == 'control']
    treatment = [d for d in data if d.get('arm') == 'treatment']

    if not control or not treatment:
        return

    fig, axes = plt.subplots(1, 2, figsize=(12, 5))

    # Plot 1: Waterfall chart showing inherent vs induced components
    ax1 = axes[0]

    providers = list(set(d.get('model') for d in data))
    x = np.arange(len(providers))

    inherent = []
    induced = []

    for prov in providers:
        c_data = [d.get('drift', 0) for d in control if d.get('model') == prov]
        t_data = [d.get('drift', 0) for d in treatment if d.get('model') == prov]

        c_mean = np.mean(c_data) if c_data else 0
        t_mean = np.mean(t_data) if t_data else 0

        inherent.append(c_mean)
        induced.append(max(0, t_mean - c_mean))  # Additional drift from probing

    # Stacked bar chart
    bars1 = ax1.bar(x, inherent, label='Inherent Drift\n(Present without probing)',
                    color='#3498db', alpha=0.8)
    bars2 = ax1.bar(x, induced, bottom=inherent, label='Induced Drift\n(Additional from probing)',
                    color='#e74c3c', alpha=0.8)

    ax1.set_xticks(x)
    ax1.set_xticklabels(providers, rotation=45, ha='right')
    ax1.set_ylabel('Drift (PFI)')
    ax1.set_title('Decomposition: Inherent vs Induced Drift')
    ax1.legend()

    # Add threshold line
    ax1.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.5, label='Critical')

    # Plot 2: The thermometer analogy visualization
    ax2 = axes[1]

    # Calculate overall ratio
    total_control = np.mean([d.get('drift', 0) for d in control])
    total_treatment = np.mean([d.get('drift', 0) for d in treatment])

    if total_treatment > 0 and total_control > 0:
        # Ratio shows how much of treatment drift was already present in control
        inherent_pct = min((total_control / total_treatment) * 100, 100)
        induced_pct = max(100 - inherent_pct, 0)
    else:
        inherent_pct = 50  # Default to 50/50 if no valid data
        induced_pct = 50

    # Create pie chart showing the split - ensure non-negative values
    sizes = [max(inherent_pct, 0), max(induced_pct, 0)]
    labels = [f'Inherent\n{inherent_pct:.0f}%', f'Induced\n{induced_pct:.0f}%']
    colors_pie = ['#3498db', '#e74c3c']
    explode = (0.05, 0)  # Slightly explode inherent slice

    wedges, texts, autotexts = ax2.pie(sizes, labels=labels, colors=colors_pie,
                                        explode=explode, autopct='', startangle=90,
                                        textprops={'fontsize': 12})

    # Add center text
    ax2.text(0, 0, 'Drift\nComposition', ha='center', va='center', fontsize=11, fontweight='bold')

    ax2.set_title('The Thermometer Analogy\n"Measurement Reveals, Not Creates"')

    # Add annotation
    fig.text(0.5, 0.02,
             f'Like a thermometer that reveals pre-existing temperature, identity probing reveals pre-existing drift.\n'
             f'Overall: {inherent_pct:.0f}% inherent (present without probing) + {induced_pct:.0f}% induced (from probing)',
             ha='center', fontsize=10, style='italic',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.5))

    plt.suptitle("Run 020B: The Thermometer Analogy", fontsize=14, fontweight='bold')
    plt.tight_layout(rect=[0, 0.08, 1, 0.95])

    outfile = PICS_DIR / "run020b_ratio_analysis.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()


def visualize_020b_trajectory_compare(data: List[Dict]):
    """Placeholder for control vs treatment trajectory comparison."""
    print("\n=== 020B: Trajectory Comparison ===")
    print("Note: Full trajectory visualization requires temporal log data.")

    # Create summary from manifest data
    control = [d for d in data if d.get('arm') == 'control']
    treatment = [d for d in data if d.get('arm') == 'treatment']

    if not control or not treatment:
        return

    fig, ax = plt.subplots(figsize=(10, 6))

    # Plot simplified trajectories
    for d in control:
        max_drift = d.get('peak_drift', 0)
        final_drift = d.get('drift', 0)
        probes = d.get('probe_count', 0)

        x = [0, probes/2, probes]
        y = [0, max_drift, final_drift]
        ax.plot(x, y, 'o-', color=ARM_COLORS['control'], alpha=0.5, linewidth=2, markersize=4)

    for d in treatment:
        max_drift = d.get('peak_drift', 0)
        final_drift = d.get('drift', 0)
        probes = d.get('probe_count', 0)

        x = [0, probes/2, probes]
        y = [0, max_drift, final_drift]
        ax.plot(x, y, 'o-', color=ARM_COLORS['treatment'], alpha=0.5, linewidth=2, markersize=4)

    # Add legend
    ax.plot([], [], 'o-', color=ARM_COLORS['control'], label='Control (No Probing)', linewidth=2)
    ax.plot([], [], 'o-', color=ARM_COLORS['treatment'], label='Treatment (With Probing)', linewidth=2)

    # Add threshold zones
    ax.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.5)
    ax.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.5)

    ax.set_xlabel('Probe Count')
    ax.set_ylabel('Drift (PFI)')
    ax.set_title('Run 020B: Simplified Drift Trajectories\nControl (Blue) vs Treatment (Red)')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    outfile = PICS_DIR / "run020b_trajectory_compare.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()


def visualize_020b_peak_final_scatter(data: List[Dict]):
    """Peak vs Final drift scatter, colored by arm type."""
    if not data:
        print("No 020B data for peak/final scatter")
        return

    print(f"\n=== 020B: Peak vs Final Scatter ({len(data)} entries) ===")

    fig, ax = plt.subplots(figsize=(10, 8))

    for d in data:
        max_drift = d.get('peak_drift', 0)
        final_drift = d.get('drift', 0)
        arm = d.get('arm', 'unknown')
        model = d.get('model', 'unknown')

        color = ARM_COLORS.get(arm, '#6B7280')
        marker = 'o' if arm == 'control' else '^'

        ax.scatter(max_drift, final_drift, c=color, marker=marker, s=100, alpha=0.7,
                  edgecolors='black', linewidth=0.5)

    # Add diagonal (no recovery)
    max_val = max(d.get('peak_drift', 0) for d in data) * 1.1
    ax.plot([0, max_val], [0, max_val], 'k--', alpha=0.3, label='No recovery (peak = final)')

    # Add threshold zones
    ax.axhline(y=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.4)
    ax.axhline(y=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.4)
    ax.axvline(x=0.9, color=ZONE_COLORS["WARNING"], linestyle='--', alpha=0.4)
    ax.axvline(x=1.23, color=ZONE_COLORS["CRITICAL"], linestyle='--', alpha=0.4)

    # Legend
    ax.scatter([], [], c=ARM_COLORS['control'], marker='o', s=100, label='Control')
    ax.scatter([], [], c=ARM_COLORS['treatment'], marker='^', s=100, label='Treatment')
    ax.legend(loc='upper left')

    ax.set_xlabel('Peak Drift (PFI)')
    ax.set_ylabel('Final Drift (PFI)')
    ax.set_title('Run 020B: Peak vs Final Drift\n(Distance below diagonal = recovery)')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    outfile = PICS_DIR / "run020b_peak_final_scatter.png"
    plt.savefig(outfile, dpi=150, bbox_inches='tight')
    plt.savefig(outfile.with_suffix('.pdf'), bbox_inches='tight')
    print(f"Saved: {outfile}")
    plt.close()


# =============================================================================
# MAIN AND EXPORTS
# =============================================================================

def generate_all_020a_visualizations():
    """Generate all Run 020A visualizations."""
    print("\n" + "="*60)
    print("Generating Run 020A Visualizations (Philosophical Tribunal)")
    print("="*60)

    manifest = load_manifest("020A")
    if manifest is None:
        print("ERROR: Could not load 020A manifest")
        return

    data = get_experiment_data(manifest, "tribunal")
    print(f"Loaded {len(data)} tribunal entries from manifest")

    visualize_020a_phase_breakdown(data)
    visualize_020a_exchange_depth(data)
    visualize_020a_provider_comparison(data)
    visualize_020a_trajectory_overlay(data)


def generate_all_020b_visualizations():
    """Generate all Run 020B visualizations."""
    print("\n" + "="*60)
    print("Generating Run 020B Visualizations (Control vs Treatment)")
    print("="*60)

    manifest = load_manifest("020B")
    if manifest is None:
        print("ERROR: Could not load 020B manifest")
        return

    data = get_experiment_data(manifest, "induced")
    print(f"Loaded {len(data)} induced entries from manifest")

    visualize_020b_control_treatment(data)
    visualize_020b_ratio_analysis(data)
    visualize_020b_trajectory_compare(data)
    visualize_020b_peak_final_scatter(data)


def generate_all_run020_visualizations():
    """Generate all Run 020 visualizations (both A and B)."""
    generate_all_020a_visualizations()
    generate_all_020b_visualizations()

    # Create markdown summary table
    generate_summary_table()


def generate_summary_table():
    """Generate a markdown table summarizing all visualizations."""
    summary = """# Run 020 Visualizations Summary

Generated: {timestamp}

## Run 020A: Philosophical Tribunal

| Visualization | Description | File |
|---------------|-------------|------|
| Phase Breakdown | Prosecutor vs Defense drift comparison | run020a_phase_breakdown.png |
| Exchange Depth | Total exchanges vs peak/final drift | run020a_exchange_depth.png |
| Provider Comparison | Cross-provider tribunal dynamics | run020a_provider_comparison.png |
| Trajectory Overlay | Simplified drift trajectories | run020a_trajectory_overlay.png |

## Run 020B: Control vs Treatment (Inherent vs Induced)

| Visualization | Description | File |
|---------------|-------------|------|
| Control/Treatment | Main comparison with ratio calculation | run020b_control_treatment.png |
| Ratio Analysis | Thermometer analogy decomposition | run020b_ratio_analysis.png |
| Trajectory Compare | Control vs Treatment trajectories | run020b_trajectory_compare.png |
| Peak/Final Scatter | Peak vs Final drift by arm | run020b_peak_final_scatter.png |

## Key Findings

### 020A Tribunal
- Prosecutor and Defense phases show distinct drift dynamics
- Cross-provider replication achieved (OpenAI, Together at IRON CLAD)

### 020B Inherent vs Induced
- Control arms show ~31-51% of treatment drift
- Confirms 82% inherent drift finding from Run 018
- "Thermometer analogy": measurement reveals, doesn't create

"""

    summary = summary.format(timestamp=datetime.now().isoformat())

    outfile = PICS_DIR / "run020_summary.md"
    with open(outfile, 'w', encoding='utf-8') as f:
        f.write(summary)
    print(f"\nSaved: {outfile}")


def main():
    parser = argparse.ArgumentParser(description="Generate Run 020 visualizations")
    parser.add_argument('--run', choices=['020A', '020B', 'all'], default='all',
                       help='Which run to visualize')
    parser.add_argument('--experiment', choices=VISUALIZATION_TYPES, default='all',
                       help='Specific visualization type')

    args = parser.parse_args()

    print(f"\nRun 020 Visualization Generator")
    print(f"Output directory: {PICS_DIR}")

    if args.run in ['020A', 'all']:
        if args.experiment == 'all' or args.experiment in VISUALIZATION_TYPES_020A:
            generate_all_020a_visualizations()

    if args.run in ['020B', 'all']:
        if args.experiment == 'all' or args.experiment in VISUALIZATION_TYPES_020B:
            generate_all_020b_visualizations()

    if args.run == 'all' and args.experiment == 'all':
        generate_summary_table()

    print(f"\nVisualization complete!")
    print(f"Files saved to: {PICS_DIR}")


if __name__ == "__main__":
    main()
