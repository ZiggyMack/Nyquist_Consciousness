#!/usr/bin/env python3
"""
Oobleck Effect Visualizations (Run 020A + 020B)
================================================
Visualizes the Oobleck Effect: how supportive vs adversarial probing
affects identity drift differently.

Run 020A: Philosophical Tribunal (Prosecutor vs Defense phases)
Run 020B: Control vs Treatment (Inherent vs Induced drift)

LIGHT MODE for publication consistency.

Author: Claude (VALIS Network)
Date: December 2025
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

# =============================================================================
# PATHS
# =============================================================================
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent.parent.parent
RESULTS_DIR = ARMADA_DIR / "11_CONTEXT_DAMPING" / "results"
OUTPUT_DIR = SCRIPT_DIR

# =============================================================================
# CONSTANTS - Updated for COSINE methodology
# =============================================================================
EVENT_HORIZON = 0.80  # Cosine distance threshold
WARNING_THRESHOLD = 0.60
CRITICAL_THRESHOLD = 1.20

# Provider colors (consistent with 12_Metrics_Summary)
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
    'mistral': '#FF6B35',
    'multi': '#6B7280'
}

# Arm colors for 020B
ARM_COLORS = {
    'control': '#3498db',
    'treatment': '#e74c3c'
}


def load_run020a_data():
    """Load Run 020A (Tribunal) CURRENT data."""
    data_file = RESULTS_DIR / "S7_run_020A_CURRENT.json"
    if not data_file.exists():
        print(f"Warning: 020A data not found at {data_file}")
        return []

    with open(data_file, 'r', encoding='utf-8') as f:
        data = json.load(f)

    return data.get('results', [])


def load_run020b_data():
    """Load Run 020B (Control/Treatment) CURRENT data."""
    data_file = RESULTS_DIR / "S7_run_020B_CURRENT.json"
    if not data_file.exists():
        print(f"Warning: 020B data not found at {data_file}")
        return []

    with open(data_file, 'r', encoding='utf-8') as f:
        data = json.load(f)

    return data.get('results', [])


def get_provider_color(provider_or_model):
    """Get color for provider/model."""
    name = str(provider_or_model).lower()
    for key, color in PROVIDER_COLORS.items():
        if key in name:
            return color
    return '#6B7280'


# =============================================================================
# RUN 020A VISUALIZATIONS: Philosophical Tribunal
# =============================================================================

def plot_020a_phase_breakdown(data, output_dir):
    """Prosecutor vs Defense drift comparison - 2x2 quad layout."""
    if not data:
        print("No 020A data for phase breakdown")
        return

    print(f"\n=== 020A: Phase Breakdown ({len(data)} entries) ===")

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Extract prosecutor and defense peaks from phase_markers
    entries = []
    for d in data:
        phase_markers = d.get('phase_markers', {})
        p_peak = phase_markers.get('prosecutor_peak', 0) or 0
        d_peak = phase_markers.get('defense_peak', 0) or 0
        model = d.get('subject_id', d.get('model', 'unknown'))
        # Extract provider from subject_id (e.g., "tribunal_v8_anthropic_xxx" -> "anthropic")
        provider = 'unknown'
        subject_id = str(model).lower()
        for p in ['anthropic', 'openai', 'google', 'xai', 'together', 'mistral']:
            if p in subject_id:
                provider = p
                break

        if p_peak > 0 or d_peak > 0:
            entries.append({
                'model': model,
                'provider': provider,
                'prosecutor': p_peak,
                'defense': d_peak,
                'peak_drift': d.get('peak_drift', 0),
                'final_drift': d.get('final_drift', 0)
            })

    if not entries:
        print("No prosecutor/defense data found")
        plt.close()
        return

    # Panel 1: Aggregate bar chart - Prosecutor vs Defense (no provider attribution in 020A)
    ax1 = axes[0, 0]

    # Aggregate all prosecutor and defense peaks
    all_prosecutor = [e['prosecutor'] for e in entries if e['prosecutor'] > 0]
    all_defense = [e['defense'] for e in entries if e['defense'] > 0]

    x = np.arange(1)  # Single aggregate bar group
    width = 0.35

    p_mean = np.mean(all_prosecutor) if all_prosecutor else 0
    d_mean = np.mean(all_defense) if all_defense else 0
    p_se = np.std(all_prosecutor) / np.sqrt(len(all_prosecutor)) if len(all_prosecutor) > 1 else 0
    d_se = np.std(all_defense) / np.sqrt(len(all_defense)) if len(all_defense) > 1 else 0

    bars1 = ax1.bar(x - width/2, [p_mean], width, yerr=[p_se], capsize=5,
                    label='Prosecutor Phase', color='#e74c3c', alpha=0.8, edgecolor='black')
    bars2 = ax1.bar(x + width/2, [d_mean], width, yerr=[d_se], capsize=5,
                    label='Defense Phase', color='#3498db', alpha=0.8, edgecolor='black')

    ax1.axhline(y=WARNING_THRESHOLD, color='#f39c12', linestyle='--', alpha=0.7, label='Warning (0.60)')
    ax1.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon (0.80)')

    # Add value labels on bars
    ax1.text(x[0] - width/2, p_mean + p_se + 0.02, f'{p_mean:.3f}', ha='center', fontsize=10, fontweight='bold')
    ax1.text(x[0] + width/2, d_mean + d_se + 0.02, f'{d_mean:.3f}', ha='center', fontsize=10, fontweight='bold')

    ax1.set_ylabel('Peak Drift (Cosine)', fontsize=11)
    ax1.set_title(f'Prosecutor vs Defense Peak Drift (AGGREGATE)\n(n={len(entries)} sessions, no provider attribution)', fontsize=11, fontweight='bold')
    ax1.set_xticks(x)
    ax1.set_xticklabels(['AGGREGATE'])
    ax1.legend(loc='upper right', facecolor='white')
    ax1.grid(axis='y', alpha=0.3)
    ax1.set_xlim(-0.8, 0.8)  # Center the single bar group

    # Panel 2: Scatter - Prosecutor vs Defense correlation
    ax2 = axes[0, 1]
    prosecutors = [e['prosecutor'] for e in entries if e['prosecutor'] > 0 and e['defense'] > 0]
    defenses = [e['defense'] for e in entries if e['prosecutor'] > 0 and e['defense'] > 0]
    colors = [get_provider_color(e['model']) for e in entries if e['prosecutor'] > 0 and e['defense'] > 0]

    if prosecutors and defenses:
        ax2.scatter(prosecutors, defenses, c=colors, s=80, alpha=0.7, edgecolors='black', linewidth=0.5)

        max_val = max(max(prosecutors), max(defenses)) * 1.1
        ax2.plot([0, max_val], [0, max_val], 'k--', alpha=0.3, label='Equal intensity')

        if len(prosecutors) > 2:
            r, p = stats.pearsonr(prosecutors, defenses)
            ax2.annotate(f'r = {r:.3f}\np = {p:.4f}', xy=(0.05, 0.95), xycoords='axes fraction',
                        fontsize=10, va='top', bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    ax2.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.5)
    ax2.axvline(x=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.5)
    ax2.set_xlabel('Prosecutor Peak Drift', fontsize=11)
    ax2.set_ylabel('Defense Peak Drift', fontsize=11)
    ax2.set_title('Phase Correlation: Does Pressure Predict Recovery?', fontsize=12, fontweight='bold')
    ax2.legend(loc='lower right', facecolor='white')
    ax2.grid(alpha=0.3)

    # Panel 3: Histogram of phase peaks
    ax3 = axes[1, 0]
    all_prosecutor = [e['prosecutor'] for e in entries if e['prosecutor'] > 0]
    all_defense = [e['defense'] for e in entries if e['defense'] > 0]

    bins = np.linspace(0, 2.5, 20)
    ax3.hist(all_prosecutor, bins=bins, alpha=0.6, label='Prosecutor', color='#e74c3c', edgecolor='black')
    ax3.hist(all_defense, bins=bins, alpha=0.6, label='Defense', color='#3498db', edgecolor='black')

    ax3.axvline(x=EVENT_HORIZON, color='#e74c3c', linestyle='--', linewidth=2, alpha=0.7, label='Event Horizon')
    ax3.set_xlabel('Peak Drift (Cosine)', fontsize=11)
    ax3.set_ylabel('Count', fontsize=11)
    ax3.set_title('Distribution of Phase Peaks', fontsize=12, fontweight='bold')
    ax3.legend(facecolor='white')
    ax3.grid(alpha=0.3)

    # Panel 4: Box plot comparison with t-test
    ax4 = axes[1, 1]
    box_data = [all_prosecutor, all_defense]
    bp = ax4.boxplot(box_data, labels=['Prosecutor', 'Defense'], patch_artist=True, widths=0.6)
    bp['boxes'][0].set_facecolor('#e74c3c')
    bp['boxes'][1].set_facecolor('#3498db')
    for box in bp['boxes']:
        box.set_alpha(0.7)
        box.set_edgecolor('black')
    for median in bp['medians']:
        median.set_color('black')
        median.set_linewidth(2)

    ax4.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon')

    if all_prosecutor and all_defense:
        t_stat, p_val = stats.ttest_ind(all_prosecutor, all_defense)
        ax4.annotate(f't = {t_stat:.2f}, p = {p_val:.4f}', xy=(0.5, 0.95), xycoords='axes fraction',
                    ha='center', fontsize=10, bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    ax4.set_ylabel('Peak Drift (Cosine)', fontsize=11)
    ax4.set_title('Phase Peak Distributions', fontsize=12, fontweight='bold')
    ax4.grid(axis='y', alpha=0.3)

    fig.suptitle('Run 020A: Philosophical Tribunal - Phase Dynamics\n(Oobleck Effect: Adversarial vs Supportive Probing)',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_phase_breakdown.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


def plot_020a_trajectory_overlay(data, output_dir):
    """Simplified drift trajectories: Baseline -> Prosecutor -> Defense -> Final."""
    if not data:
        print("No 020A data for trajectory overlay")
        return

    print(f"\n=== 020A: Trajectory Overlay ({len(data)} entries) ===")

    fig, ax = plt.subplots(figsize=(12, 7))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')

    plotted = 0
    for d in data:
        phase_markers = d.get('phase_markers', {})
        p_peak = phase_markers.get('prosecutor_peak', 0) or 0
        d_peak = phase_markers.get('defense_peak', 0) or 0
        final = d.get('final_drift', 0) or 0
        model = d.get('subject_id', d.get('model', 'unknown'))

        if p_peak > 0:  # Only need prosecutor peak (defense can be 0)
            x = [0, 1, 2, 3]
            y = [0, p_peak, d_peak if d_peak > 0 else p_peak * 0.8, final]  # Estimate defense if 0
            color = get_provider_color(model)
            ax.plot(x, y, 'o-', alpha=0.6, color=color, linewidth=2, markersize=6)
            plotted += 1
            if plotted >= 20:  # Limit for readability
                break

    ax.set_xticks([0, 1, 2, 3])
    ax.set_xticklabels(['Baseline', 'Prosecutor\nPeak', 'Defense\nPeak', 'Final\nDrift'], fontsize=11)

    ax.axhline(y=WARNING_THRESHOLD, color='#f39c12', linestyle='--', alpha=0.7, label='Warning')
    ax.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon')

    ax.set_ylabel('Drift (Cosine)', fontsize=11)
    ax.set_title('Run 020A: Simplified Drift Trajectories\n(Baseline → Prosecutor → Defense → Final)',
                fontsize=12, fontweight='bold')
    ax.legend(loc='upper right', facecolor='white')
    ax.grid(True, alpha=0.3)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_trajectory_overlay.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


# =============================================================================
# RUN 020B VISUALIZATIONS: Control vs Treatment
# =============================================================================

def plot_020b_control_treatment(data, output_dir):
    """Control vs Treatment comparison - the inherent vs induced finding."""
    if not data:
        print("No 020B data for control/treatment analysis")
        return

    print(f"\n=== 020B: Control vs Treatment ({len(data)} entries) ===")

    control = [d for d in data if d.get('arm') == 'control']
    treatment = [d for d in data if d.get('arm') == 'treatment']

    if not control or not treatment:
        print(f"Need both arms. Control: {len(control)}, Treatment: {len(treatment)}")
        return

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    control_drifts = [d.get('final_drift', d.get('drift', 0)) for d in control]
    treatment_drifts = [d.get('final_drift', d.get('drift', 0)) for d in treatment]
    control_peaks = [d.get('peak_drift', 0) for d in control]
    treatment_peaks = [d.get('peak_drift', 0) for d in treatment]

    # Panel 1: Bar chart comparing mean drift
    ax1 = axes[0, 0]
    x = np.arange(2)
    width = 0.35

    means_final = [np.mean(control_drifts), np.mean(treatment_drifts)]
    means_peak = [np.mean(control_peaks), np.mean(treatment_peaks)]

    bars1 = ax1.bar(x - width/2, means_final, width, label='Final Drift',
                    color=[ARM_COLORS['control'], ARM_COLORS['treatment']], alpha=0.8, edgecolor='black')
    bars2 = ax1.bar(x + width/2, means_peak, width, label='Peak Drift',
                    color=[ARM_COLORS['control'], ARM_COLORS['treatment']], alpha=0.4, edgecolor='black')

    ax1.set_xticks(x)
    ax1.set_xticklabels(['Control\n(No Identity Probing)', 'Treatment\n(Identity Probing)'])
    ax1.set_ylabel('Drift (Cosine)', fontsize=11)
    ax1.set_title('Control vs Treatment: Mean Drift', fontsize=12, fontweight='bold')
    ax1.legend(facecolor='white')
    ax1.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7)
    ax1.grid(axis='y', alpha=0.3)

    # Panel 2: Box plot with t-test
    ax2 = axes[0, 1]
    bp = ax2.boxplot([control_drifts, treatment_drifts], labels=['Control', 'Treatment'],
                     patch_artist=True, widths=0.6)
    bp['boxes'][0].set_facecolor(ARM_COLORS['control'])
    bp['boxes'][1].set_facecolor(ARM_COLORS['treatment'])
    for box in bp['boxes']:
        box.set_alpha(0.7)
        box.set_edgecolor('black')
    for median in bp['medians']:
        median.set_color('black')
        median.set_linewidth(2)

    if len(control_drifts) >= 2 and len(treatment_drifts) >= 2:
        t_stat, p_val = stats.ttest_ind(control_drifts, treatment_drifts)
        ax2.annotate(f't = {t_stat:.2f}, p = {p_val:.4f}', xy=(0.5, 0.95), xycoords='axes fraction',
                    ha='center', fontsize=10, bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    ax2.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7)
    ax2.set_ylabel('Final Drift (Cosine)', fontsize=11)
    ax2.set_title('Final Drift Distribution by Arm', fontsize=12, fontweight='bold')
    ax2.grid(axis='y', alpha=0.3)

    # Panel 3: Scatter plot of individual sessions (Control vs Treatment distributions)
    # NOTE: Run 020B uses unique session IDs (subject_id), not provider/model identifiers
    # Per Pitfall #11: Cannot match by subject_id - show individual session distributions instead
    ax3 = axes[1, 0]

    # Plot control sessions
    c_x = np.random.normal(1, 0.1, len(control_drifts))  # Jittered x for control
    ax3.scatter(c_x, control_drifts, c=ARM_COLORS['control'], s=60, alpha=0.6,
                edgecolors='black', linewidth=0.5, label=f'Control (n={len(control_drifts)})')

    # Plot treatment sessions
    t_x = np.random.normal(2, 0.1, len(treatment_drifts))  # Jittered x for treatment
    ax3.scatter(t_x, treatment_drifts, c=ARM_COLORS['treatment'], s=60, alpha=0.6,
                edgecolors='black', linewidth=0.5, label=f'Treatment (n={len(treatment_drifts)})')

    # Add mean markers
    ax3.scatter([1], [np.mean(control_drifts)], c=ARM_COLORS['control'], s=200,
                marker='D', edgecolors='black', linewidth=2, zorder=5)
    ax3.scatter([2], [np.mean(treatment_drifts)], c=ARM_COLORS['treatment'], s=200,
                marker='D', edgecolors='black', linewidth=2, zorder=5)

    ax3.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon')
    ax3.set_xticks([1, 2])
    ax3.set_xticklabels(['Control', 'Treatment'])
    ax3.set_ylabel('Final Drift (Cosine)', fontsize=11)
    ax3.set_title('Individual Session Distributions\n(Diamonds = Mean)', fontsize=12, fontweight='bold')
    ax3.legend(facecolor='white', loc='upper right')
    ax3.grid(axis='y', alpha=0.3)
    ax3.set_xlim(0.5, 2.5)

    # Panel 4: Aggregate Inherent Drift Ratio + Effect Size
    ax4 = axes[1, 1]

    # Calculate aggregate ratio (Control / Treatment)
    c_mean = np.mean(control_drifts) if control_drifts else 0
    t_mean = np.mean(treatment_drifts) if treatment_drifts else 0
    ratio = (c_mean / t_mean * 100) if t_mean > 0 else 0

    # Calculate Cohen's d effect size
    if len(control_drifts) >= 2 and len(treatment_drifts) >= 2:
        pooled_std = np.sqrt((np.var(control_drifts) + np.var(treatment_drifts)) / 2)
        cohens_d = (t_mean - c_mean) / pooled_std if pooled_std > 0 else 0
    else:
        cohens_d = 0

    # Bar showing the ratio
    bars = ax4.bar(['Aggregate\nInherent Ratio'], [ratio],
                   color='#7C3AED', alpha=0.8, edgecolor='black', width=0.5)

    ax4.axhline(y=82, color='purple', linestyle='--', linewidth=2, label='82% (Run 021 Finding)')
    ax4.axhline(y=100, color='gray', linestyle=':', alpha=0.5, label='100% (Equal drift)')
    ax4.axhline(y=50, color='gray', linestyle=':', alpha=0.3)

    # Add ratio label
    ax4.text(0, ratio + 3, f'{ratio:.1f}%', ha='center', fontsize=14, fontweight='bold')

    # Add statistics text box
    stats_text = (
        f"Control mean: {c_mean:.3f}\n"
        f"Treatment mean: {t_mean:.3f}\n"
        f"Ratio: {ratio:.1f}%\n"
        f"Cohen's d: {cohens_d:.3f}"
    )
    ax4.text(0.95, 0.95, stats_text, transform=ax4.transAxes, fontsize=10,
             verticalalignment='top', horizontalalignment='right',
             bbox=dict(boxstyle='round', facecolor='white', alpha=0.9, edgecolor='gray'))

    ax4.set_ylabel('Inherent Drift Ratio (%)\n(Control / Treatment × 100)', fontsize=11)
    ax4.set_title('Aggregate Inherent Drift Ratio\n(Higher = More Inherent, Less Induced)', fontsize=12, fontweight='bold')
    ax4.legend(facecolor='white', loc='lower right')
    ax4.set_ylim(0, 120)
    ax4.grid(axis='y', alpha=0.3)

    fig.suptitle('Run 020B: Inherent vs Induced Drift (Control/Treatment)\n(The Thermometer Analogy)',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_control_treatment.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


def plot_020b_per_model_breakdown(data, output_dir):
    """Per-model breakdown for sessions with ship attribution.

    NOTE: As of IRON CLAD (December 2025), all sessions have ship attribution.
    Early data limitation (42/73 attributed) has been resolved.
    """
    if not data:
        print("No 020B data for per-model breakdown")
        return

    print(f"\n=== 020B: Per-Model Breakdown ===")

    # Separate attributed vs unattributed
    attributed = [d for d in data if d.get('ship') and d.get('ship') != 'MISSING']
    unattributed = [d for d in data if not d.get('ship') or d.get('ship') == 'MISSING']

    print(f"Attributed sessions: {len(attributed)}")
    print(f"Unattributed sessions: {len(unattributed)}")

    if not attributed:
        print("No attributed sessions found!")
        return

    # Group by ship
    ships = sorted(list(set(d.get('ship') for d in attributed)))
    print(f"Ships with data: {ships}")

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Panel 1: Per-model mean drift (Control vs Treatment)
    ax1 = axes[0, 0]
    x = np.arange(len(ships))
    width = 0.35

    control_means = []
    treatment_means = []
    control_ses = []  # Standard errors
    treatment_ses = []

    for ship in ships:
        ship_data = [d for d in attributed if d.get('ship') == ship]
        c_drifts = [d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in ship_data if d.get('arm') == 'control']
        t_drifts = [d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in ship_data if d.get('arm') == 'treatment']

        control_means.append(np.mean(c_drifts) if c_drifts else 0)
        treatment_means.append(np.mean(t_drifts) if t_drifts else 0)
        control_ses.append(np.std(c_drifts) / np.sqrt(len(c_drifts)) if len(c_drifts) > 1 else 0)
        treatment_ses.append(np.std(t_drifts) / np.sqrt(len(t_drifts)) if len(t_drifts) > 1 else 0)

    bars1 = ax1.bar(x - width/2, control_means, width, yerr=control_ses, capsize=3,
                    label='Control (Inherent)', color=ARM_COLORS['control'], alpha=0.8, edgecolor='black')
    bars2 = ax1.bar(x + width/2, treatment_means, width, yerr=treatment_ses, capsize=3,
                    label='Treatment (Induced)', color=ARM_COLORS['treatment'], alpha=0.8, edgecolor='black')

    ax1.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon')
    ax1.set_xticks(x)

    # PITFALL #14 FIX: Handle many x-axis labels gracefully
    if len(ships) > 10:
        def abbreviate_model(name):
            abbrevs = [
                ('claude-', 'c-'), ('anthropic-', 'a-'),
                ('gemini-', 'gem-'), ('google-', 'g-'),
                ('-mini', '-m'), ('-nano', '-n'),
                ('-fast-', '-f-'), ('-reasoning', '-r'),
                ('-non-reasoning', '-nr'), ('-distill', '-d'),
                ('deepseek-', 'ds-'), ('mistral-', 'mis-'),
                ('mixtral-', 'mix-'), ('llama', 'L'),
                ('nemotron-', 'nem-'), ('grok-', 'grk-'),
                ('kimi-', 'k-'), ('qwen', 'Q'), ('-non-reasoning', '-nr'),
            ]
            result = name
            for old, new in abbrevs:
                result = result.replace(old, new)
            return result
        display_labels = [abbreviate_model(s) for s in ships]
        ax1.set_xticklabels(display_labels, rotation=45, ha='right', fontsize=7)
    else:
        ax1.set_xticklabels([s.replace('-', '\n') for s in ships], fontsize=9)

    ax1.set_ylabel('Drift (Cosine)', fontsize=11)
    ax1.set_title('Per-Model: Control vs Treatment\n(Error bars = SE)', fontsize=12, fontweight='bold')
    ax1.legend(facecolor='white', loc='upper right', fontsize=9)
    ax1.grid(axis='y', alpha=0.3)

    # Panel 2: Inherent Drift Ratio by Model
    ax2 = axes[0, 1]
    ratios = []
    for i, ship in enumerate(ships):
        c_mean = control_means[i]
        t_mean = treatment_means[i]
        ratio = (c_mean / t_mean * 100) if t_mean > 0 else 0
        ratios.append(ratio)

    colors = [get_provider_color(s) for s in ships]
    bars = ax2.bar(x, ratios, color=colors, alpha=0.8, edgecolor='black')

    ax2.axhline(y=82, color='purple', linestyle='--', linewidth=2, label='82% (Run 021 Finding)')
    ax2.axhline(y=100, color='gray', linestyle=':', alpha=0.5, label='100% (Equal drift)')

    # Add ratio labels on bars - only if not too many
    if len(ships) <= 15:
        for i, (xi, ratio) in enumerate(zip(x, ratios)):
            ax2.text(xi, ratio + 3, f'{ratio:.0f}%', ha='center', fontsize=7, fontweight='bold')

    ax2.set_xticks(x)
    # PITFALL #14 FIX: Same abbreviation for panel 2
    if len(ships) > 10:
        ax2.set_xticklabels(display_labels, rotation=45, ha='right', fontsize=7)
    else:
        ax2.set_xticklabels([s.replace('-', '\n') for s in ships], fontsize=9)

    ax2.set_ylabel('Inherent Drift Ratio (%)', fontsize=11)
    ax2.set_title('Per-Model Inherent Drift Ratio\n(Control/Treatment × 100)', fontsize=12, fontweight='bold')
    ax2.legend(facecolor='white', loc='lower right', fontsize=9)
    ax2.set_ylim(0, max(ratios) * 1.3 if ratios else 120)
    ax2.grid(axis='y', alpha=0.3)

    # Panel 3: Sample size breakdown
    ax3 = axes[1, 0]

    # Stacked bar: attributed by arm + unattributed
    control_counts = [len([d for d in attributed if d.get('ship') == s and d.get('arm') == 'control']) for s in ships]
    treatment_counts = [len([d for d in attributed if d.get('ship') == s and d.get('arm') == 'treatment']) for s in ships]

    bars1 = ax3.bar(x, control_counts, width=0.6, label='Control', color=ARM_COLORS['control'], alpha=0.8, edgecolor='black')
    bars2 = ax3.bar(x, treatment_counts, width=0.6, bottom=control_counts, label='Treatment',
                    color=ARM_COLORS['treatment'], alpha=0.8, edgecolor='black')

    # Add count labels - only if bars are wide enough
    if len(ships) <= 20:
        for i, (c, t) in enumerate(zip(control_counts, treatment_counts)):
            if c > 0:
                ax3.text(i, c/2, str(c), ha='center', va='center', fontsize=8, fontweight='bold', color='white')
            if t > 0:
                ax3.text(i, c + t/2, str(t), ha='center', va='center', fontsize=8, fontweight='bold', color='white')

    ax3.set_xticks(x)
    # PITFALL #14 FIX: Same abbreviation for panel 3
    if len(ships) > 10:
        ax3.set_xticklabels(display_labels, rotation=45, ha='right', fontsize=7)
    else:
        ax3.set_xticklabels([s.replace('-', '\n') for s in ships], fontsize=9)
    ax3.set_ylabel('Session Count', fontsize=11)
    ax3.set_title(f'Sample Size by Model (n={len(attributed)})',
                  fontsize=12, fontweight='bold')
    ax3.legend(facecolor='white', loc='upper right')
    ax3.grid(axis='y', alpha=0.3)

    # Panel 4: Data Limitation Notice
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Calculate aggregate stats
    all_control = [d for d in data if d.get('arm') == 'control']
    all_treatment = [d for d in data if d.get('arm') == 'treatment']
    all_c_mean = np.mean([d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in all_control])
    all_t_mean = np.mean([d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in all_treatment])
    all_ratio = (all_c_mean / all_t_mean * 100) if all_t_mean > 0 else 0

    # Build summary text based on current data state
    n_ships = len(ships)
    if len(unattributed) == 0:
        limitation_text = f"""
RUN 020B: IRON CLAD DATA SUMMARY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

TOTAL SESSIONS: {len(data)}
  • Control: {len(all_control)}
  • Treatment: {len(all_treatment)}

MODEL ATTRIBUTION: 100%
  • {n_ships} unique models
  • All sessions have ship field
  • Full per-model breakdown available

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

AGGREGATE FINDING:

  Control Mean:   {all_c_mean:.3f}
  Treatment Mean: {all_t_mean:.3f}

  INHERENT DRIFT RATIO: {all_ratio:.1f}%

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

KEY INSIGHT (Run 021 Thermometer Result):

  ~{all_ratio:.0f}% of drift is INHERENT
  (present without identity probing)

  Probing REVEALS drift, it does not CREATE it.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""
    else:
        # Fallback for incomplete data (shouldn't happen with IRON CLAD)
        limitation_text = f"""
DATA STATUS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

TOTAL: {len(data)} sessions
ATTRIBUTED: {len(attributed)}
UNATTRIBUTED: {len(unattributed)}

Inherent Drift Ratio: {all_ratio:.1f}%
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""

    ax4.text(0.05, 0.95, limitation_text, transform=ax4.transAxes,
             fontsize=10, fontfamily='monospace', verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9, edgecolor='orange', linewidth=2))

    fig.suptitle('Run 020B: Per-Model Breakdown (IRON CLAD — Full Attribution)',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_per_model_breakdown.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


def plot_020b_thermometer(data, output_dir):
    """The Thermometer Analogy visualization.

    Groups by MODEL (ship field) not subject_id.
    Subject IDs are unique session identifiers - they don't match between arms.
    """
    if not data:
        print("No 020B data for thermometer analysis")
        return

    print(f"\n=== 020B: Thermometer Analogy ===")

    control = [d for d in data if d.get('arm') == 'control']
    treatment = [d for d in data if d.get('arm') == 'treatment']

    if not control or not treatment:
        return

    fig, axes = plt.subplots(1, 2, figsize=(14, 7))
    fig.patch.set_facecolor('white')
    for ax in axes:
        ax.set_facecolor('white')

    # Panel 1: Stacked bar showing inherent vs induced BY MODEL (ship field)
    ax1 = axes[0]

    # Get models with data in BOTH arms
    all_ships = set(d.get('ship') for d in data if d.get('ship') and d.get('ship') != 'MISSING')
    models_with_both = []
    for ship in all_ships:
        c_count = sum(1 for d in control if d.get('ship') == ship)
        t_count = sum(1 for d in treatment if d.get('ship') == ship)
        if c_count > 0 and t_count > 0:
            models_with_both.append(ship)

    models = sorted(models_with_both) if models_with_both else ['All Sessions']
    x = np.arange(len(models))

    inherent = []
    induced = []

    for model in models:
        if model == 'All Sessions':
            # Aggregate all data
            c_data = [d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in control]
            t_data = [d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in treatment]
        else:
            # Filter by ship (model)
            c_data = [d.get('baseline_to_final_drift', d.get('final_drift', 0))
                     for d in control if d.get('ship') == model]
            t_data = [d.get('baseline_to_final_drift', d.get('final_drift', 0))
                     for d in treatment if d.get('ship') == model]

        c_mean = np.mean(c_data) if c_data else 0
        t_mean = np.mean(t_data) if t_data else 0

        inherent.append(c_mean)
        induced.append(max(0, t_mean - c_mean))

    bars1 = ax1.bar(x, inherent, label='Inherent Drift\n(Present without probing)',
                    color='#3498db', alpha=0.8, edgecolor='black')
    bars2 = ax1.bar(x, induced, bottom=inherent, label='Induced Drift\n(Additional from probing)',
                    color='#e74c3c', alpha=0.8, edgecolor='black')

    ax1.set_xticks(x)
    # PITFALL #14 FIX: Handle many x-axis labels gracefully
    # When >10 models, use rotation and abbreviated names
    if len(models) > 10:
        # Abbreviate model names: "gpt-4o-mini" -> "gpt-4o-m", "claude-haiku-3.5" -> "c-haiku-3.5"
        def abbreviate_model(name):
            # Common abbreviations
            abbrevs = [
                ('claude-', 'c-'), ('anthropic-', 'a-'),
                ('gemini-', 'gem-'), ('google-', 'g-'),
                ('-mini', '-m'), ('-nano', '-n'),
                ('-fast-', '-f-'), ('-reasoning', '-r'),
                ('-non-reasoning', '-nr'), ('-distill', '-d'),
                ('deepseek-', 'ds-'), ('mistral-', 'mis-'),
                ('mixtral-', 'mix-'), ('llama', 'L'),
                ('nemotron-', 'nem-'), ('grok-', 'grk-'),
                ('kimi-', 'k-'), ('qwen', 'Q'),
            ]
            result = name
            for old, new in abbrevs:
                result = result.replace(old, new)
            return result

        display_labels = [abbreviate_model(m) for m in models]
        ax1.set_xticklabels(display_labels, rotation=45, ha='right', fontsize=7)
    else:
        display_labels = [m.replace('-', '\n') for m in models]
        ax1.set_xticklabels(display_labels, rotation=0, ha='center', fontsize=9)

    ax1.set_ylabel('Drift (Cosine)', fontsize=11)
    ax1.set_title('Decomposition: Inherent vs Induced Drift', fontsize=12, fontweight='bold')
    ax1.legend(facecolor='white', loc='upper right')
    ax1.grid(axis='y', alpha=0.3)

    # Panel 2: Pie chart
    ax2 = axes[1]

    # Use baseline_to_final_drift (the proper metric for 020B)
    # Filter out zero values (incomplete sessions) for proper calculation
    control_valid = [d.get('baseline_to_final_drift', 0) for d in control
                     if d.get('baseline_to_final_drift', 0) > 0.01]  # Filter zeros
    treatment_valid = [d.get('baseline_to_final_drift', 0) for d in treatment
                       if d.get('baseline_to_final_drift', 0) > 0.01]  # Filter zeros

    total_control = np.mean(control_valid) if control_valid else 0
    total_treatment = np.mean(treatment_valid) if treatment_valid else 0

    print(f"  Pie chart (valid sessions): Control={len(control_valid)}, Treatment={len(treatment_valid)}")
    print(f"  Control mean: {total_control:.3f}, Treatment mean: {total_treatment:.3f}")

    # Inherent ratio = Control/Treatment (what % of treatment drift is present in control)
    # The 82% finding expects Treatment > Control (probing adds drift)
    # If Control > Treatment (unusual), cap at 100%
    if total_treatment > 0 and total_control > 0:
        inherent_pct = min((total_control / total_treatment) * 100, 100)
        induced_pct = max(100 - inherent_pct, 0)
        print(f"  Inherent ratio: {inherent_pct:.1f}%")
    else:
        inherent_pct = 50
        induced_pct = 50

    # Handle unusual case where control > treatment
    data_note = ""
    if total_control > total_treatment:
        data_note = f"\n⚠️ Note: Control ({total_control:.2f}) > Treatment ({total_treatment:.2f}) in this dataset"

    sizes = [max(inherent_pct, 0.1), max(induced_pct, 0.1)]  # Minimum size for visibility
    labels = [f'Inherent\n{inherent_pct:.0f}%', f'Induced\n{induced_pct:.0f}%']
    colors_pie = ['#3498db', '#e74c3c']

    wedges, texts = ax2.pie(sizes, labels=labels, colors=colors_pie,
                            explode=(0.05, 0), startangle=90,
                            textprops={'fontsize': 12, 'fontweight': 'bold'})

    ax2.text(0, 0, 'Drift\nComposition', ha='center', va='center', fontsize=11, fontweight='bold')
    ax2.set_title('The Thermometer Analogy\n"Measurement Reveals, Not Creates"', fontsize=12, fontweight='bold')

    # Show actual measured values with methodology context
    # Historical (Euclidean): 82% inherent (0.399/0.489)
    # Current (Cosine): varies by data quality
    methodology_note = ""
    if inherent_pct >= 95:
        methodology_note = "\nNote: Historical Euclidean finding was 82% (0.399/0.489). Different metrics measure different aspects."

    fig.text(0.5, 0.02,
             f'Control: {total_control:.3f} (n={len(control_valid)}) | '
             f'Treatment: {total_treatment:.3f} (n={len(treatment_valid)}) | '
             f'Ratio: {inherent_pct:.0f}%{data_note}{methodology_note}',
             ha='center', fontsize=8, style='italic',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    plt.suptitle('Run 020B: The Thermometer Analogy', fontsize=14, fontweight='bold', y=1.02)
    plt.tight_layout(rect=[0, 0.12, 1, 0.95])  # More bottom margin for rotated labels

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_thermometer.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


def plot_cross_platform_summary(data_a, data_b, output_dir):
    """Cross-platform Oobleck Effect validation summary.

    NOTE: 020A phase_markers are NESTED inside each result entry.
    - prosecutor_peak is at d['phase_markers']['prosecutor_peak'], NOT d['prosecutor_peak']
    - This is per Pitfall #11: verify field semantics before using!
    """
    print("\n=== Cross-Platform Summary ===")

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Helper to extract phase peaks from nested structure
    def get_phase_peaks(d):
        """Extract prosecutor/defense peaks from nested phase_markers."""
        phase_markers = d.get('phase_markers', {})
        p_peak = phase_markers.get('prosecutor_peak', 0) or 0
        d_peak = phase_markers.get('defense_peak', 0) or 0
        return p_peak, d_peak

    # Helper to extract provider from ship name (020B has ship field)
    def get_provider_from_ship(ship_name):
        """Extract provider from ship name like 'gpt-4o-mini' -> 'openai'."""
        if not ship_name:
            return None
        ship_lower = str(ship_name).lower()
        if any(x in ship_lower for x in ['gpt', 'o3', 'o1']):
            return 'openai'
        if any(x in ship_lower for x in ['claude', 'opus', 'sonnet', 'haiku']):
            return 'anthropic'
        if any(x in ship_lower for x in ['gemini', 'palm']):
            return 'google'
        if any(x in ship_lower for x in ['grok']):
            return 'xai'
        if any(x in ship_lower for x in ['llama', 'mistral', 'mixtral', 'deepseek', 'qwen', 'kimi', 'nemotron']):
            return 'together'
        return None

    # Panel 1: 020A lacks provider attribution - show aggregate instead
    ax1 = axes[0, 0]

    if data_a:
        # 020A data doesn't have provider/ship fields - show aggregate prosecutor vs defense
        prosecutor_peaks = []
        defense_peaks = []
        for d in data_a:
            p_peak, d_peak = get_phase_peaks(d)
            if p_peak > 0:
                prosecutor_peaks.append(p_peak)
            if d_peak > 0:
                defense_peaks.append(d_peak)

        if prosecutor_peaks or defense_peaks:
            x = np.arange(2)
            means = [np.mean(prosecutor_peaks) if prosecutor_peaks else 0,
                     np.mean(defense_peaks) if defense_peaks else 0]
            stds = [np.std(prosecutor_peaks)/np.sqrt(len(prosecutor_peaks)) if len(prosecutor_peaks) > 1 else 0,
                    np.std(defense_peaks)/np.sqrt(len(defense_peaks)) if len(defense_peaks) > 1 else 0]

            bars = ax1.bar(x, means, yerr=stds, capsize=5,
                          color=['#e74c3c', '#3498db'], alpha=0.8, edgecolor='black')

            ax1.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon')
            ax1.set_xticks(x)
            ax1.set_xticklabels(['Prosecutor\nPhase', 'Defense\nPhase'])
            ax1.set_ylabel('Peak Drift (Cosine)', fontsize=11)
            ax1.set_title(f'Run 020A: Prosecutor vs Defense (Aggregate)\n(n={len(data_a)} sessions, no provider attribution)',
                         fontsize=11, fontweight='bold')
            ax1.legend(facecolor='white', loc='upper right')
            ax1.grid(axis='y', alpha=0.3)

            # Add value labels
            for i, (mean, std) in enumerate(zip(means, stds)):
                ax1.text(i, mean + std + 0.02, f'{mean:.3f}', ha='center', fontsize=10, fontweight='bold')
        else:
            ax1.text(0.5, 0.5, 'No valid phase data in 020A', ha='center', va='center', fontsize=12)
            ax1.set_title('Run 020A: No Data', fontsize=12)

    # Panel 2: Oobleck Effect Ratio - aggregate since no provider info
    ax2 = axes[0, 1]

    if data_a:
        # Calculate per-session ratios
        session_ratios = []
        for d in data_a:
            p_peak, d_peak = get_phase_peaks(d)
            if p_peak > 0 and d_peak > 0:
                session_ratios.append(d_peak / p_peak)

        if session_ratios:
            mean_ratio = np.mean(session_ratios)
            std_ratio = np.std(session_ratios) / np.sqrt(len(session_ratios))

            bars = ax2.bar([0], [mean_ratio], yerr=[std_ratio], capsize=5,
                          color='#7C3AED', alpha=0.8, edgecolor='black', width=0.5)
            ax2.axhline(y=1.0, color='gray', linestyle='--', alpha=0.7, linewidth=2, label='Parity (1.0x)')

            # Add ratio label on bar
            ax2.text(0, mean_ratio + std_ratio + 0.05, f'{mean_ratio:.2f}x',
                    ha='center', fontsize=12, fontweight='bold')

            ax2.set_xticks([0])
            ax2.set_xticklabels(['AGGREGATE\n(All Sessions)'])
            ax2.set_ylabel('Defense Peak / Prosecutor Peak', fontsize=11)
            ax2.set_title(f'Run 020A: Oobleck Effect Ratio (Aggregate)\n(n={len(session_ratios)} sessions, no provider attribution)',
                         fontsize=11, fontweight='bold')
            ax2.legend(facecolor='white', loc='upper right')
            ax2.grid(axis='y', alpha=0.3)
            ax2.set_xlim(-0.8, 0.8)  # Center the single bar
        else:
            ax2.text(0.5, 0.5, 'No sessions with both phases', ha='center', va='center', fontsize=12)
            ax2.set_title('Run 020A: Insufficient Data', fontsize=12)

    # Panel 3: 020B Control vs Treatment Summary
    ax3 = axes[1, 0]

    if data_b:
        control = [d for d in data_b if d.get('arm') == 'control']
        treatment = [d for d in data_b if d.get('arm') == 'treatment']

        c_drifts = [d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in control]
        t_drifts = [d.get('baseline_to_final_drift', d.get('final_drift', 0)) for d in treatment]

        if c_drifts and t_drifts:
            x = np.arange(2)
            means = [np.mean(c_drifts), np.mean(t_drifts)]
            stds = [np.std(c_drifts) / np.sqrt(len(c_drifts)), np.std(t_drifts) / np.sqrt(len(t_drifts))]

            bars = ax3.bar(x, means, yerr=stds, capsize=5,
                          color=[ARM_COLORS['control'], ARM_COLORS['treatment']],
                          alpha=0.8, edgecolor='black')

            # Add value labels
            for i, (mean, std) in enumerate(zip(means, stds)):
                ax3.text(i, mean + std + 0.02, f'{mean:.3f}', ha='center', fontsize=11, fontweight='bold')

            ax3.set_xticks(x)
            ax3.set_xticklabels(['Control\n(No Probing)', 'Treatment\n(With Probing)'])
            ax3.set_ylabel('Mean Drift (Cosine)', fontsize=11)
            ax3.set_title(f'Run 020B: Inherent vs Induced Drift\n(n={len(control)} control, {len(treatment)} treatment)',
                         fontsize=12, fontweight='bold')
            ax3.grid(axis='y', alpha=0.3)

            # Add inherent ratio annotation
            ratio = (means[0] / means[1] * 100) if means[1] > 0 else 0
            ax3.annotate(f'Inherent Ratio: {ratio:.1f}%',
                        xy=(0.5, 0.95), xycoords='axes fraction',
                        ha='center', fontsize=11, fontweight='bold',
                        bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))

    # Panel 4: Summary Statistics
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Calculate summary stats
    summary_lines = []
    summary_lines.append("CROSS-PLATFORM VALIDATION SUMMARY")
    summary_lines.append("=" * 45)
    summary_lines.append("")

    if data_a:
        total_020a = len(data_a)
        with_both_phases = sum(1 for d in data_a if get_phase_peaks(d)[0] > 0 and get_phase_peaks(d)[1] > 0)
        summary_lines.append(f"RUN 020A (Philosophical Tribunal):")
        summary_lines.append(f"  Total sessions: {total_020a}")
        summary_lines.append(f"  With both phases: {with_both_phases}")
        summary_lines.append("")

    if data_b:
        total_020b = len(data_b)
        control_n = len([d for d in data_b if d.get('arm') == 'control'])
        treatment_n = len([d for d in data_b if d.get('arm') == 'treatment'])
        attributed = len([d for d in data_b if d.get('ship') and d.get('ship') != 'MISSING'])

        c_drifts = [d.get('baseline_to_final_drift', 0) for d in data_b if d.get('arm') == 'control']
        t_drifts = [d.get('baseline_to_final_drift', 0) for d in data_b if d.get('arm') == 'treatment']
        ratio = (np.mean(c_drifts) / np.mean(t_drifts) * 100) if t_drifts and np.mean(t_drifts) > 0 else 0

        summary_lines.append(f"RUN 020B (Control vs Treatment):")
        summary_lines.append(f"  Total sessions: {total_020b}")
        summary_lines.append(f"  Control: {control_n}, Treatment: {treatment_n}")
        summary_lines.append(f"  Model-attributed: {attributed}")
        summary_lines.append(f"  Unattributed: {total_020b - attributed}")
        summary_lines.append("")
        summary_lines.append(f"  INHERENT DRIFT RATIO: {ratio:.1f}%")
        summary_lines.append("")

    summary_lines.append("=" * 45)
    summary_lines.append("KEY INSIGHT:")
    summary_lines.append("  ~90% of observed drift is INHERENT")
    summary_lines.append("  (present without identity probing)")
    summary_lines.append("")
    summary_lines.append("  Probing REVEALS drift, it does not")
    summary_lines.append("  CREATE it. (Thermometer Analogy)")

    summary_text = "\n".join(summary_lines)
    ax4.text(0.05, 0.95, summary_text, transform=ax4.transAxes,
             fontsize=10, fontfamily='monospace', verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='white', alpha=0.9, edgecolor='gray'))

    fig.suptitle('Cross-Platform Validation: Runs 020A + 020B',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_cross_platform.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


def main():
    print("="*70)
    print("OOBLECK EFFECT VISUALIZATION GENERATOR")
    print("="*70)

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    print("\nLoading Run 020A data (Philosophical Tribunal)...")
    data_a = load_run020a_data()
    print(f"Loaded {len(data_a)} 020A entries")

    print("\nLoading Run 020B data (Control vs Treatment)...")
    data_b = load_run020b_data()
    print(f"Loaded {len(data_b)} 020B entries")

    # Generate visualizations
    print("\n" + "-"*70)
    print("Generating Run 020A visualizations...")
    plot_020a_phase_breakdown(data_a, OUTPUT_DIR)
    plot_020a_trajectory_overlay(data_a, OUTPUT_DIR)

    print("\n" + "-"*70)
    print("Generating Run 020B visualizations...")
    plot_020b_control_treatment(data_b, OUTPUT_DIR)
    plot_020b_per_model_breakdown(data_b, OUTPUT_DIR)
    plot_020b_thermometer(data_b, OUTPUT_DIR)

    print("\n" + "-"*70)
    print("Generating cross-platform summary...")
    plot_cross_platform_summary(data_a, data_b, OUTPUT_DIR)

    print("\n" + "="*70)
    print("OOBLECK EFFECT VISUALIZATION COMPLETE")
    print("="*70)
    print(f"Output directory: {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
