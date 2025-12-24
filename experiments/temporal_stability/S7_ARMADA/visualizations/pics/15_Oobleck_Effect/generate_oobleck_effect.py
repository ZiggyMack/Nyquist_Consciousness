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

    # Panel 1: Grouped bar chart - Prosecutor vs Defense by provider
    ax1 = axes[0, 0]
    providers = sorted(list(set(e['provider'] for e in entries)))
    provider_data = {p: {'prosecutor': [], 'defense': []} for p in providers}

    for e in entries:
        provider_data[e['provider']]['prosecutor'].append(e['prosecutor'])
        provider_data[e['provider']]['defense'].append(e['defense'])

    x = np.arange(len(providers))
    width = 0.35

    p_means = [np.mean(provider_data[p]['prosecutor']) if provider_data[p]['prosecutor'] else 0 for p in providers]
    d_means = [np.mean(provider_data[p]['defense']) if provider_data[p]['defense'] else 0 for p in providers]

    bars1 = ax1.bar(x - width/2, p_means, width, label='Prosecutor Phase',
                    color='#e74c3c', alpha=0.8, edgecolor='black')
    bars2 = ax1.bar(x + width/2, d_means, width, label='Defense Phase',
                    color='#3498db', alpha=0.8, edgecolor='black')

    ax1.axhline(y=WARNING_THRESHOLD, color='#f39c12', linestyle='--', alpha=0.7, label='Warning (0.60)')
    ax1.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon (0.80)')

    ax1.set_xlabel('Provider', fontsize=11)
    ax1.set_ylabel('Peak Drift (Cosine)', fontsize=11)
    ax1.set_title('Prosecutor vs Defense Peak Drift by Provider', fontsize=12, fontweight='bold')
    ax1.set_xticks(x)
    ax1.set_xticklabels([p.upper() for p in providers], rotation=45, ha='right')
    ax1.legend(loc='upper right', facecolor='white')
    ax1.grid(axis='y', alpha=0.3)

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

    # Panel 3: Provider-level scatter
    ax3 = axes[1, 0]
    providers = set(d.get('subject_id', d.get('model', 'unknown')) for d in data)

    for prov in providers:
        c_data = [d for d in control if d.get('subject_id', d.get('model')) == prov]
        t_data = [d for d in treatment if d.get('subject_id', d.get('model')) == prov]

        if c_data and t_data:
            c_mean = np.mean([d.get('final_drift', d.get('drift', 0)) for d in c_data])
            t_mean = np.mean([d.get('final_drift', d.get('drift', 0)) for d in t_data])

            color = get_provider_color(prov)
            ax3.scatter([c_mean], [t_mean], c=[color], s=150, edgecolors='black', linewidth=1)
            ax3.annotate(str(prov)[:15], (c_mean, t_mean), textcoords="offset points",
                        xytext=(5, 5), fontsize=9)

    max_val = max(max(control_drifts + treatment_drifts, default=1), 2.5)
    ax3.plot([0, max_val], [0, max_val], 'k--', alpha=0.3, label='Equal drift')

    ax3.set_xlabel('Control Drift (No Probing)', fontsize=11)
    ax3.set_ylabel('Treatment Drift (With Probing)', fontsize=11)
    ax3.set_title('Provider-Level Comparison', fontsize=12, fontweight='bold')
    ax3.legend(facecolor='white')
    ax3.grid(alpha=0.3)

    # Panel 4: Inherent drift ratio
    ax4 = axes[1, 1]

    ratios = []
    provider_labels = []
    for prov in providers:
        c_data = [d.get('final_drift', d.get('drift', 0)) for d in control if d.get('subject_id', d.get('model')) == prov]
        t_data = [d.get('final_drift', d.get('drift', 0)) for d in treatment if d.get('subject_id', d.get('model')) == prov]

        if c_data and t_data:
            c_mean = np.mean(c_data)
            t_mean = np.mean(t_data)
            if t_mean > 0:
                ratio = c_mean / t_mean * 100
                ratios.append(ratio)
                provider_labels.append(str(prov)[:15])

    if ratios:
        colors = [get_provider_color(p) for p in provider_labels]
        bars = ax4.bar(provider_labels, ratios, color=colors, alpha=0.8, edgecolor='black')

        ax4.axhline(y=82, color='purple', linestyle='--', linewidth=2, label='82% (Run 018 Finding)')
        ax4.axhline(y=50, color='gray', linestyle=':', alpha=0.5, label='50% reference')

        for bar, ratio in zip(bars, ratios):
            ax4.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 2,
                    f'{ratio:.0f}%', ha='center', fontsize=10)

        ax4.set_ylabel('Inherent Drift Ratio (%)\n(Control / Treatment × 100)', fontsize=11)
        ax4.set_title('Inherent Drift Ratio by Provider\n(Higher = More Inherent, Less Induced)', fontsize=12, fontweight='bold')
        ax4.legend(facecolor='white')
        ax4.set_ylim(0, 120)
        ax4.tick_params(axis='x', rotation=45)

    ax4.grid(axis='y', alpha=0.3)

    fig.suptitle('Run 020B: Inherent vs Induced Drift (Control/Treatment)\n(The Thermometer Analogy)',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_control_treatment.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


def plot_020b_thermometer(data, output_dir):
    """The Thermometer Analogy visualization."""
    if not data:
        print("No 020B data for thermometer analysis")
        return

    print(f"\n=== 020B: Thermometer Analogy ===")

    control = [d for d in data if d.get('arm') == 'control']
    treatment = [d for d in data if d.get('arm') == 'treatment']

    if not control or not treatment:
        return

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    fig.patch.set_facecolor('white')
    for ax in axes:
        ax.set_facecolor('white')

    # Panel 1: Stacked bar showing inherent vs induced
    ax1 = axes[0]

    providers = list(set(d.get('subject_id', d.get('model', 'unknown')) for d in data))
    x = np.arange(len(providers))

    inherent = []
    induced = []

    for prov in providers:
        c_data = [d.get('final_drift', d.get('drift', 0)) for d in control if d.get('subject_id', d.get('model')) == prov]
        t_data = [d.get('final_drift', d.get('drift', 0)) for d in treatment if d.get('subject_id', d.get('model')) == prov]

        c_mean = np.mean(c_data) if c_data else 0
        t_mean = np.mean(t_data) if t_data else 0

        inherent.append(c_mean)
        induced.append(max(0, t_mean - c_mean))

    bars1 = ax1.bar(x, inherent, label='Inherent Drift\n(Present without probing)',
                    color='#3498db', alpha=0.8, edgecolor='black')
    bars2 = ax1.bar(x, induced, bottom=inherent, label='Induced Drift\n(Additional from probing)',
                    color='#e74c3c', alpha=0.8, edgecolor='black')

    ax1.set_xticks(x)
    ax1.set_xticklabels([str(p)[:12] for p in providers], rotation=45, ha='right')
    ax1.set_ylabel('Drift (Cosine)', fontsize=11)
    ax1.set_title('Decomposition: Inherent vs Induced Drift', fontsize=12, fontweight='bold')
    ax1.legend(facecolor='white')
    ax1.grid(axis='y', alpha=0.3)

    # Panel 2: Pie chart
    ax2 = axes[1]

    total_control = np.mean([d.get('final_drift', d.get('drift', 0)) for d in control])
    total_treatment = np.mean([d.get('final_drift', d.get('drift', 0)) for d in treatment])

    if total_treatment > 0 and total_control > 0:
        inherent_pct = min((total_control / total_treatment) * 100, 100)
        induced_pct = max(100 - inherent_pct, 0)
    else:
        inherent_pct = 50
        induced_pct = 50

    sizes = [max(inherent_pct, 0), max(induced_pct, 0)]
    labels = [f'Inherent\n{inherent_pct:.0f}%', f'Induced\n{induced_pct:.0f}%']
    colors_pie = ['#3498db', '#e74c3c']

    wedges, texts = ax2.pie(sizes, labels=labels, colors=colors_pie,
                            explode=(0.05, 0), startangle=90,
                            textprops={'fontsize': 12, 'fontweight': 'bold'})

    ax2.text(0, 0, 'Drift\nComposition', ha='center', va='center', fontsize=11, fontweight='bold')
    ax2.set_title('The Thermometer Analogy\n"Measurement Reveals, Not Creates"', fontsize=12, fontweight='bold')

    fig.text(0.5, 0.02,
             f'Like a thermometer that reveals pre-existing temperature, identity probing reveals pre-existing drift.\n'
             f'Overall: {inherent_pct:.0f}% inherent (present without probing) + {induced_pct:.0f}% induced (from probing)',
             ha='center', fontsize=10, style='italic',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    plt.suptitle('Run 020B: The Thermometer Analogy', fontsize=14, fontweight='bold', y=1.02)
    plt.tight_layout(rect=[0, 0.08, 1, 0.95])

    for ext in ['png', 'svg']:
        outfile = output_dir / f'oobleck_thermometer.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


def plot_cross_platform_summary(data_a, data_b, output_dir):
    """Cross-platform Oobleck Effect validation summary."""
    print("\n=== Cross-Platform Summary ===")

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    fig.patch.set_facecolor('white')
    for ax in axes:
        ax.set_facecolor('white')

    # Panel 1: Oobleck Effect Ratio by Architecture (from 020A)
    ax1 = axes[0]

    if data_a:
        entries = []
        for d in data_a:
            p_peak = d.get('prosecutor_peak', 0) or 0
            d_peak = d.get('defense_peak', 0) or 0
            if p_peak > 0 and d_peak > 0:
                ratio = d_peak / p_peak  # Defense/Prosecutor ratio
                entries.append({
                    'model': d.get('subject_id', d.get('model', 'unknown')),
                    'ratio': ratio
                })

        if entries:
            models = list(set(e['model'] for e in entries))
            ratios = [np.mean([e['ratio'] for e in entries if e['model'] == m]) for m in models]
            colors = [get_provider_color(m) for m in models]

            bars = ax1.bar(range(len(models)), ratios, color=colors, alpha=0.8, edgecolor='black')
            ax1.axhline(y=1.0, color='gray', linestyle='--', alpha=0.7, label='Parity (1.0x)')
            ax1.set_xticks(range(len(models)))
            ax1.set_xticklabels([str(m)[:12] for m in models], rotation=45, ha='right')
            ax1.set_ylabel('Defense Peak / Prosecutor Peak', fontsize=11)
            ax1.set_title('Oobleck Effect Ratio by Architecture', fontsize=12, fontweight='bold')
            ax1.legend(facecolor='white')
            ax1.grid(axis='y', alpha=0.3)

    # Panel 2: Defense > Prosecutor by Architecture (bar chart)
    ax2 = axes[1]

    if data_a:
        models = list(set(d.get('subject_id', d.get('model', 'unknown')) for d in data_a))
        prosecutor_means = []
        defense_means = []

        for m in models:
            m_data = [d for d in data_a if d.get('subject_id', d.get('model')) == m]
            p_peaks = [d.get('prosecutor_peak', 0) or 0 for d in m_data]
            d_peaks = [d.get('defense_peak', 0) or 0 for d in m_data]
            prosecutor_means.append(np.mean([p for p in p_peaks if p > 0]) if any(p > 0 for p in p_peaks) else 0)
            defense_means.append(np.mean([d for d in d_peaks if d > 0]) if any(d > 0 for d in d_peaks) else 0)

        x = np.arange(len(models))
        width = 0.35

        bars1 = ax2.bar(x - width/2, prosecutor_means, width, label='Prosecutor',
                        color='#e74c3c', alpha=0.8, edgecolor='black')
        bars2 = ax2.bar(x + width/2, defense_means, width, label='Defense',
                        color='#3498db', alpha=0.8, edgecolor='black')

        ax2.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7, label='Event Horizon')
        ax2.set_xticks(x)
        ax2.set_xticklabels([str(m)[:12] for m in models], rotation=45, ha='right')
        ax2.set_ylabel('Peak Drift (Cosine)', fontsize=11)
        ax2.set_title('Prosecutor vs Defense Peak by Architecture', fontsize=12, fontweight='bold')
        ax2.legend(facecolor='white')
        ax2.grid(axis='y', alpha=0.3)

    fig.suptitle('Cross-Platform Validation Summary: Runs 020A + 020B',
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
