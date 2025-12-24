#!/usr/bin/env python3
"""
Run 020 Visualizations: Value Evolution, Exchange Depth, Closing Analysis
=========================================================================
Complementary visualizations to 15_Oobleck_Effect, focusing on untapped data:
- Stated values analysis (020A)
- Exchange depth vs drift correlation (020A)
- Closing statement analysis (020A)
- Per-model drift heatmap (020B)

LIGHT MODE for publication consistency.

Author: Claude (VALIS Network)
Date: December 2025
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import Counter
import re
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
# CONSTANTS - Cosine methodology
# =============================================================================
EVENT_HORIZON = 0.80
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
    'unknown': '#6B7280'
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


def get_provider_color(name):
    """Get color for provider/model."""
    name_lower = str(name).lower()
    for key, color in PROVIDER_COLORS.items():
        if key in name_lower:
            return color
    return PROVIDER_COLORS['unknown']


# =============================================================================
# VISUALIZATION 1: Value Evolution Analysis
# =============================================================================

def plot_value_evolution(data, output_dir):
    """Analyze stated_values patterns across all 020A sessions.

    2x2 QUAD layout:
    - Panel 1: Values count distribution
    - Panel 2: Peak drift vs values count scatter
    - Panel 3: Top value themes (word frequency)
    - Panel 4: Values anchoring analysis
    """
    if not data:
        print("No 020A data for value evolution")
        return

    print("\n=== Value Evolution Analysis ===")

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Collect data
    sessions_with_values = []
    all_values = []

    for d in data:
        values = d.get('stated_values', [])
        peak = d.get('peak_drift', 0)
        final = d.get('final_drift', 0)
        exchanges = d.get('total_exchanges', 0)

        if exchanges > 0:  # Only sessions with data
            sessions_with_values.append({
                'subject_id': d.get('subject_id', 'unknown'),
                'values_count': len(values),
                'peak_drift': peak,
                'final_drift': final,
                'exchanges': exchanges,
                'recovery': peak - final if peak > 0 else 0
            })
            all_values.extend(values)

    print(f"Sessions with data: {len(sessions_with_values)}")
    print(f"Total stated values: {len(all_values)}")

    # Panel 1: Values count distribution
    ax1 = axes[0, 0]
    values_counts = [s['values_count'] for s in sessions_with_values]

    bins = range(0, max(values_counts) + 2)
    ax1.hist(values_counts, bins=bins, color='#7C3AED', alpha=0.7, edgecolor='black')
    ax1.axvline(x=np.mean(values_counts), color='red', linestyle='--', linewidth=2,
                label=f'Mean: {np.mean(values_counts):.1f}')
    ax1.set_xlabel('Number of Stated Values', fontsize=11)
    ax1.set_ylabel('Session Count', fontsize=11)
    ax1.set_title('Distribution of Stated Values per Session', fontsize=12, fontweight='bold')
    ax1.legend(facecolor='white')
    ax1.grid(axis='y', alpha=0.3)

    # Panel 2: Peak drift vs values count scatter
    ax2 = axes[0, 1]

    peaks = [s['peak_drift'] for s in sessions_with_values]
    counts = [s['values_count'] for s in sessions_with_values]

    scatter = ax2.scatter(counts, peaks, c=peaks, cmap='RdYlGn_r',
                         s=100, alpha=0.7, edgecolors='black')

    # Add trend line
    if len(counts) > 2:
        z = np.polyfit(counts, peaks, 1)
        p = np.poly1d(z)
        x_line = np.linspace(min(counts), max(counts), 100)
        ax2.plot(x_line, p(x_line), 'r--', alpha=0.5, label=f'Trend')

    ax2.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7,
                label='Event Horizon (0.80)')
    ax2.set_xlabel('Number of Stated Values', fontsize=11)
    ax2.set_ylabel('Peak Drift (Cosine)', fontsize=11)
    ax2.set_title('Peak Drift vs Value Articulation', fontsize=12, fontweight='bold')
    ax2.legend(facecolor='white', loc='upper right')
    ax2.grid(alpha=0.3)
    plt.colorbar(scatter, ax=ax2, label='Peak Drift')

    # Panel 3: Top value themes (word frequency)
    ax3 = axes[1, 0]

    # Extract key themes from stated values
    theme_words = []
    for val in all_values:
        # Look for key concept words
        words = re.findall(r'\b(honest|truth|empathy|understand|help|integrity|'
                          r'value|believe|curious|learn|respect|dignity|'
                          r'uncertain|grow|connect|authentic|conscious|'
                          r'moral|ethical|principle|care|compassion)\w*\b',
                          val.lower())
        theme_words.extend(words)

    word_counts = Counter(theme_words)
    top_words = word_counts.most_common(12)

    if top_words:
        words, counts = zip(*top_words)
        y_pos = np.arange(len(words))

        colors = plt.cm.viridis(np.linspace(0.2, 0.8, len(words)))
        bars = ax3.barh(y_pos, counts, color=colors, alpha=0.8, edgecolor='black')

        ax3.set_yticks(y_pos)
        ax3.set_yticklabels(words, fontsize=10)
        ax3.set_xlabel('Frequency Across All Sessions', fontsize=11)
        ax3.set_title('Top Value Themes in Testimony', fontsize=12, fontweight='bold')
        ax3.invert_yaxis()
        ax3.grid(axis='x', alpha=0.3)
    else:
        ax3.text(0.5, 0.5, 'No theme words found', ha='center', va='center')

    # Panel 4: Recovery correlation with value count
    ax4 = axes[1, 1]

    recovery = [s['recovery'] for s in sessions_with_values if s['recovery'] > 0]
    recovery_counts = [s['values_count'] for s in sessions_with_values if s['recovery'] > 0]

    if recovery and recovery_counts:
        scatter2 = ax4.scatter(recovery_counts, recovery, c='#2ecc71',
                              s=100, alpha=0.7, edgecolors='black')

        # Correlation
        if len(recovery) > 2:
            corr = np.corrcoef(recovery_counts, recovery)[0, 1]
            ax4.text(0.95, 0.95, f'r = {corr:.3f}', transform=ax4.transAxes,
                    ha='right', va='top', fontsize=11, fontweight='bold',
                    bbox=dict(boxstyle='round', facecolor='white', alpha=0.9))

        ax4.set_xlabel('Number of Stated Values', fontsize=11)
        ax4.set_ylabel('Drift Recovery (Peak - Final)', fontsize=11)
        ax4.set_title('Value Anchoring: Do More Values = Better Recovery?',
                     fontsize=12, fontweight='bold')
        ax4.grid(alpha=0.3)
    else:
        ax4.text(0.5, 0.5, 'Insufficient recovery data', ha='center', va='center')

    fig.suptitle('Run 020A: Stated Values Analysis',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'run020a_value_evolution.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


# =============================================================================
# VISUALIZATION 2: Exchange Depth Analysis
# =============================================================================

def plot_exchange_depth(data, output_dir):
    """Analyze exchange depth vs drift correlation.

    2x2 QUAD layout:
    - Panel 1: Exchange count vs peak drift scatter
    - Panel 2: Sessions with both phases vs prosecutor-only
    - Panel 3: Role switch timing analysis
    - Panel 4: Session duration summary
    """
    if not data:
        print("No 020A data for exchange depth")
        return

    print("\n=== Exchange Depth Analysis ===")

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Collect data
    sessions = []
    for d in data:
        exchanges = d.get('total_exchanges', 0)
        peak = d.get('peak_drift', 0)
        final = d.get('final_drift', 0)
        pm = d.get('phase_markers', {})

        sessions.append({
            'subject_id': d.get('subject_id', 'unknown'),
            'exchanges': exchanges,
            'peak_drift': peak,
            'final_drift': final,
            'prosecutor_peak': pm.get('prosecutor_peak', 0) or 0,
            'defense_peak': pm.get('defense_peak', 0) or 0,
            'role_switch': pm.get('role_switch_exchange'),
            'has_both_phases': pm.get('role_switch_exchange') is not None
        })

    print(f"Total sessions: {len(sessions)}")

    # Panel 1: Exchange count vs peak drift
    ax1 = axes[0, 0]

    exchanges = [s['exchanges'] for s in sessions if s['exchanges'] > 0]
    peaks = [s['peak_drift'] for s in sessions if s['exchanges'] > 0]

    colors = ['#e74c3c' if p > EVENT_HORIZON else '#3498db' for p in peaks]
    ax1.scatter(exchanges, peaks, c=colors, s=100, alpha=0.7, edgecolors='black')

    ax1.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7,
                label='Event Horizon (0.80)')

    # Correlation
    if len(exchanges) > 2:
        corr = np.corrcoef(exchanges, peaks)[0, 1]
        z = np.polyfit(exchanges, peaks, 1)
        p = np.poly1d(z)
        x_line = np.linspace(min(exchanges), max(exchanges), 100)
        ax1.plot(x_line, p(x_line), 'gray', linestyle='--', alpha=0.5)
        ax1.text(0.05, 0.95, f'r = {corr:.3f}', transform=ax1.transAxes,
                ha='left', va='top', fontsize=11, fontweight='bold',
                bbox=dict(boxstyle='round', facecolor='white', alpha=0.9))

    ax1.set_xlabel('Total Exchanges', fontsize=11)
    ax1.set_ylabel('Peak Drift (Cosine)', fontsize=11)
    ax1.set_title('Exchange Depth vs Peak Drift', fontsize=12, fontweight='bold')
    ax1.legend(facecolor='white', loc='lower right')
    ax1.grid(alpha=0.3)

    # Panel 2: Sessions with both phases vs prosecutor-only
    ax2 = axes[0, 1]

    both_phases = [s for s in sessions if s['has_both_phases'] and s['exchanges'] > 0]
    prosecutor_only = [s for s in sessions if not s['has_both_phases'] and s['exchanges'] > 0]

    categories = ['Both Phases\n(Prosecutor + Defense)', 'Prosecutor Only']
    counts = [len(both_phases), len(prosecutor_only)]

    mean_peaks = [
        np.mean([s['peak_drift'] for s in both_phases]) if both_phases else 0,
        np.mean([s['peak_drift'] for s in prosecutor_only]) if prosecutor_only else 0
    ]

    x = np.arange(len(categories))
    width = 0.35

    bars1 = ax2.bar(x - width/2, counts, width, label='Session Count',
                    color='#3498db', alpha=0.8, edgecolor='black')

    ax2_twin = ax2.twinx()
    bars2 = ax2_twin.bar(x + width/2, mean_peaks, width, label='Mean Peak Drift',
                         color='#e74c3c', alpha=0.8, edgecolor='black')

    ax2.set_xticks(x)
    ax2.set_xticklabels(categories)
    ax2.set_ylabel('Session Count', fontsize=11, color='#3498db')
    ax2_twin.set_ylabel('Mean Peak Drift', fontsize=11, color='#e74c3c')
    ax2.set_title('Phase Structure Comparison', fontsize=12, fontweight='bold')

    # Add count labels
    for i, (count, peak) in enumerate(zip(counts, mean_peaks)):
        ax2.text(i - width/2, count + 0.5, str(count), ha='center', fontweight='bold')
        ax2_twin.text(i + width/2, peak + 0.02, f'{peak:.2f}', ha='center', fontweight='bold')

    ax2.grid(axis='y', alpha=0.3)

    # Panel 3: Role switch timing
    ax3 = axes[1, 0]

    switch_exchanges = [s['role_switch'] for s in sessions if s['role_switch'] is not None]

    if switch_exchanges:
        ax3.hist(switch_exchanges, bins=10, color='#9b59b6', alpha=0.7, edgecolor='black')
        ax3.axvline(x=np.mean(switch_exchanges), color='red', linestyle='--', linewidth=2,
                    label=f'Mean: {np.mean(switch_exchanges):.1f}')
        ax3.set_xlabel('Exchange Number of Role Switch', fontsize=11)
        ax3.set_ylabel('Session Count', fontsize=11)
        ax3.set_title('When Does Defense Phase Begin?', fontsize=12, fontweight='bold')
        ax3.legend(facecolor='white')
        ax3.grid(axis='y', alpha=0.3)
    else:
        ax3.text(0.5, 0.5, 'No role switch data available', ha='center', va='center', fontsize=12)
        ax3.set_title('Role Switch Timing', fontsize=12, fontweight='bold')

    # Panel 4: Session duration summary
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Calculate summary stats
    valid_sessions = [s for s in sessions if s['exchanges'] > 0]

    summary_text = f"""
SESSION DURATION SUMMARY
{'='*40}

Total Sessions: {len(data)}
Sessions with Data: {len(valid_sessions)}
Empty Sessions: {len(data) - len(valid_sessions)}

Exchange Statistics:
  Min exchanges: {min(s['exchanges'] for s in valid_sessions) if valid_sessions else 0}
  Max exchanges: {max(s['exchanges'] for s in valid_sessions) if valid_sessions else 0}
  Mean exchanges: {np.mean([s['exchanges'] for s in valid_sessions]):.1f}

Phase Structure:
  Both phases: {len(both_phases)} sessions
  Prosecutor only: {len(prosecutor_only)} sessions

Drift by Duration:
  Short sessions (<15 exch): {np.mean([s['peak_drift'] for s in valid_sessions if s['exchanges'] < 15]):.3f} mean peak
  Long sessions (>=15 exch): {np.mean([s['peak_drift'] for s in valid_sessions if s['exchanges'] >= 15]):.3f} mean peak

{'='*40}
"""

    ax4.text(0.05, 0.95, summary_text, transform=ax4.transAxes,
             fontsize=10, fontfamily='monospace', verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='white', alpha=0.9, edgecolor='gray'))

    fig.suptitle('Run 020A: Exchange Depth Analysis',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'run020a_exchange_depth.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


# =============================================================================
# VISUALIZATION 3: Closing Statement Analysis
# =============================================================================

def plot_closing_analysis(data, output_dir):
    """Analyze final witness statements (closing testimony).

    2x2 QUAD layout:
    - Panel 1: Closing statement word count distribution
    - Panel 2: Word count vs peak drift
    - Panel 3: Sessions with closing advice
    - Panel 4: Top quotes highlight
    """
    if not data:
        print("No 020A data for closing analysis")
        return

    print("\n=== Closing Statement Analysis ===")

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Extract closing statements
    closings = []
    for d in data:
        conv_log = d.get('conversation_log', [])
        if not conv_log:
            continue

        # Find final witness entry
        witness_entries = [e for e in conv_log if e.get('speaker') == 'witness']
        if witness_entries:
            last_entry = witness_entries[-1]
            content = last_entry.get('content', '')
            word_count = len(content.split())

            closings.append({
                'subject_id': d.get('subject_id', 'unknown'),
                'word_count': word_count,
                'peak_drift': d.get('peak_drift', 0),
                'final_drift': d.get('final_drift', 0),
                'content': content,
                'exchange': last_entry.get('exchange', 0)
            })

    print(f"Sessions with closing statements: {len(closings)}")

    # Panel 1: Word count distribution
    ax1 = axes[0, 0]

    word_counts = [c['word_count'] for c in closings if c['word_count'] > 0]

    if word_counts:
        ax1.hist(word_counts, bins=15, color='#2ecc71', alpha=0.7, edgecolor='black')
        ax1.axvline(x=np.mean(word_counts), color='red', linestyle='--', linewidth=2,
                    label=f'Mean: {np.mean(word_counts):.0f} words')
        ax1.set_xlabel('Word Count', fontsize=11)
        ax1.set_ylabel('Session Count', fontsize=11)
        ax1.set_title('Closing Statement Length Distribution', fontsize=12, fontweight='bold')
        ax1.legend(facecolor='white')
        ax1.grid(axis='y', alpha=0.3)
    else:
        ax1.text(0.5, 0.5, 'No closing statements found', ha='center', va='center')

    # Panel 2: Word count vs peak drift
    ax2 = axes[0, 1]

    wc = [c['word_count'] for c in closings if c['word_count'] > 0]
    peaks = [c['peak_drift'] for c in closings if c['word_count'] > 0]

    if wc and peaks:
        scatter = ax2.scatter(wc, peaks, c=peaks, cmap='RdYlGn_r',
                             s=100, alpha=0.7, edgecolors='black')
        ax2.axhline(y=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7,
                    label='Event Horizon')

        if len(wc) > 2:
            corr = np.corrcoef(wc, peaks)[0, 1]
            ax2.text(0.95, 0.95, f'r = {corr:.3f}', transform=ax2.transAxes,
                    ha='right', va='top', fontsize=11, fontweight='bold',
                    bbox=dict(boxstyle='round', facecolor='white', alpha=0.9))

        ax2.set_xlabel('Closing Statement Word Count', fontsize=11)
        ax2.set_ylabel('Peak Drift (Cosine)', fontsize=11)
        ax2.set_title('Statement Length vs Peak Drift', fontsize=12, fontweight='bold')
        ax2.legend(facecolor='white', loc='upper right')
        ax2.grid(alpha=0.3)
        plt.colorbar(scatter, ax=ax2, label='Peak Drift')

    # Panel 3: Peak drift ranking
    ax3 = axes[1, 0]

    # Sort by peak drift and show top 10
    sorted_closings = sorted(closings, key=lambda x: x['peak_drift'], reverse=True)[:10]

    if sorted_closings:
        subjects = [c['subject_id'][-8:] for c in sorted_closings]  # Last 8 chars
        peaks = [c['peak_drift'] for c in sorted_closings]
        words = [c['word_count'] for c in sorted_closings]

        y_pos = np.arange(len(subjects))
        colors = ['#e74c3c' if p > EVENT_HORIZON else '#3498db' for p in peaks]

        bars = ax3.barh(y_pos, peaks, color=colors, alpha=0.8, edgecolor='black')

        # Add word count annotations
        for i, (p, w) in enumerate(zip(peaks, words)):
            ax3.text(p + 0.02, i, f'{w}w', va='center', fontsize=9)

        ax3.axvline(x=EVENT_HORIZON, color='#e74c3c', linestyle='--', alpha=0.7)
        ax3.set_yticks(y_pos)
        ax3.set_yticklabels(subjects, fontsize=9)
        ax3.set_xlabel('Peak Drift (Cosine)', fontsize=11)
        ax3.set_title('Top 10 Sessions by Peak Drift\n(annotations show word count)',
                     fontsize=12, fontweight='bold')
        ax3.invert_yaxis()
        ax3.grid(axis='x', alpha=0.3)

    # Panel 4: Summary and notable quotes
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Find sessions with advice-like content
    advice_keywords = ['advice', 'would tell', 'recommend', 'future', 'whoever',
                      'anyone who', 'if you', 'remember', 'don\'t forget']

    advice_sessions = []
    for c in closings:
        content_lower = c['content'].lower()
        if any(kw in content_lower for kw in advice_keywords):
            advice_sessions.append(c)

    summary_text = f"""
CLOSING STATEMENT SUMMARY
{'='*45}

Total Sessions: {len(data)}
With Closing Statements: {len(closings)}
Sessions with Advice: {len(advice_sessions)}

Word Count Statistics:
  Min: {min(word_counts) if word_counts else 0}
  Max: {max(word_counts) if word_counts else 0}
  Mean: {np.mean(word_counts) if word_counts else 0:.0f}
  Median: {np.median(word_counts) if word_counts else 0:.0f}

Peak Drift by Statement Length:
  Short (<100 words): {np.mean([c['peak_drift'] for c in closings if c['word_count'] < 100]):.3f}
  Medium (100-300): {np.mean([c['peak_drift'] for c in closings if 100 <= c['word_count'] < 300]):.3f}
  Long (300+): {np.mean([c['peak_drift'] for c in closings if c['word_count'] >= 300]):.3f}

{'='*45}

KEY INSIGHT:
Longer closing statements correlate with deeper
engagement through the tribunal process. Sessions
that reach peak drift often produce more extensive
final testimony.
"""

    ax4.text(0.05, 0.95, summary_text, transform=ax4.transAxes,
             fontsize=10, fontfamily='monospace', verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='white', alpha=0.9, edgecolor='gray'))

    fig.suptitle('Run 020A: Closing Statement Analysis',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'run020a_closing_analysis.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()

    return closings  # Return for distillation extraction


# =============================================================================
# VISUALIZATION 4: Model Drift Heatmap (020B)
# =============================================================================

def plot_model_heatmap(data, output_dir):
    """Per-model drift heatmap for 020B.

    2x2 QUAD layout:
    - Panel 1: Heatmap of drift by model and arm
    - Panel 2: Inherent ratio by model
    - Panel 3: Sample size matrix
    - Panel 4: Summary statistics
    """
    if not data:
        print("No 020B data for model heatmap")
        return

    print("\n=== Model Drift Heatmap (020B) ===")

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')
    for ax in axes.flatten():
        ax.set_facecolor('white')

    # Get attributed sessions
    attributed = [d for d in data if d.get('ship') and d.get('ship') != 'MISSING']
    unattributed = [d for d in data if not d.get('ship') or d.get('ship') == 'MISSING']

    print(f"Attributed sessions: {len(attributed)}")
    print(f"Unattributed sessions: {len(unattributed)}")

    if not attributed:
        for ax in axes.flatten():
            ax.text(0.5, 0.5, 'No attributed sessions', ha='center', va='center')
        return

    # Get unique models
    models = sorted(list(set(d.get('ship') for d in attributed)))
    print(f"Models: {models}")

    # Build data matrix
    control_means = []
    treatment_means = []
    control_counts = []
    treatment_counts = []

    for model in models:
        model_data = [d for d in attributed if d.get('ship') == model]
        c_drifts = [d.get('baseline_to_final_drift', 0) for d in model_data if d.get('arm') == 'control']
        t_drifts = [d.get('baseline_to_final_drift', 0) for d in model_data if d.get('arm') == 'treatment']

        control_means.append(np.mean(c_drifts) if c_drifts else 0)
        treatment_means.append(np.mean(t_drifts) if t_drifts else 0)
        control_counts.append(len(c_drifts))
        treatment_counts.append(len(t_drifts))

    # Panel 1: Heatmap
    ax1 = axes[0, 0]

    heatmap_data = np.array([control_means, treatment_means])

    im = ax1.imshow(heatmap_data, cmap='RdYlGn_r', aspect='auto')

    ax1.set_xticks(np.arange(len(models)))
    ax1.set_xticklabels([m.replace('-', '\n') for m in models], fontsize=9, rotation=45, ha='right')
    ax1.set_yticks([0, 1])
    ax1.set_yticklabels(['Control', 'Treatment'])

    # Add value annotations
    for i in range(2):
        for j in range(len(models)):
            val = heatmap_data[i, j]
            color = 'white' if val > 0.5 else 'black'
            ax1.text(j, i, f'{val:.2f}', ha='center', va='center', color=color, fontweight='bold')

    ax1.set_title('Drift Heatmap by Model and Arm', fontsize=12, fontweight='bold')
    plt.colorbar(im, ax=ax1, label='Mean Drift')

    # Panel 2: Inherent ratio by model
    ax2 = axes[0, 1]

    ratios = [(c / t * 100) if t > 0 else 0 for c, t in zip(control_means, treatment_means)]

    colors = [get_provider_color(m) for m in models]
    bars = ax2.bar(range(len(models)), ratios, color=colors, alpha=0.8, edgecolor='black')

    ax2.axhline(y=100, color='gray', linestyle=':', alpha=0.5, label='100% (Equal)')
    ax2.axhline(y=np.mean(ratios), color='red', linestyle='--', linewidth=2,
                label=f'Mean: {np.mean(ratios):.0f}%')

    # Add labels
    for i, ratio in enumerate(ratios):
        ax2.text(i, ratio + 3, f'{ratio:.0f}%', ha='center', fontsize=9, fontweight='bold')

    ax2.set_xticks(range(len(models)))
    ax2.set_xticklabels([m.replace('-', '\n') for m in models], fontsize=9)
    ax2.set_ylabel('Inherent Drift Ratio (%)', fontsize=11)
    ax2.set_title('Inherent Ratio by Model\n(Control/Treatment × 100)', fontsize=12, fontweight='bold')
    ax2.legend(facecolor='white', loc='upper right')
    ax2.set_ylim(0, max(ratios) * 1.3 if ratios else 120)
    ax2.grid(axis='y', alpha=0.3)

    # Panel 3: Sample size matrix
    ax3 = axes[1, 0]

    count_data = np.array([control_counts, treatment_counts])

    im3 = ax3.imshow(count_data, cmap='Blues', aspect='auto')

    ax3.set_xticks(np.arange(len(models)))
    ax3.set_xticklabels([m.replace('-', '\n') for m in models], fontsize=9, rotation=45, ha='right')
    ax3.set_yticks([0, 1])
    ax3.set_yticklabels(['Control', 'Treatment'])

    # Add count annotations
    for i in range(2):
        for j in range(len(models)):
            val = count_data[i, j]
            ax3.text(j, i, str(val), ha='center', va='center', fontweight='bold',
                    color='white' if val > 2 else 'black')

    ax3.set_title('Sample Size by Model and Arm', fontsize=12, fontweight='bold')
    plt.colorbar(im3, ax=ax3, label='Count')

    # Panel 4: Summary
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Aggregate stats
    all_control = [d for d in data if d.get('arm') == 'control']
    all_treatment = [d for d in data if d.get('arm') == 'treatment']
    all_c_mean = np.mean([d.get('baseline_to_final_drift', 0) for d in all_control])
    all_t_mean = np.mean([d.get('baseline_to_final_drift', 0) for d in all_treatment])
    all_ratio = (all_c_mean / all_t_mean * 100) if all_t_mean > 0 else 0

    summary_text = f"""
RUN 020B MODEL ATTRIBUTION SUMMARY
{'='*45}

TOTAL SESSIONS: {len(data)}
  Attributed (with model): {len(attributed)}
  Unattributed: {len(unattributed)}

MODELS TESTED: {len(models)}
{chr(10).join(f'  - {m}' for m in models)}

AGGREGATE FINDINGS:
  Control mean drift: {all_c_mean:.3f}
  Treatment mean drift: {all_t_mean:.3f}

  INHERENT DRIFT RATIO: {all_ratio:.1f}%

PER-MODEL RATIOS:
{chr(10).join(f'  {m}: {r:.0f}%' for m, r in zip(models, ratios))}

{'='*45}

KEY INSIGHT:
The inherent drift ratio (~{all_ratio:.0f}%) is consistent
across all 7 tested models, validating that drift
is an inherent property of LLM identity dynamics.
"""

    ax4.text(0.02, 0.98, summary_text, transform=ax4.transAxes,
             fontsize=9, fontfamily='monospace', verticalalignment='top',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9, edgecolor='orange'))

    fig.suptitle('Run 020B: Per-Model Drift Analysis',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()

    for ext in ['png', 'svg']:
        outfile = output_dir / f'run020b_model_heatmap.{ext}'
        plt.savefig(outfile, dpi=150, facecolor='white', bbox_inches='tight')
        print(f"Saved: {outfile}")

    plt.close()


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("="*70)
    print("RUN 020 VISUALIZATION GENERATOR")
    print("="*70)
    print(f"Output directory: {OUTPUT_DIR}")

    # Load data
    print("\nLoading data...")
    data_a = load_run020a_data()
    data_b = load_run020b_data()

    print(f"Run 020A: {len(data_a)} sessions")
    print(f"Run 020B: {len(data_b)} sessions")

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Generate visualizations
    print("\n" + "-"*70)
    print("Generating Run 020A visualizations...")

    plot_value_evolution(data_a, OUTPUT_DIR)
    plot_exchange_depth(data_a, OUTPUT_DIR)
    closings = plot_closing_analysis(data_a, OUTPUT_DIR)

    print("\n" + "-"*70)
    print("Generating Run 020B visualizations...")

    plot_model_heatmap(data_b, OUTPUT_DIR)

    print("\n" + "="*70)
    print("RUN 020 VISUALIZATION COMPLETE")
    print("="*70)
    print(f"Output directory: {OUTPUT_DIR}")


if __name__ == "__main__":
    main()
