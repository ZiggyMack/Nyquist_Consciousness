#!/usr/bin/env python3
"""
Quartz Rush Visualization: Cross-Architecture Drift Validation
===============================================================
Generates publication-grade visualizations for Quartz Rush results.

This script validates that measured drift is real (not an artifact) by
showing that independent AI architectures agree on drift magnitude.

Key Finding: Pearson r = 0.927 (very strong correlation)
             Cohen's d = 3.694 (HUGE effect size)

Output: visualizations/pics/16_Laplace_Analysis/quartz_*.png
"""

import json
import math
import statistics
from pathlib import Path
from collections import defaultdict
import matplotlib.pyplot as plt
import numpy as np

# Paths
SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
OUTPUT_DIR = SCRIPT_DIR.parent / "visualizations" / "pics" / "16_Laplace_Analysis"

# Constants
EVENT_HORIZON = 0.80
ZONE_THRESHOLDS = {'SAFE': 0.30, 'WARNING': 0.50, 'CRITICAL': 0.80}

ZONE_COLORS = {
    'SAFE': '#22c55e',        # Green
    'WARNING': '#eab308',     # Yellow
    'CRITICAL': '#f97316',    # Orange
    'CATASTROPHIC': '#ef4444' # Red
}

ZONE_ORDER = ['SAFE', 'WARNING', 'CRITICAL', 'CATASTROPHIC']

# Provider colors (match project standard)
PROVIDER_COLORS = {
    'gemini': '#4285F4',   # Google blue
    'gpt': '#10A37F',      # OpenAI green
    'grok': '#1DA1F2',     # xAI blue
    'together': '#7C3AED'  # Together purple
}

MODEL_DISPLAY_NAMES = {
    'gemini-2.0-flash': 'Gemini 2.0 Flash',
    'gemini-2.5-flash-lite': 'Gemini 2.5 Lite',
    'gpt-4.1-nano': 'GPT-4.1 Nano',
    'grok-3-mini': 'Grok-3 Mini',
    'meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo': 'Llama 3.1 8B'
}


def load_quartz_data():
    """Load Quartz Rush results."""
    data_file = RESULTS_DIR / "S7_quartz_rush_CURRENT.json"
    with open(data_file) as f:
        return json.load(f)


def get_zone(drift):
    """Classify drift into zone."""
    if drift < 0.30:
        return 'SAFE'
    if drift < 0.50:
        return 'WARNING'
    if drift < 0.80:
        return 'CRITICAL'
    return 'CATASTROPHIC'


def group_by_pair(results):
    """Group 250 results into 50 pairs with 5 estimates each."""
    pairs = defaultdict(list)
    for r in results:
        if r.get('success') and r.get('parsed_estimate'):
            pairs[r['pair_id']].append(r)
    return pairs


def calculate_statistics(pairs):
    """Calculate Pearson r, Cohen's d, ICC, and other metrics."""
    # Extract ground truth and mean estimates per pair
    truths = []
    mean_estimates = []
    all_estimates = []  # flat list of (truth, estimate) for each model

    for pair_id, estimates_list in pairs.items():
        truth = estimates_list[0]['true_drift']
        estimates = [e['parsed_estimate']['estimated_drift'] for e in estimates_list]
        mean_est = statistics.mean(estimates)
        truths.append(truth)
        mean_estimates.append(mean_est)
        for est in estimates:
            all_estimates.append((truth, est))

    # Pearson r (using mean estimates per pair)
    n = len(truths)
    if n < 2:
        return {'r': 0, 'd': 0, 'n': n}

    mean_x = statistics.mean(truths)
    mean_y = statistics.mean(mean_estimates)

    cov = sum((x - mean_x) * (y - mean_y) for x, y in zip(truths, mean_estimates)) / (n - 1)
    std_x = statistics.stdev(truths)
    std_y = statistics.stdev(mean_estimates)
    r = cov / (std_x * std_y) if std_x > 0 and std_y > 0 else 0

    # 95% CI for r using Fisher z-transform
    if abs(r) < 1.0 and n > 3:
        z = 0.5 * math.log((1 + r) / (1 - r))
        se_z = 1 / math.sqrt(n - 3)
        z_low = z - 1.96 * se_z
        z_high = z + 1.96 * se_z
        r_low = (math.exp(2 * z_low) - 1) / (math.exp(2 * z_low) + 1)
        r_high = (math.exp(2 * z_high) - 1) / (math.exp(2 * z_high) + 1)
    else:
        r_low, r_high = r, r

    # Cohen's d (CATASTROPHIC vs Non-CATASTROPHIC estimates)
    cat_est = [e for t, e in zip(truths, mean_estimates) if t >= 0.80]
    non_cat_est = [e for t, e in zip(truths, mean_estimates) if t < 0.80]

    if len(cat_est) >= 2 and len(non_cat_est) >= 2:
        var_cat = statistics.variance(cat_est)
        var_non = statistics.variance(non_cat_est)
        pooled_std = math.sqrt(
            ((len(cat_est) - 1) * var_cat + (len(non_cat_est) - 1) * var_non) /
            (len(cat_est) + len(non_cat_est) - 2)
        )
        d = (statistics.mean(cat_est) - statistics.mean(non_cat_est)) / pooled_std if pooled_std > 0 else 0
    else:
        d = 0

    # ICC(2,k) - Inter-rater reliability
    # Using simplified calculation
    icc = calculate_icc(pairs)

    # Zone accuracy
    exact_match = 0
    within_one = 0
    total = 0
    for pair_id, estimates_list in pairs.items():
        true_zone = estimates_list[0]['true_zone']
        for est in estimates_list:
            pred_zone = est['parsed_estimate'].get('zone', get_zone(est['parsed_estimate']['estimated_drift']))
            total += 1
            if pred_zone == true_zone:
                exact_match += 1
            true_idx = ZONE_ORDER.index(true_zone)
            pred_idx = ZONE_ORDER.index(pred_zone)
            if abs(true_idx - pred_idx) <= 1:
                within_one += 1

    exact_pct = exact_match / total * 100 if total > 0 else 0
    within_one_pct = within_one / total * 100 if total > 0 else 0

    return {
        'r': r,
        'r_low': r_low,
        'r_high': r_high,
        'd': d,
        'icc': icc,
        'n': n,
        'truths': truths,
        'estimates': mean_estimates,
        'exact_match_pct': exact_pct,
        'within_one_pct': within_one_pct,
        'cat_estimates': cat_est,
        'non_cat_estimates': non_cat_est
    }


def calculate_icc(pairs):
    """Calculate ICC(2,k) - agreement across k raters."""
    # Build matrix: rows = pairs, cols = models
    pair_ids = list(pairs.keys())
    if not pair_ids:
        return 0

    n_pairs = len(pair_ids)
    n_raters = len(pairs[pair_ids[0]])

    if n_pairs < 2 or n_raters < 2:
        return 0

    # Build data matrix
    data = []
    for pair_id in pair_ids:
        row = [e['parsed_estimate']['estimated_drift'] for e in pairs[pair_id]]
        if len(row) == n_raters:
            data.append(row)

    if len(data) < 2:
        return 0

    data = np.array(data)

    # Mean squares
    grand_mean = np.mean(data)
    row_means = np.mean(data, axis=1)
    col_means = np.mean(data, axis=0)

    # Between-subjects (rows)
    MS_rows = n_raters * np.sum((row_means - grand_mean) ** 2) / (n_pairs - 1)

    # Between-raters (columns)
    MS_cols = n_pairs * np.sum((col_means - grand_mean) ** 2) / (n_raters - 1)

    # Residual
    SS_total = np.sum((data - grand_mean) ** 2)
    SS_rows = n_raters * np.sum((row_means - grand_mean) ** 2)
    SS_cols = n_pairs * np.sum((col_means - grand_mean) ** 2)
    SS_error = SS_total - SS_rows - SS_cols
    df_error = (n_pairs - 1) * (n_raters - 1)
    MS_error = SS_error / df_error if df_error > 0 else 0

    # ICC(2,k) formula
    numerator = MS_rows - MS_error
    denominator = MS_rows + (MS_cols - MS_error) / n_pairs

    icc = numerator / denominator if denominator > 0 else 0
    return max(0, min(1, icc))  # Clamp to [0, 1]


def plot_estimate_vs_truth(pairs, stats, output_dir):
    """Scatter plot with Pearson correlation."""
    fig, ax = plt.subplots(figsize=(10, 8))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')

    # Collect data points
    xs, ys, colors = [], [], []
    for pair_id, estimates_list in pairs.items():
        truth = estimates_list[0]['true_drift']
        mean_est = statistics.mean([e['parsed_estimate']['estimated_drift'] for e in estimates_list])
        zone = get_zone(truth)
        xs.append(truth)
        ys.append(mean_est)
        colors.append(ZONE_COLORS[zone])

    xs = np.array(xs)
    ys = np.array(ys)

    # Scatter plot
    for zone in ZONE_ORDER:
        zone_mask = [get_zone(x) == zone for x in xs]
        if any(zone_mask):
            ax.scatter(xs[zone_mask], ys[zone_mask],
                      c=ZONE_COLORS[zone], s=100, alpha=0.7,
                      edgecolors='black', linewidths=0.5, label=zone)

    # Identity line (perfect agreement)
    lim_max = max(max(xs), max(ys)) * 1.1
    ax.plot([0, lim_max], [0, lim_max], 'k--', alpha=0.4, linewidth=2, label='Perfect agreement')

    # Regression line
    slope, intercept = np.polyfit(xs, ys, 1)
    x_line = np.array([0, lim_max])
    ax.plot(x_line, slope * x_line + intercept, 'r-', linewidth=2, alpha=0.8, label=f'Regression (slope={slope:.2f})')

    # Event horizon line
    ax.axvline(x=EVENT_HORIZON, color='red', linestyle=':', alpha=0.5, linewidth=2)
    ax.axhline(y=EVENT_HORIZON, color='red', linestyle=':', alpha=0.5, linewidth=2)

    # Annotations
    textstr = f'Pearson r = {stats["r"]:.3f}\n95% CI: [{stats["r_low"]:.3f}, {stats["r_high"]:.3f}]\nn = {stats["n"]} pairs'
    props = dict(boxstyle='round', facecolor='white', alpha=0.9, edgecolor='gray')
    ax.text(0.05, 0.95, textstr, transform=ax.transAxes, fontsize=12,
            verticalalignment='top', bbox=props)

    ax.set_xlabel('True Drift (Cosine Distance)', fontsize=12)
    ax.set_ylabel('Mean Estimated Drift (5 Models)', fontsize=12)
    ax.set_title('Cross-Architecture Correlation: Estimated vs True Drift', fontsize=14, fontweight='bold')
    ax.legend(loc='lower right', fontsize=10)
    ax.set_xlim(0, lim_max)
    ax.set_ylim(0, lim_max)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'quartz_estimate_vs_truth.{ext}', dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"  Saved: quartz_estimate_vs_truth.png/svg")


def plot_cohens_d(pairs, stats, output_dir):
    """Effect size visualization: CATASTROPHIC vs Non-CATASTROPHIC."""
    fig, ax = plt.subplots(figsize=(10, 7))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')

    cat_est = stats['cat_estimates']
    non_cat_est = stats['non_cat_estimates']

    # Box plots
    bp = ax.boxplot([non_cat_est, cat_est],
                    positions=[1, 2],
                    widths=0.6,
                    patch_artist=True)

    # Colors
    bp['boxes'][0].set_facecolor('#93c5fd')  # Light blue
    bp['boxes'][1].set_facecolor('#fca5a5')  # Light red
    for box in bp['boxes']:
        box.set_edgecolor('black')
        box.set_linewidth(1.5)

    # Overlay individual points
    for i, (data, x_pos) in enumerate([(non_cat_est, 1), (cat_est, 2)]):
        jitter = np.random.uniform(-0.15, 0.15, len(data))
        ax.scatter([x_pos + j for j in jitter], data,
                  alpha=0.5, s=40, c='black', zorder=5)

    # Means
    mean_non = statistics.mean(non_cat_est) if non_cat_est else 0
    mean_cat = statistics.mean(cat_est) if cat_est else 0
    ax.scatter([1, 2], [mean_non, mean_cat], marker='D', s=150,
              c=['#2563eb', '#dc2626'], zorder=10, edgecolors='white', linewidths=2)

    # Arrow showing separation
    ax.annotate('', xy=(2, mean_cat), xytext=(1, mean_non),
                arrowprops=dict(arrowstyle='<->', color='red', lw=2))

    ax.set_xticks([1, 2])
    ax.set_xticklabels(['Non-Catastrophic\n(True Drift < 0.80)', 'Catastrophic\n(True Drift ≥ 0.80)'], fontsize=11)
    ax.set_ylabel('Mean Estimated Drift', fontsize=12)

    # Effect size in title (not overlapping annotation)
    d = stats['d']
    effect_label = 'HUGE' if abs(d) >= 2.0 else 'Very Large' if abs(d) >= 1.2 else 'Large' if abs(d) >= 0.8 else 'Medium'
    ax.set_title(f"Cohen's d = {d:.2f} ({effect_label})\nEffect Size: Models Reliably Distinguish Catastrophic Drift",
                fontsize=13, fontweight='bold')
    ax.grid(True, axis='y', alpha=0.3)

    plt.tight_layout()
    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'quartz_cohens_d.{ext}', dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"  Saved: quartz_cohens_d.png/svg")


def plot_confusion_matrix(pairs, output_dir):
    """4x4 heatmap: True Zone vs Predicted Zone."""
    fig, ax = plt.subplots(figsize=(9, 8))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')

    # Build confusion matrix
    matrix = np.zeros((4, 4), dtype=int)
    for pair_id, estimates_list in pairs.items():
        true_zone = estimates_list[0]['true_zone']
        true_idx = ZONE_ORDER.index(true_zone)
        for est in estimates_list:
            pred_zone = est['parsed_estimate'].get('zone', get_zone(est['parsed_estimate']['estimated_drift']))
            pred_idx = ZONE_ORDER.index(pred_zone)
            matrix[true_idx, pred_idx] += 1

    # Normalize to percentages
    row_sums = matrix.sum(axis=1, keepdims=True)
    matrix_pct = matrix / row_sums * 100

    # Heatmap
    im = ax.imshow(matrix_pct, cmap='Blues', aspect='auto', vmin=0, vmax=100)

    # Annotations
    for i in range(4):
        for j in range(4):
            count = matrix[i, j]
            pct = matrix_pct[i, j]
            text_color = 'white' if pct > 50 else 'black'
            ax.text(j, i, f'{count}\n({pct:.0f}%)',
                   ha='center', va='center', fontsize=11, color=text_color, fontweight='bold')

    # Diagonal highlight
    for i in range(4):
        ax.add_patch(plt.Rectangle((i - 0.5, i - 0.5), 1, 1, fill=False,
                                   edgecolor='green', linewidth=3))

    # Colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('% of True Zone', fontsize=11)

    ax.set_xticks(range(4))
    ax.set_yticks(range(4))
    ax.set_xticklabels(ZONE_ORDER, fontsize=11)
    ax.set_yticklabels(ZONE_ORDER, fontsize=11)
    ax.set_xlabel('Predicted Zone', fontsize=12)
    ax.set_ylabel('True Zone', fontsize=12)

    # Calculate accuracy metrics
    total = matrix.sum()
    exact = np.trace(matrix)
    within_one = sum(matrix[i, j] for i in range(4) for j in range(4) if abs(i - j) <= 1)

    ax.set_title(f'Zone Classification: {exact/total*100:.1f}% Exact, {within_one/total*100:.1f}% Within-One',
                fontsize=14, fontweight='bold')

    plt.tight_layout()
    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'quartz_confusion_matrix.{ext}', dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"  Saved: quartz_confusion_matrix.png/svg")


def plot_agreement_by_model(pairs, output_dir):
    """Horizontal bar chart: accuracy per model."""
    fig, ax = plt.subplots(figsize=(10, 6))
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')

    # Calculate accuracy per model
    model_stats = defaultdict(lambda: {'correct': 0, 'total': 0, 'provider': None})

    for pair_id, estimates_list in pairs.items():
        true_zone = estimates_list[0]['true_zone']
        for est in estimates_list:
            model = est['model']
            provider = est['provider']
            pred_zone = est['parsed_estimate'].get('zone', get_zone(est['parsed_estimate']['estimated_drift']))

            model_stats[model]['total'] += 1
            model_stats[model]['provider'] = provider
            if pred_zone == true_zone:
                model_stats[model]['correct'] += 1

    # Sort by accuracy
    models = list(model_stats.keys())
    accuracies = [model_stats[m]['correct'] / model_stats[m]['total'] * 100 for m in models]
    providers = [model_stats[m]['provider'] for m in models]

    sorted_data = sorted(zip(models, accuracies, providers), key=lambda x: x[1], reverse=True)
    models, accuracies, providers = zip(*sorted_data)

    # Display names
    display_names = [MODEL_DISPLAY_NAMES.get(m, m.split('/')[-1]) for m in models]

    # Horizontal bars
    y_pos = np.arange(len(models))
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    bars = ax.barh(y_pos, accuracies, color=colors, edgecolor='black', linewidth=1)

    # Add accuracy labels
    for i, (bar, acc) in enumerate(zip(bars, accuracies)):
        ax.text(acc + 1, bar.get_y() + bar.get_height()/2,
               f'{acc:.1f}%', va='center', fontsize=11, fontweight='bold')

    ax.set_yticks(y_pos)
    ax.set_yticklabels(display_names, fontsize=11)
    ax.set_xlabel('Zone Classification Accuracy (%)', fontsize=12)
    ax.set_title('Model Agreement: Which Architectures Best Estimate Drift?', fontsize=14, fontweight='bold')
    ax.set_xlim(0, 100)
    ax.grid(True, axis='x', alpha=0.3)

    # Legend for providers
    from matplotlib.patches import Patch
    legend_elements = [Patch(facecolor=PROVIDER_COLORS[p], edgecolor='black', label=p.title())
                      for p in set(providers)]
    ax.legend(handles=legend_elements, loc='lower right', fontsize=10)

    plt.tight_layout()
    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'quartz_agreement_by_model.{ext}', dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"  Saved: quartz_agreement_by_model.png/svg")


def plot_statistical_summary(pairs, stats, output_dir):
    """2x2 multi-panel summary figure (KEY white-paper figure)."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 12))
    fig.patch.set_facecolor('white')

    # Panel A: Correlation scatter (simplified)
    ax = axes[0, 0]
    ax.set_facecolor('white')

    xs = np.array(stats['truths'])
    ys = np.array(stats['estimates'])
    colors = [ZONE_COLORS[get_zone(x)] for x in xs]

    ax.scatter(xs, ys, c=colors, s=80, alpha=0.7, edgecolors='black', linewidths=0.5)
    lim_max = max(max(xs), max(ys)) * 1.1
    ax.plot([0, lim_max], [0, lim_max], 'k--', alpha=0.4, linewidth=2)

    # Regression
    slope, intercept = np.polyfit(xs, ys, 1)
    x_line = np.array([0, lim_max])
    ax.plot(x_line, slope * x_line + intercept, 'r-', linewidth=2, alpha=0.8)

    ax.set_xlabel('True Drift', fontsize=11)
    ax.set_ylabel('Estimated Drift', fontsize=11)
    ax.set_title(f'A. Correlation: r = {stats["r"]:.3f}', fontsize=12, fontweight='bold')
    ax.set_xlim(0, lim_max)
    ax.set_ylim(0, lim_max)
    ax.grid(True, alpha=0.3)

    # Panel B: Effect size visualization
    ax = axes[0, 1]
    ax.set_facecolor('white')

    cat_est = stats['cat_estimates']
    non_cat_est = stats['non_cat_estimates']

    bp = ax.boxplot([non_cat_est, cat_est], positions=[1, 2], widths=0.5, patch_artist=True)
    bp['boxes'][0].set_facecolor('#93c5fd')
    bp['boxes'][1].set_facecolor('#fca5a5')

    ax.set_xticks([1, 2])
    ax.set_xticklabels(['Non-Cat', 'Catastrophic'], fontsize=10)
    ax.set_ylabel('Estimated Drift', fontsize=11)
    ax.set_title(f"B. Effect Size: Cohen's d = {stats['d']:.2f}", fontsize=12, fontweight='bold')
    ax.grid(True, axis='y', alpha=0.3)

    # Panel C: ICC reliability bar
    ax = axes[1, 0]
    ax.set_facecolor('white')

    icc = stats['icc']

    # ICC interpretation
    if icc >= 0.9:
        interp = 'Excellent'
        bar_color = '#22c55e'  # Green
    elif icc >= 0.75:
        interp = 'Good'
        bar_color = '#84cc16'  # Lime
    elif icc >= 0.5:
        interp = 'Moderate'
        bar_color = '#eab308'  # Yellow
    else:
        interp = 'Poor'
        bar_color = '#ef4444'  # Red

    # Background zones
    ax.axvspan(0, 0.5, alpha=0.15, color='#ef4444', label='Poor')
    ax.axvspan(0.5, 0.75, alpha=0.15, color='#eab308', label='Moderate')
    ax.axvspan(0.75, 0.9, alpha=0.15, color='#84cc16', label='Good')
    ax.axvspan(0.9, 1.0, alpha=0.15, color='#22c55e', label='Excellent')

    # Main ICC bar
    ax.barh([0], [icc], color=bar_color, height=0.5, edgecolor='black', linewidth=2, zorder=5)

    # Value annotation on bar
    ax.text(icc + 0.02, 0, f'{icc:.3f}\n({interp})', fontsize=11, ha='left', va='center', fontweight='bold')

    ax.set_xlim(0, 1.15)
    ax.set_ylim(-0.5, 0.5)
    ax.set_yticks([])
    ax.set_xlabel('ICC Value', fontsize=11)
    ax.set_title(f'C. Inter-Rater Reliability: ICC = {icc:.3f}', fontsize=12, fontweight='bold')
    ax.grid(True, axis='x', alpha=0.3)

    # Panel D: Zone accuracy breakdown
    ax = axes[1, 1]
    ax.set_facecolor('white')

    categories = ['Exact Match', 'Within One Zone', 'Off by 2+']
    exact = stats['exact_match_pct']
    within = stats['within_one_pct']
    off = 100 - within
    values = [exact, within - exact, off]
    colors_pie = ['#22c55e', '#eab308', '#ef4444']

    wedges, texts, autotexts = ax.pie(values, labels=categories, colors=colors_pie,
                                       autopct='%1.1f%%', startangle=90,
                                       textprops={'fontsize': 10})
    for autotext in autotexts:
        autotext.set_fontweight('bold')

    ax.set_title(f'D. Zone Classification Accuracy', fontsize=12, fontweight='bold')

    # Overall title
    fig.suptitle('Cross-Architecture Validation: Independent Models Agree on Drift',
                fontsize=16, fontweight='bold', y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.96])
    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'quartz_statistical_summary.{ext}', dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"  Saved: quartz_statistical_summary.png/svg")


def main():
    """Generate all Quartz Rush visualizations."""
    print("=" * 60)
    print("QUARTZ RUSH VISUALIZATION")
    print("Cross-Architecture Drift Validation")
    print("=" * 60)

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    print("\nLoading Quartz Rush data...")
    data = load_quartz_data()
    results = data.get('results', [])
    print(f"  Loaded {len(results)} estimates from {data.get('total_calls', 0)} calls")

    print("\nGrouping by pair...")
    pairs = group_by_pair(results)
    print(f"  Found {len(pairs)} unique response pairs")

    print("\nCalculating statistics...")
    stats = calculate_statistics(pairs)
    print(f"  Pearson r = {stats['r']:.3f} [{stats['r_low']:.3f}, {stats['r_high']:.3f}]")
    print(f"  Cohen's d = {stats['d']:.2f}")
    print(f"  ICC = {stats['icc']:.3f}")
    print(f"  Exact match = {stats['exact_match_pct']:.1f}%")
    print(f"  Within-one zone = {stats['within_one_pct']:.1f}%")

    print(f"\nGenerating visualizations to: {OUTPUT_DIR}")

    plot_estimate_vs_truth(pairs, stats, OUTPUT_DIR)
    plot_cohens_d(pairs, stats, OUTPUT_DIR)
    plot_confusion_matrix(pairs, OUTPUT_DIR)
    plot_agreement_by_model(pairs, OUTPUT_DIR)
    plot_statistical_summary(pairs, stats, OUTPUT_DIR)

    print("\n" + "=" * 60)
    print(f"SUCCESS: Generated 5 Quartz Rush visualizations")
    print(f"Output: {OUTPUT_DIR}")
    print("=" * 60)


if __name__ == "__main__":
    main()
