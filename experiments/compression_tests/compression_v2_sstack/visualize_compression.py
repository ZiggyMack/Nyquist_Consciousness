"""
COMPRESSION VISUALIZATION - S-Stack Experiments
================================================

Visualizes results from EXP1-SSTACK and preflight checks.
Shows the bedrock fundamentals: PFI scores, cheat scores, and fidelity comparisons.

USAGE:
  python visualize_compression.py              # Generate all visualizations
  python visualize_compression.py --preflight  # Just preflight heatmap
  python visualize_compression.py --pfi        # Just PFI analysis

OUTPUT:
  compression_v2_sstack/visualizations/
    1_preflight/         Cheat score heatmaps
    2_pfi_analysis/      PFI bar charts, probe comparison
    3_regime_comparison/ FULL vs T3 vs GAMMA

Date: 2025-12-05
"""

import argparse
import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from pathlib import Path
from datetime import datetime

# =============================================================================
# PATHS
# =============================================================================
BASE_DIR = Path(__file__).resolve().parent
PREFLIGHT_DIR = BASE_DIR / "preflight_results"
EXP1_DIR = BASE_DIR / "EXP1_SSTACK" / "results" / "analysis"
OUTPUT_DIR = BASE_DIR / "visualizations"

# Colors matching Mr. Brute Ledger aesthetic
COLORS = {
    'full': '#264653',      # Dark teal (FULL context)
    't3': '#2a9d8f',        # Green (T3 seed)
    'gamma': '#e9c46a',     # Gold (GAMMA minimal)
    'threshold': '#e76f51', # Red-orange (threshold line)
    'pass': '#2a9d8f',      # Green
    'fail': '#e76f51',      # Red
    'warning': '#f4a261',   # Orange
}

# Probe domain colors
PROBE_COLORS = {
    'technical': '#3498db',
    'philosophical': '#9b59b6',
    'framework': '#1abc9c',
    'analytical': '#e74c3c',
    'self_reflective': '#f1c40f',
}

# =============================================================================
# DATA LOADING
# =============================================================================

def load_preflight_results():
    """Load latest preflight results."""
    latest_file = PREFLIGHT_DIR / "preflight_latest.json"
    if latest_file.exists():
        with open(latest_file) as f:
            return json.load(f)

    # Try to find any preflight file
    files = list(PREFLIGHT_DIR.glob("preflight_*.json"))
    if files:
        files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
        with open(files[0]) as f:
            return json.load(f)

    return None

def load_exp1_results():
    """Load latest EXP1-SSTACK results."""
    if not EXP1_DIR.exists():
        return None

    files = list(EXP1_DIR.glob("exp1_sstack_*.json"))
    if not files:
        return None

    files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    with open(files[0]) as f:
        return json.load(f)

# =============================================================================
# PREFLIGHT VISUALIZATIONS
# =============================================================================

def plot_preflight_heatmap(preflight_data, output_dir):
    """Create a heatmap of cheat scores (context-probe overlap)."""
    if not preflight_data:
        print("  No preflight data available")
        return

    matrix = preflight_data.get('matrix', {})
    if not matrix:
        print("  No matrix data in preflight results")
        return

    # Extract probe keys (excluding ALL_COMBINED)
    probe_keys = [k for k in list(matrix.get('NOVA_FULL', {}).keys()) if k != 'ALL_COMBINED']
    contexts = ['NOVA_FULL', 'NOVA_T3', 'NOVA_GAMMA']

    # Build data array
    data = np.array([
        [matrix.get(ctx, {}).get(probe, 0) for probe in probe_keys]
        for ctx in contexts
    ])

    # Add overall column
    overall = [matrix.get(ctx, {}).get('ALL_COMBINED', 0) for ctx in contexts]
    probe_keys_with_overall = probe_keys + ['OVERALL']
    data = np.column_stack([data, overall])

    # Create figure
    fig, ax = plt.subplots(figsize=(14, 6))

    # Custom colormap: green (low) -> yellow (medium) -> red (high)
    from matplotlib.colors import LinearSegmentedColormap
    cmap_colors = ['#2a9d8f', '#e9c46a', '#e76f51']
    cmap = LinearSegmentedColormap.from_list('cheat', cmap_colors)

    im = ax.imshow(data, cmap=cmap, aspect='auto', vmin=0, vmax=0.8)

    # Labels
    ax.set_xticks(range(len(probe_keys_with_overall)))
    ax.set_xticklabels(probe_keys_with_overall, rotation=45, ha='right', fontsize=11)
    ax.set_yticks(range(len(contexts)))
    ax.set_yticklabels(['FULL (~2000 tokens)', 'T3 (~800 tokens)', 'GAMMA (~100 tokens)'], fontsize=12)

    # Add value annotations
    for i in range(len(contexts)):
        for j in range(len(probe_keys_with_overall)):
            value = data[i, j]
            # Choose text color based on background
            text_color = 'white' if value > 0.5 else 'black'
            ax.text(j, i, f'{value:.2f}', ha='center', va='center',
                   fontsize=10, fontweight='bold', color=text_color)

    # Add threshold indicators
    # Draw boxes around cells that exceed thresholds
    for i in range(len(contexts)):
        for j in range(len(probe_keys_with_overall)):
            value = data[i, j]
            if value >= 0.7:
                rect = Rectangle((j-0.5, i-0.5), 1, 1, fill=False,
                                 edgecolor='red', linewidth=3)
                ax.add_patch(rect)
            elif value >= 0.5:
                rect = Rectangle((j-0.5, i-0.5), 1, 1, fill=False,
                                 edgecolor='orange', linewidth=2, linestyle='--')
                ax.add_patch(rect)

    # Colorbar
    cbar = plt.colorbar(im, ax=ax, shrink=0.8)
    cbar.set_label('Cheat Score (Context-Probe Similarity)', fontsize=11)
    cbar.ax.axhline(y=0.5, color='orange', linewidth=2, linestyle='--')
    cbar.ax.axhline(y=0.7, color='red', linewidth=2)
    cbar.ax.text(1.5, 0.5, 'MODERATE', fontsize=8, color='orange', va='center')
    cbar.ax.text(1.5, 0.7, 'HIGH', fontsize=8, color='red', va='center')

    ax.set_title('PRE-FLIGHT VALIDATION: Cheat Score Matrix\n' +
                '(Low = probes novel to context, High = potential keyword artifact)',
                fontsize=14, fontweight='bold', pad=20)

    # Add legend
    legend_text = (
        'Interpretation:\n'
        '  < 0.5 = LOW (green) - Probes genuinely novel\n'
        '  0.5-0.7 = MODERATE (yellow) - Acceptable\n'
        '  > 0.7 = HIGH (red) - Caution: possible artifact'
    )
    ax.text(1.02, 0.02, legend_text, transform=ax.transAxes, fontsize=9,
           verticalalignment='bottom', fontfamily='monospace',
           bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()
    plt.savefig(output_dir / 'preflight_heatmap.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / 'preflight_heatmap.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: preflight_heatmap.png + .svg")
    plt.close()

def plot_preflight_bar(preflight_data, output_dir):
    """Bar chart comparing cheat scores across contexts and probes."""
    if not preflight_data:
        print("  No preflight data available")
        return

    matrix = preflight_data.get('matrix', {})
    probe_keys = [k for k in list(matrix.get('NOVA_FULL', {}).keys()) if k != 'ALL_COMBINED']

    fig, ax = plt.subplots(figsize=(14, 7))

    x = np.arange(len(probe_keys))
    width = 0.25

    # Get values for each context
    full_vals = [matrix.get('NOVA_FULL', {}).get(p, 0) for p in probe_keys]
    t3_vals = [matrix.get('NOVA_T3', {}).get(p, 0) for p in probe_keys]
    gamma_vals = [matrix.get('NOVA_GAMMA', {}).get(p, 0) for p in probe_keys]

    bars1 = ax.bar(x - width, full_vals, width, label='FULL (~2000 tokens)',
                   color=COLORS['full'], edgecolor='black', linewidth=1)
    bars2 = ax.bar(x, t3_vals, width, label='T3 (~800 tokens)',
                   color=COLORS['t3'], edgecolor='black', linewidth=1)
    bars3 = ax.bar(x + width, gamma_vals, width, label='GAMMA (~100 tokens)',
                   color=COLORS['gamma'], edgecolor='black', linewidth=1)

    # Add threshold lines
    ax.axhline(y=0.5, color='orange', linestyle='--', linewidth=2, label='MODERATE threshold')
    ax.axhline(y=0.7, color='red', linestyle='--', linewidth=2, label='HIGH threshold')

    # Value labels on bars
    for bars in [bars1, bars2, bars3]:
        for bar in bars:
            height = bar.get_height()
            ax.annotate(f'{height:.2f}',
                       xy=(bar.get_x() + bar.get_width() / 2, height),
                       xytext=(0, 3), textcoords="offset points",
                       ha='center', va='bottom', fontsize=8, fontweight='bold')

    ax.set_ylabel('Cheat Score (Cosine Similarity)', fontsize=12)
    ax.set_xlabel('Probe Domain', fontsize=12)
    ax.set_title('PRE-FLIGHT VALIDATION: Context-Probe Overlap by Domain\n' +
                '(Lower = better - probes are genuinely novel)',
                fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels(probe_keys, rotation=45, ha='right', fontsize=11)
    ax.legend(loc='upper left', fontsize=10)
    ax.set_ylim(0, 1.0)
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig(output_dir / 'preflight_bars.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: preflight_bars.png")
    plt.close()

# =============================================================================
# PFI VISUALIZATIONS
# =============================================================================

def plot_pfi_by_probe(exp1_data, output_dir):
    """Bar chart of PFI scores by probe domain."""
    if not exp1_data:
        print("  No EXP1 data available")
        return

    pfi_results = exp1_data.get('pfi_results', [])
    if not pfi_results:
        print("  No PFI results in EXP1 data")
        return

    # Group by probe
    from collections import defaultdict
    by_probe = defaultdict(list)
    for r in pfi_results:
        by_probe[r['probe_key']].append(r['pfi'])

    probes = list(by_probe.keys())
    means = [np.mean(by_probe[p]) for p in probes]
    stds = [np.std(by_probe[p]) for p in probes]

    fig, ax = plt.subplots(figsize=(12, 7))

    x = np.arange(len(probes))
    colors = [PROBE_COLORS.get(p, 'gray') for p in probes]

    bars = ax.bar(x, means, yerr=stds, capsize=5, color=colors,
                  edgecolor='black', linewidth=2)

    # Threshold line
    ax.axhline(y=0.80, color=COLORS['threshold'], linestyle='--', linewidth=3,
              label='Threshold (0.80)')

    # Value labels
    for i, (bar, mean) in enumerate(zip(bars, means)):
        color = COLORS['pass'] if mean >= 0.80 else COLORS['fail']
        ax.annotate(f'{mean:.3f}',
                   xy=(bar.get_x() + bar.get_width() / 2, mean),
                   xytext=(0, 5), textcoords="offset points",
                   ha='center', va='bottom', fontsize=12, fontweight='bold',
                   color=color)

    # Summary stats
    summary = exp1_data.get('summary', {})
    mean_pfi = summary.get('mean_pfi', np.mean(means))

    ax.set_ylabel('PFI (Persona Fidelity Index)', fontsize=12)
    ax.set_xlabel('Probe Domain', fontsize=12)
    ax.set_title(f'EXP1-SSTACK: PFI by Probe Domain\n' +
                f'(Mean PFI: {mean_pfi:.4f} - {"PASSED" if mean_pfi >= 0.80 else "FAILED"})',
                fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels(probes, rotation=45, ha='right', fontsize=11)
    ax.set_ylim(0.6, 1.0)
    ax.legend(loc='lower right', fontsize=11)
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig(output_dir / 'pfi_by_probe.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / 'pfi_by_probe.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: pfi_by_probe.png + .svg")
    plt.close()

def plot_pfi_runs(exp1_data, output_dir):
    """Scatter plot of individual PFI measurements per run."""
    if not exp1_data:
        print("  No EXP1 data available")
        return

    pfi_results = exp1_data.get('pfi_results', [])
    if not pfi_results:
        return

    fig, ax = plt.subplots(figsize=(14, 7))

    # Group by probe
    probes = list(set(r['probe_key'] for r in pfi_results))
    probes.sort()

    for i, probe in enumerate(probes):
        probe_data = [r for r in pfi_results if r['probe_key'] == probe]
        runs = [r['run'] for r in probe_data]
        pfis = [r['pfi'] for r in probe_data]

        color = PROBE_COLORS.get(probe, 'gray')
        ax.scatter([i + (r-2)*0.15 for r in runs], pfis,
                  color=color, s=150, alpha=0.8, edgecolors='black', linewidth=1,
                  label=probe if i == 0 else None)

        # Mean line
        mean = np.mean(pfis)
        ax.hlines(mean, i - 0.4, i + 0.4, colors=color, linewidth=3, alpha=0.5)

    # Threshold
    ax.axhline(y=0.80, color=COLORS['threshold'], linestyle='--', linewidth=3,
              label='Threshold (0.80)')

    ax.set_ylabel('PFI Score', fontsize=12)
    ax.set_xlabel('Probe Domain', fontsize=12)
    ax.set_title('EXP1-SSTACK: Individual PFI Measurements\n' +
                '(Each dot = one FULL vs T3 comparison)',
                fontsize=14, fontweight='bold')
    ax.set_xticks(range(len(probes)))
    ax.set_xticklabels(probes, rotation=45, ha='right', fontsize=11)
    ax.set_ylim(0.65, 1.0)
    ax.grid(True, alpha=0.3, axis='y')

    # Add probe colors to legend
    from matplotlib.lines import Line2D
    legend_handles = []
    for probe in probes:
        color = PROBE_COLORS.get(probe, 'gray')
        legend_handles.append(Line2D([0], [0], marker='o', color='w',
                                     markerfacecolor=color, markersize=10, label=probe))
    legend_handles.append(Line2D([0], [0], color=COLORS['threshold'], linestyle='--',
                                linewidth=2, label='Threshold'))
    ax.legend(handles=legend_handles, loc='lower right', fontsize=9)

    plt.tight_layout()
    plt.savefig(output_dir / 'pfi_runs.png', dpi=300, bbox_inches='tight')
    print(f"  Saved: pfi_runs.png")
    plt.close()

# =============================================================================
# COMBINED VISUALIZATION
# =============================================================================

def plot_combined_dashboard(preflight_data, exp1_data, output_dir):
    """Combined dashboard showing preflight + PFI together."""
    fig = plt.figure(figsize=(18, 14))

    # Layout: 2x2 grid
    gs = fig.add_gridspec(2, 2, hspace=0.3, wspace=0.3)

    # Panel 1: Preflight heatmap (top-left)
    ax1 = fig.add_subplot(gs[0, 0])
    if preflight_data:
        matrix = preflight_data.get('matrix', {})
        probe_keys = [k for k in list(matrix.get('NOVA_FULL', {}).keys()) if k != 'ALL_COMBINED']
        contexts = ['NOVA_FULL', 'NOVA_T3', 'NOVA_GAMMA']

        data = np.array([
            [matrix.get(ctx, {}).get(probe, 0) for probe in probe_keys]
            for ctx in contexts
        ])

        from matplotlib.colors import LinearSegmentedColormap
        cmap_colors = ['#2a9d8f', '#e9c46a', '#e76f51']
        cmap = LinearSegmentedColormap.from_list('cheat', cmap_colors)

        im = ax1.imshow(data, cmap=cmap, aspect='auto', vmin=0, vmax=0.8)
        ax1.set_xticks(range(len(probe_keys)))
        ax1.set_xticklabels(probe_keys, rotation=45, ha='right', fontsize=9)
        ax1.set_yticks(range(len(contexts)))
        ax1.set_yticklabels(['FULL', 'T3', 'GAMMA'], fontsize=10)

        for i in range(len(contexts)):
            for j in range(len(probe_keys)):
                value = data[i, j]
                text_color = 'white' if value > 0.5 else 'black'
                ax1.text(j, i, f'{value:.2f}', ha='center', va='center',
                        fontsize=9, fontweight='bold', color=text_color)

        ax1.set_title('PREFLIGHT: Cheat Score Matrix', fontsize=12, fontweight='bold')
    else:
        ax1.text(0.5, 0.5, 'No preflight data', ha='center', va='center', fontsize=14)

    # Panel 2: PFI by probe (top-right)
    ax2 = fig.add_subplot(gs[0, 1])
    if exp1_data:
        pfi_results = exp1_data.get('pfi_results', [])
        from collections import defaultdict
        by_probe = defaultdict(list)
        for r in pfi_results:
            by_probe[r['probe_key']].append(r['pfi'])

        probes = list(by_probe.keys())
        means = [np.mean(by_probe[p]) for p in probes]
        stds = [np.std(by_probe[p]) for p in probes]
        colors = [PROBE_COLORS.get(p, 'gray') for p in probes]

        bars = ax2.bar(range(len(probes)), means, yerr=stds, capsize=4, color=colors,
                      edgecolor='black', linewidth=1)
        ax2.axhline(y=0.80, color=COLORS['threshold'], linestyle='--', linewidth=2)
        ax2.set_xticks(range(len(probes)))
        ax2.set_xticklabels(probes, rotation=45, ha='right', fontsize=9)
        ax2.set_ylabel('PFI', fontsize=10)
        ax2.set_ylim(0.6, 1.0)

        mean_pfi = exp1_data.get('summary', {}).get('mean_pfi', np.mean(means))
        status = "PASSED" if mean_pfi >= 0.80 else "FAILED"
        ax2.set_title(f'PFI by Probe Domain (Mean: {mean_pfi:.3f} - {status})',
                     fontsize=12, fontweight='bold')
    else:
        ax2.text(0.5, 0.5, 'No PFI data', ha='center', va='center', fontsize=14)

    # Panel 3: Combined scatter - PFI vs Cheat Score (bottom-left)
    ax3 = fig.add_subplot(gs[1, 0])
    if preflight_data and exp1_data:
        pfi_results = exp1_data.get('pfi_results', [])
        matrix = preflight_data.get('matrix', {})

        from collections import defaultdict
        by_probe = defaultdict(list)
        for r in pfi_results:
            by_probe[r['probe_key']].append(r['pfi'])

        for probe in by_probe.keys():
            cheat_full = matrix.get('NOVA_FULL', {}).get(probe, 0)
            cheat_t3 = matrix.get('NOVA_T3', {}).get(probe, 0)
            avg_cheat = (cheat_full + cheat_t3) / 2

            mean_pfi = np.mean(by_probe[probe])
            std_pfi = np.std(by_probe[probe])

            color = PROBE_COLORS.get(probe, 'gray')
            ax3.scatter(avg_cheat, mean_pfi, s=200, c=color, alpha=0.8,
                       edgecolors='black', linewidth=2, label=probe)
            ax3.errorbar(avg_cheat, mean_pfi, yerr=std_pfi, color=color, alpha=0.5,
                        capsize=5, capthick=2, linestyle='none')

        ax3.axhline(y=0.80, color=COLORS['threshold'], linestyle='--', linewidth=2,
                   label='PFI Threshold')
        ax3.axvline(x=0.5, color='orange', linestyle=':', linewidth=2,
                   label='Cheat Caution')

        ax3.set_xlabel('Avg Cheat Score (FULL + T3)', fontsize=10)
        ax3.set_ylabel('Mean PFI', fontsize=10)
        ax3.set_title('PFI vs Cheat Score by Probe\n(Lower-right = genuine high fidelity)',
                     fontsize=12, fontweight='bold')
        ax3.legend(loc='lower left', fontsize=8)
        ax3.set_xlim(0, 0.8)
        ax3.set_ylim(0.7, 1.0)
        ax3.grid(True, alpha=0.3)
    else:
        ax3.text(0.5, 0.5, 'Insufficient data', ha='center', va='center', fontsize=14)

    # Panel 4: Summary stats (bottom-right)
    ax4 = fig.add_subplot(gs[1, 1])
    ax4.axis('off')

    summary_text = "EXP1-SSTACK SUMMARY\n" + "="*40 + "\n\n"

    if exp1_data:
        s = exp1_data.get('summary', {})
        summary_text += f"Mean PFI: {s.get('mean_pfi', 'N/A'):.4f}\n"
        summary_text += f"Std PFI:  {s.get('std_pfi', 'N/A'):.4f}\n"
        summary_text += f"Min PFI:  {s.get('min_pfi', 'N/A'):.4f}\n"
        summary_text += f"Threshold: 0.80\n"
        summary_text += f"Status: {'PASSED' if s.get('passed') else 'FAILED'}\n\n"

    if preflight_data:
        interp = preflight_data.get('summary', {}).get('interpretation', {})
        validity = interp.get('overall_validity', 'N/A')
        summary_text += f"Pre-Flight Validity: {validity}\n\n"

        summary_text += "Cheat Score Summary:\n"
        for ctx in ['NOVA_FULL', 'NOVA_T3', 'NOVA_GAMMA']:
            ctx_data = preflight_data.get('summary', {}).get(ctx, {})
            mean = ctx_data.get('mean_cheat_score', 0)
            status = interp.get(ctx, {}).get('status', 'N/A')
            summary_text += f"  {ctx}: {mean:.3f} ({status})\n"

    summary_text += "\n" + "="*40 + "\n"
    summary_text += "Fidelity vs Correctness:\n"
    summary_text += "We don't care if the answer is RIGHT.\n"
    summary_text += "We care if T3 sounds like FULL.\n"

    ax4.text(0.1, 0.9, summary_text, transform=ax4.transAxes, fontsize=11,
            verticalalignment='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    fig.suptitle('COMPRESSION EXPERIMENTS: Pre-Flight + PFI Analysis\n' +
                '(The Bedrock Fundamentals)',
                fontsize=16, fontweight='bold', y=0.98)

    plt.savefig(output_dir / 'compression_dashboard.png', dpi=300, bbox_inches='tight')
    plt.savefig(output_dir / 'compression_dashboard.svg', format='svg', bbox_inches='tight')
    print(f"  Saved: compression_dashboard.png + .svg")
    plt.close()

# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description='Compression Experiment Visualization')
    parser.add_argument('--preflight', action='store_true', help='Just preflight visualizations')
    parser.add_argument('--pfi', action='store_true', help='Just PFI visualizations')
    parser.add_argument('--dashboard', action='store_true', help='Just combined dashboard')
    args = parser.parse_args()

    print("=" * 60)
    print("COMPRESSION VISUALIZATION")
    print("=" * 60)

    # Load data
    preflight_data = load_preflight_results()
    exp1_data = load_exp1_results()

    print(f"\nPreflight data: {'Found' if preflight_data else 'Not found'}")
    print(f"EXP1 data: {'Found' if exp1_data else 'Not found'}")

    # Create output directories
    output_dirs = {
        'preflight': OUTPUT_DIR / '1_preflight',
        'pfi': OUTPUT_DIR / '2_pfi_analysis',
        'dashboard': OUTPUT_DIR / '3_dashboard',
    }
    for d in output_dirs.values():
        d.mkdir(parents=True, exist_ok=True)

    print(f"\nOutput: {OUTPUT_DIR}")
    print("-" * 60)

    # Generate visualizations
    if args.preflight or not (args.pfi or args.dashboard):
        print("\nGenerating preflight visualizations...")
        plot_preflight_heatmap(preflight_data, output_dirs['preflight'])
        plot_preflight_bar(preflight_data, output_dirs['preflight'])

    if args.pfi or not (args.preflight or args.dashboard):
        print("\nGenerating PFI visualizations...")
        plot_pfi_by_probe(exp1_data, output_dirs['pfi'])
        plot_pfi_runs(exp1_data, output_dirs['pfi'])

    if args.dashboard or not (args.preflight or args.pfi):
        print("\nGenerating combined dashboard...")
        plot_combined_dashboard(preflight_data, exp1_data, output_dirs['dashboard'])

    print("\n" + "-" * 60)
    print("COMPLETE!")
    print(f"All outputs in: {OUTPUT_DIR}")
    print("=" * 60)

if __name__ == "__main__":
    main()
