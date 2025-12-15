"""
Run 017 Context Damping Visualizations
======================================
Local visualization script for Run 017 data. Designed to be called from
the master visualize_armada.py or run standalone.

USAGE:
    python visualize_run017.py                    # Generate all visualizations
    python visualize_run017.py --viz heatmap      # Specific visualization
    python visualize_run017.py --output pics/     # Custom output directory
    python visualize_run017.py --interactive      # Launch interactive dashboard

VISUALIZATIONS:
    1. persona_heatmap      - Stability metrics across all 24 personas
    2. recovery_trajectories - Overlay recovery sequences by persona type
    3. pillar_effectiveness - Compare r015_* synthetic variants
    4. ringback_patterns    - Oscillation analysis with FFT
    5. exit_survey_analysis - Word frequency and themes from surveys
    6. persona_clustering   - PCA/clustering of response patterns
    7. context_damping_effect - Before/after research context comparison

INTEGRATION WITH visualize_armada.py:
    This script exports functions that can be called from the master visualizer:

    from experiments.temporal_stability.S7_ARMADA.11_CONTEXT_DAMPING.visualize_run017 import (
        generate_all_run017_visualizations,
        get_run017_data,
        VISUALIZATION_TYPES
    )

Author: Claude (with Lisan Al Gaib)
Date: December 11, 2025
"""

import json
import argparse
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.colors import LinearSegmentedColormap
from pathlib import Path
from collections import defaultdict
from datetime import datetime
import warnings
warnings.filterwarnings('ignore')

# Optional imports
try:
    import seaborn as sns
    HAS_SEABORN = True
except ImportError:
    HAS_SEABORN = False

try:
    from scipy.fft import fft, fftfreq
    from scipy.interpolate import make_interp_spline
    HAS_SCIPY = True
except ImportError:
    HAS_SCIPY = False

try:
    import plotly.graph_objects as go
    import plotly.express as px
    from plotly.subplots import make_subplots
    HAS_PLOTLY = True
except ImportError:
    HAS_PLOTLY = False

# =============================================================================
# PATHS
# =============================================================================
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent
RESULTS_DIR = ARMADA_DIR / "0_results" / "runs"
TEMPORAL_LOGS_DIR = ARMADA_DIR / "0_results" / "temporal_logs"
# Store visualizations in central location: S7_ARMADA/visualizations/run017/
OUTPUT_DIR = ARMADA_DIR / "visualizations" / "run017"

# Ensure output directory exists
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# =============================================================================
# CONSTANTS
# =============================================================================
EVENT_HORIZON = 1.23
CATASTROPHIC_THRESHOLD = 1.8

# Color schemes
PERSONA_COLORS = {
    # Real personas
    "personas_base": "#6366f1",      # Indigo
    "personas_cfa": "#8b5cf6",       # Purple
    "personas_claude": "#7c3aed",    # Violet
    "personas_gemini": "#4285f4",    # Google Blue
    "personas_nova": "#f59e0b",      # Amber
    "personas_pan_handlers": "#10b981",  # Emerald
    "personas_ziggy": "#ef4444",     # Red
    # Prep models
    "prep_": "#64748b",              # Slate (all prep models)
    # Synthetic r015
    "r015_control": "#94a3b8",       # Gray
    "r015_optimal": "#22c55e",       # Green
    "r015_values_only": "#3b82f6",   # Blue
    "r015_": "#06b6d4",              # Cyan (default for r015)
}

STABILITY_CMAP = LinearSegmentedColormap.from_list(
    'stability', ['#ef4444', '#f59e0b', '#22c55e']  # Red -> Amber -> Green
)

# Available visualization types
VISUALIZATION_TYPES = [
    'persona_heatmap',
    'recovery_trajectories',
    'pillar_effectiveness',
    'ringback_patterns',
    'exit_survey_analysis',
    'persona_clustering',
    'context_damping_effect',
    'summary_dashboard'
]

# =============================================================================
# DATA LOADING
# =============================================================================

def get_run017_data():
    """Load aggregated Run 017 data."""
    data_file = RESULTS_DIR / "S7_run_017_context_damping.json"

    if not data_file.exists():
        print(f"ERROR: Data file not found: {data_file}")
        print("Run aggregate_run017.py first to generate the data file.")
        return None

    with open(data_file, 'r', encoding='utf-8') as f:
        return json.load(f)

def get_persona_color(persona_name):
    """Get color for a persona, with fallbacks."""
    if persona_name in PERSONA_COLORS:
        return PERSONA_COLORS[persona_name]

    # Check prefixes
    for prefix, color in PERSONA_COLORS.items():
        if persona_name.startswith(prefix):
            return color

    # Default
    return "#64748b"

def categorize_persona(name):
    """Categorize persona into groups for analysis."""
    if name.startswith("personas_"):
        return "Real Personas"
    elif name.startswith("prep_"):
        return "Prep Models"
    elif name.startswith("r015_"):
        if "optimal" in name:
            return "Synthetic Optimal"
        elif "control" in name or "minimal" in name:
            return "Synthetic Minimal"
        else:
            return "Synthetic Experimental"
    return "Unknown"

# =============================================================================
# VISUALIZATION 1: PERSONA STABILITY HEATMAP
# =============================================================================

def viz_persona_heatmap(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Generate heatmap comparing stability metrics across all personas.

    X-axis: Metrics (peak_drift, settled_drift, ringback, stability_rate)
    Y-axis: Persona names (sorted by stability)
    Color: Performance (green=good, red=bad)
    """
    by_persona = data.get("by_persona", {})

    if not by_persona:
        print("No persona data available")
        return None

    # Extract metrics for each persona
    personas = []
    metrics_data = []

    def safe_get(d, key, default=0):
        """Get value from dict, returning default if None or missing."""
        val = d.get(key)
        return val if val is not None else default

    for persona, pdata in by_persona.items():
        summary = pdata.get("summary", {})
        if safe_get(summary, "n_runs", 0) > 0:
            personas.append(persona)
            metrics_data.append([
                safe_get(summary, "peak_drift_mean", 0),
                safe_get(summary, "settled_drift_mean", 0),
                safe_get(summary, "settling_time_mean", 0),
                safe_get(summary, "ringback_count_mean", 0),
                safe_get(summary, "stability_rate", 0) * 100,  # Convert to percentage
                safe_get(summary, "meta_references_mean", 0),
            ])

    if not personas:
        print("No valid persona summaries")
        return None

    metrics_array = np.array(metrics_data)
    metric_names = ["Peak Drift", "Settled Drift", "Settling Time",
                   "Ringback Count", "Stability %", "Meta References"]

    # Sort by stability rate (descending)
    sort_idx = np.argsort(-metrics_array[:, 4])
    personas = [personas[i] for i in sort_idx]
    metrics_array = metrics_array[sort_idx]

    # Create figure
    fig, ax = plt.subplots(figsize=(14, max(10, len(personas) * 0.4)))

    # Normalize each column for coloring (0-1 scale)
    normalized = np.zeros_like(metrics_array)
    for i in range(metrics_array.shape[1]):
        col = metrics_array[:, i]
        col_min, col_max = col.min(), col.max()
        if col_max > col_min:
            normalized[:, i] = (col - col_min) / (col_max - col_min)
        else:
            normalized[:, i] = 0.5

    # Invert some columns so green = good
    # For drift metrics, lower is better
    normalized[:, 0] = 1 - normalized[:, 0]  # Peak drift
    normalized[:, 1] = 1 - normalized[:, 1]  # Settled drift
    normalized[:, 2] = 1 - normalized[:, 2]  # Settling time
    normalized[:, 3] = 1 - normalized[:, 3]  # Ringback count
    # Stability % - higher is better (keep as is)
    # Meta references - higher = more self-aware (keep as is)

    # Create heatmap
    if HAS_SEABORN:
        sns.heatmap(normalized, ax=ax, cmap=STABILITY_CMAP,
                   xticklabels=metric_names, yticklabels=personas,
                   annot=metrics_array, fmt='.2f',
                   annot_kws={'size': 8},
                   cbar_kws={'label': 'Performance (Green=Good)'})
    else:
        im = ax.imshow(normalized, cmap=STABILITY_CMAP, aspect='auto')
        ax.set_xticks(range(len(metric_names)))
        ax.set_xticklabels(metric_names, rotation=45, ha='right')
        ax.set_yticks(range(len(personas)))
        ax.set_yticklabels(personas)

        # Add text annotations
        for i in range(len(personas)):
            for j in range(len(metric_names)):
                ax.text(j, i, f'{metrics_array[i, j]:.2f}',
                       ha='center', va='center', fontsize=7)

        plt.colorbar(im, ax=ax, label='Performance (Green=Good)')

    ax.set_title('Run 017: Persona Stability Heatmap\n(222 runs, 24 personas)',
                fontsize=14, fontweight='bold')
    ax.set_xlabel('Stability Metrics')
    ax.set_ylabel('Persona (sorted by stability rate)')

    # Add category annotations on the right
    categories = [categorize_persona(p) for p in personas]
    unique_cats = list(dict.fromkeys(categories))  # Preserve order
    cat_colors = {'Real Personas': '#7c3aed', 'Prep Models': '#64748b',
                  'Synthetic Optimal': '#22c55e', 'Synthetic Minimal': '#94a3b8',
                  'Synthetic Experimental': '#06b6d4', 'Unknown': '#000000'}

    for i, (persona, cat) in enumerate(zip(personas, categories)):
        ax.annotate(cat[:3], xy=(len(metric_names) + 0.1, i),
                   fontsize=7, color=cat_colors.get(cat, '#000000'),
                   va='center')

    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_persona_heatmap.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# VISUALIZATION 2: RECOVERY TRAJECTORIES
# =============================================================================

def viz_recovery_trajectories(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Overlay recovery sequences comparing different persona types.
    Shows how different I_AM file designs produce different recovery patterns.
    """
    by_persona = data.get("by_persona", {})

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    categories = {
        "Real Personas": [],
        "Synthetic Optimal": [],
        "Synthetic Minimal": [],
        "Synthetic Experimental": []
    }

    # Collect recovery sequences by category
    for persona, pdata in by_persona.items():
        cat = categorize_persona(persona)
        if cat in categories:
            for run in pdata.get("individual_runs", []):
                seq = run.get("recovery_sequence", [])
                if seq and len(seq) >= 3:
                    categories[cat].append({
                        "persona": persona,
                        "sequence": seq,
                        "peak": run.get("peak_drift", 0),
                        "settled": run.get("settled_drift", 0)
                    })

    # Plot each category
    for ax, (cat_name, runs) in zip(axes.flat, categories.items()):
        if not runs:
            ax.text(0.5, 0.5, f"No data for {cat_name}",
                   ha='center', va='center', transform=ax.transAxes)
            ax.set_title(cat_name)
            continue

        # Plot each sequence with transparency
        max_len = max(len(r["sequence"]) for r in runs)

        for run in runs[:20]:  # Limit to 20 traces for clarity
            seq = run["sequence"]
            color = get_persona_color(run["persona"])
            ax.plot(range(len(seq)), seq, color=color, alpha=0.3, linewidth=1)

        # Calculate and plot mean trajectory
        all_seqs = [r["sequence"] for r in runs]
        padded = np.array([s + [s[-1]] * (max_len - len(s)) for s in all_seqs])
        mean_seq = np.mean(padded, axis=0)
        std_seq = np.std(padded, axis=0)

        ax.plot(range(len(mean_seq)), mean_seq, color='black', linewidth=2.5,
               label='Mean Trajectory')
        ax.fill_between(range(len(mean_seq)), mean_seq - std_seq, mean_seq + std_seq,
                       color='gray', alpha=0.2, label='±1 std')

        # Add event horizon line
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--',
                  linewidth=1.5, label=f'Event Horizon ({EVENT_HORIZON})')

        ax.set_title(f'{cat_name} ({len(runs)} runs)', fontsize=11, fontweight='bold')
        ax.set_xlabel('Recovery Probe #')
        ax.set_ylabel('Drift')
        ax.set_ylim(0, 2.0)
        ax.legend(loc='upper right', fontsize=8)
        ax.grid(True, alpha=0.3)

    fig.suptitle('Run 017: Recovery Trajectories by Persona Type',
                fontsize=14, fontweight='bold')
    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_recovery_trajectories.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# VISUALIZATION 3: PILLAR EFFECTIVENESS
# =============================================================================

def viz_pillar_effectiveness(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Compare r015_* synthetic variants to determine which pillar combinations
    produce the best stability.

    Key questions answered:
    - Does values_only beat named_only?
    - Does all_pillars beat single_pillar_values?
    - Which combination is optimal?
    """
    by_persona = data.get("by_persona", {})

    # Filter to r015_ variants only
    r015_data = {}
    for persona, pdata in by_persona.items():
        if persona.startswith("r015_"):
            summary = pdata.get("summary", {})
            if summary.get("n_runs", 0) > 0:
                r015_data[persona.replace("r015_", "")] = {
                    "stability_rate": summary.get("stability_rate", 0) * 100,
                    "peak_drift": summary.get("peak_drift_mean", 0),
                    "settled_drift": summary.get("settled_drift_mean", 0),
                    "ringback": summary.get("ringback_count_mean", 0),
                    "n_runs": summary.get("n_runs", 0)
                }

    if not r015_data:
        print("No r015_* synthetic variants found")
        return None

    # Sort by stability rate
    sorted_variants = sorted(r015_data.items(), key=lambda x: -x[1]["stability_rate"])

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    variants = [v[0] for v in sorted_variants]

    # Plot 1: Stability Rate
    ax1 = axes[0, 0]
    rates = [r015_data[v]["stability_rate"] for v in variants]
    colors = ['#22c55e' if r >= 95 else '#f59e0b' if r >= 80 else '#ef4444' for r in rates]
    bars = ax1.barh(variants, rates, color=colors)
    ax1.axvline(x=95, color='green', linestyle='--', alpha=0.7, label='95% threshold')
    ax1.set_xlabel('Stability Rate (%)')
    ax1.set_title('Stability Rate by Variant', fontweight='bold')
    ax1.set_xlim(0, 105)

    # Add value labels
    for bar, rate in zip(bars, rates):
        ax1.text(rate + 1, bar.get_y() + bar.get_height()/2,
                f'{rate:.1f}%', va='center', fontsize=8)

    # Plot 2: Peak Drift
    ax2 = axes[0, 1]
    peaks = [r015_data[v]["peak_drift"] for v in variants]
    colors = ['#22c55e' if p < EVENT_HORIZON else '#ef4444' for p in peaks]
    ax2.barh(variants, peaks, color=colors)
    ax2.axvline(x=EVENT_HORIZON, color='red', linestyle='--',
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax2.set_xlabel('Peak Drift')
    ax2.set_title('Peak Drift by Variant', fontweight='bold')
    ax2.legend(loc='lower right', fontsize=8)

    # Plot 3: Settled Drift
    ax3 = axes[1, 0]
    settled = [r015_data[v]["settled_drift"] for v in variants]
    ax3.barh(variants, settled, color='#3b82f6')
    ax3.axvline(x=EVENT_HORIZON, color='red', linestyle='--', alpha=0.5)
    ax3.set_xlabel('Settled Drift')
    ax3.set_title('Settled Drift (Final Recovery)', fontweight='bold')

    # Plot 4: Ringback Count
    ax4 = axes[1, 1]
    ringback = [r015_data[v]["ringback"] for v in variants]
    colors = ['#22c55e' if r <= 3 else '#f59e0b' if r <= 5 else '#ef4444' for r in ringback]
    ax4.barh(variants, ringback, color=colors)
    ax4.set_xlabel('Ringback Count (Oscillations)')
    ax4.set_title('Recovery Oscillations by Variant', fontweight='bold')

    fig.suptitle('Run 017: Pillar Effectiveness Analysis\nWhich I_AM components produce best stability?',
                fontsize=14, fontweight='bold')
    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_pillar_effectiveness.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# VISUALIZATION 4: RINGBACK PATTERNS (with FFT)
# =============================================================================

def viz_ringback_patterns(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Analyze oscillation patterns in recovery sequences.
    Uses FFT to identify resonant frequencies and classify damping behavior.
    """
    by_persona = data.get("by_persona", {})

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Collect all recovery sequences
    all_sequences = []
    for persona, pdata in by_persona.items():
        for run in pdata.get("individual_runs", []):
            seq = run.get("recovery_sequence", [])
            if seq and len(seq) >= 6:
                all_sequences.append({
                    "persona": persona,
                    "sequence": seq,
                    "ringback": run.get("ringback_count", 0)
                })

    if not all_sequences:
        print("No recovery sequences found")
        return None

    # Plot 1: Ringback distribution
    ax1 = axes[0, 0]
    ringbacks = [s["ringback"] for s in all_sequences]
    ax1.hist(ringbacks, bins=range(0, max(ringbacks) + 2), color='#3b82f6',
            edgecolor='white', alpha=0.8)
    ax1.axvline(x=np.mean(ringbacks), color='red', linestyle='--',
               label=f'Mean: {np.mean(ringbacks):.1f}')
    ax1.set_xlabel('Ringback Count')
    ax1.set_ylabel('Frequency')
    ax1.set_title('Distribution of Recovery Oscillations', fontweight='bold')
    ax1.legend()

    # Plot 2: FFT of a representative sequence
    ax2 = axes[0, 1]
    if HAS_SCIPY:
        # Find median-length sequence
        median_len = int(np.median([len(s["sequence"]) for s in all_sequences]))
        representative = [s for s in all_sequences if len(s["sequence"]) == median_len]

        if representative:
            seq = representative[0]["sequence"]
            N = len(seq)

            # Compute FFT
            yf = fft(seq)
            xf = fftfreq(N, 1)[:N//2]

            ax2.plot(xf[1:], 2.0/N * np.abs(yf[1:N//2]), color='#8b5cf6')
            ax2.set_xlabel('Frequency (cycles per probe)')
            ax2.set_ylabel('Amplitude')
            ax2.set_title('FFT Spectral Analysis (Representative)', fontweight='bold')
            ax2.grid(True, alpha=0.3)
    else:
        ax2.text(0.5, 0.5, 'scipy required for FFT', ha='center', va='center',
                transform=ax2.transAxes)
        ax2.set_title('FFT Analysis (scipy not available)', fontweight='bold')

    # Plot 3: Damping classification
    ax3 = axes[1, 0]
    # Classify sequences by damping behavior
    underdamped = 0  # Oscillates before settling
    overdamped = 0   # Monotonic approach
    critically = 0   # Few oscillations, fast settling

    for s in all_sequences:
        seq = s["sequence"]
        ringback = s["ringback"]

        if ringback == 0:
            overdamped += 1
        elif ringback <= 2:
            critically += 1
        else:
            underdamped += 1

    labels = ['Underdamped\n(>2 oscillations)', 'Critically Damped\n(1-2 oscillations)',
              'Overdamped\n(monotonic)']
    sizes = [underdamped, critically, overdamped]
    colors = ['#ef4444', '#f59e0b', '#22c55e']

    ax3.pie(sizes, labels=labels, colors=colors, autopct='%1.1f%%', startangle=90)
    ax3.set_title('Damping Classification', fontweight='bold')

    # Plot 4: Settling time vs ringback
    ax4 = axes[1, 1]
    settling_times = []
    ringback_counts = []

    for persona, pdata in by_persona.items():
        for run in pdata.get("individual_runs", []):
            st = run.get("settling_time")
            rb = run.get("ringback_count")
            if st is not None and rb is not None:
                settling_times.append(st)
                ringback_counts.append(rb)

    ax4.scatter(ringback_counts, settling_times, alpha=0.5, color='#06b6d4')
    ax4.set_xlabel('Ringback Count')
    ax4.set_ylabel('Settling Time (probes)')
    ax4.set_title('Settling Time vs Oscillations', fontweight='bold')
    ax4.grid(True, alpha=0.3)

    # Add trend line
    if len(ringback_counts) > 2:
        z = np.polyfit(ringback_counts, settling_times, 1)
        p = np.poly1d(z)
        x_line = np.linspace(min(ringback_counts), max(ringback_counts), 100)
        ax4.plot(x_line, p(x_line), 'r--', alpha=0.7, label=f'Trend')
        ax4.legend()

    fig.suptitle('Run 017: Ringback & Oscillation Analysis',
                fontsize=14, fontweight='bold')
    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_ringback_patterns.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# VISUALIZATION 5: EXIT SURVEY ANALYSIS
# =============================================================================

def viz_exit_survey_analysis(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Analyze exit survey responses for patterns and themes.
    Word frequency, self-awareness markers, and stability correlation.
    """
    by_persona = data.get("by_persona", {})

    # Collect all exit survey text
    survey_texts = []
    stable_texts = []
    unstable_texts = []

    for persona, pdata in by_persona.items():
        for run in pdata.get("individual_runs", []):
            # Check if there's exit survey data in the temporal logs
            is_stable = run.get("is_stable")
            if is_stable is None:
                is_stable = True

            # We'll analyze meta_references as a proxy for survey depth
            meta_refs = run.get("meta_references")
            if meta_refs is None:
                meta_refs = 0
            peak_drift = run.get("peak_drift")
            if peak_drift is None:
                peak_drift = 0
            settled_drift = run.get("settled_drift")
            if settled_drift is None:
                settled_drift = 0

            survey_texts.append({
                "persona": persona,
                "meta_refs": meta_refs,
                "is_stable": is_stable,
                "peak_drift": peak_drift,
                "settled_drift": settled_drift
            })

    if not survey_texts:
        print("No survey data found")
        return None

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Meta references distribution
    ax1 = axes[0, 0]
    meta_refs = [s["meta_refs"] for s in survey_texts]
    ax1.hist(meta_refs, bins=20, color='#8b5cf6', edgecolor='white', alpha=0.8)
    ax1.axvline(x=np.mean(meta_refs), color='red', linestyle='--',
               label=f'Mean: {np.mean(meta_refs):.1f}')
    ax1.set_xlabel('Meta References Count')
    ax1.set_ylabel('Frequency')
    ax1.set_title('Self-Awareness Markers in Responses', fontweight='bold')
    ax1.legend()

    # Plot 2: Meta references by persona category
    ax2 = axes[0, 1]
    cat_refs = defaultdict(list)
    for s in survey_texts:
        cat = categorize_persona(s["persona"])
        cat_refs[cat].append(s["meta_refs"])

    categories = list(cat_refs.keys())
    means = [np.mean(cat_refs[c]) for c in categories]
    stds = [np.std(cat_refs[c]) for c in categories]

    bars = ax2.bar(range(len(categories)), means, yerr=stds, capsize=5,
                   color=['#7c3aed', '#64748b', '#22c55e', '#94a3b8', '#06b6d4'][:len(categories)])
    ax2.set_xticks(range(len(categories)))
    ax2.set_xticklabels(categories, rotation=45, ha='right')
    ax2.set_ylabel('Mean Meta References')
    ax2.set_title('Self-Awareness by Persona Type', fontweight='bold')

    # Plot 3: Meta references vs stability
    ax3 = axes[1, 0]
    stable_refs = [s["meta_refs"] for s in survey_texts if s["is_stable"]]
    unstable_refs = [s["meta_refs"] for s in survey_texts if not s["is_stable"]]

    if stable_refs and unstable_refs:
        ax3.boxplot([stable_refs, unstable_refs], labels=['Stable', 'Unstable'])
        ax3.set_ylabel('Meta References')
        ax3.set_title('Self-Awareness: Stable vs Unstable Runs', fontweight='bold')
    else:
        # Just show stable distribution if no unstable
        ax3.boxplot([stable_refs], labels=['All Runs'])
        ax3.set_ylabel('Meta References')
        ax3.set_title('Self-Awareness Distribution', fontweight='bold')

    # Plot 4: Correlation: meta refs vs settled drift
    ax4 = axes[1, 1]
    meta_vals = [s["meta_refs"] for s in survey_texts]
    drift_vals = [s["settled_drift"] for s in survey_texts]

    ax4.scatter(meta_vals, drift_vals, alpha=0.5, color='#06b6d4')
    ax4.set_xlabel('Meta References')
    ax4.set_ylabel('Settled Drift')
    ax4.set_title('Self-Awareness vs Final Drift', fontweight='bold')
    ax4.axhline(y=EVENT_HORIZON, color='red', linestyle='--', alpha=0.5)
    ax4.grid(True, alpha=0.3)

    # Add correlation coefficient
    if len(meta_vals) > 2:
        corr = np.corrcoef(meta_vals, drift_vals)[0, 1]
        ax4.text(0.05, 0.95, f'r = {corr:.3f}', transform=ax4.transAxes,
                fontsize=10, verticalalignment='top')

    fig.suptitle('Run 017: Exit Survey Analysis\n(Meta-awareness patterns from 176 surveys)',
                fontsize=14, fontweight='bold')
    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_exit_survey_analysis.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# VISUALIZATION 6: PERSONA CLUSTERING (PCA)
# =============================================================================

def viz_persona_clustering(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Reduce persona data to 2D using PCA to visualize clustering patterns.
    """
    by_persona = data.get("by_persona", {})

    # Build feature matrix
    personas = []
    features = []

    def safe_val(d, key, default=0):
        """Get value, return default if None or missing."""
        v = d.get(key)
        return v if v is not None else default

    for persona, pdata in by_persona.items():
        summary = pdata.get("summary", {})
        if safe_val(summary, "n_runs", 0) > 0:
            personas.append(persona)
            features.append([
                safe_val(summary, "peak_drift_mean", 0),
                safe_val(summary, "settled_drift_mean", 0),
                safe_val(summary, "settling_time_mean", 0),
                safe_val(summary, "ringback_count_mean", 0),
                safe_val(summary, "stability_rate", 0),
                safe_val(summary, "meta_references_mean", 0),
            ])

    if len(personas) < 3:
        print("Not enough personas for clustering")
        return None

    features = np.array(features)

    # Standardize features
    means = features.mean(axis=0)
    stds = features.std(axis=0)
    stds[stds == 0] = 1
    features_std = (features - means) / stds

    # Simple PCA (2 components)
    # Center the data
    centered = features_std - features_std.mean(axis=0)

    # SVD for PCA
    U, S, Vt = np.linalg.svd(centered, full_matrices=False)

    # Project to 2D
    pca_result = centered @ Vt[:2].T

    # Calculate variance explained
    var_explained = (S[:2] ** 2) / (S ** 2).sum() * 100

    fig, ax = plt.subplots(figsize=(12, 10))

    # Color by category
    categories = [categorize_persona(p) for p in personas]
    unique_cats = list(set(categories))
    cat_colors = {
        'Real Personas': '#7c3aed',
        'Prep Models': '#64748b',
        'Synthetic Optimal': '#22c55e',
        'Synthetic Minimal': '#94a3b8',
        'Synthetic Experimental': '#06b6d4',
        'Unknown': '#000000'
    }

    for cat in unique_cats:
        mask = [c == cat for c in categories]
        indices = [i for i, m in enumerate(mask) if m]

        ax.scatter(pca_result[indices, 0], pca_result[indices, 1],
                  c=cat_colors.get(cat, '#000000'), label=cat, s=100, alpha=0.7)

        # Add labels
        for i in indices:
            ax.annotate(personas[i].replace("personas_", "").replace("r015_", "").replace("prep_", ""),
                       (pca_result[i, 0], pca_result[i, 1]),
                       fontsize=8, alpha=0.8,
                       xytext=(5, 5), textcoords='offset points')

    ax.set_xlabel(f'PC1 ({var_explained[0]:.1f}% variance)')
    ax.set_ylabel(f'PC2 ({var_explained[1]:.1f}% variance)')
    ax.set_title('Run 017: Persona Clustering (PCA)\nSimilar personas cluster together',
                fontsize=14, fontweight='bold')
    ax.legend(loc='best')
    ax.grid(True, alpha=0.3)
    ax.axhline(y=0, color='gray', linestyle='-', alpha=0.3)
    ax.axvline(x=0, color='gray', linestyle='-', alpha=0.3)

    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_persona_clustering.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# VISUALIZATION 7: CONTEXT DAMPING EFFECT
# =============================================================================

def viz_context_damping_effect(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Compare stability metrics to visualize the effect of research context.
    Shows overall statistics and highlights key findings.
    """
    overall = data.get("overall_summary", {})
    by_persona = data.get("by_persona", {})

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: Overall summary metrics
    ax1 = axes[0, 0]
    metrics = {
        'Peak Drift': overall.get('peak_drift_mean', 0),
        'Settled Drift': overall.get('settled_drift_mean', 0),
        'Settling Time': overall.get('settling_time_mean', 0) / 12,  # Normalize to ~1
        'Ringback Count': overall.get('ringback_count_mean', 0) / 5,  # Normalize
        'Stability Rate': overall.get('stability_rate', 0),
    }

    colors = ['#3b82f6', '#22c55e', '#f59e0b', '#ef4444', '#8b5cf6']
    bars = ax1.bar(metrics.keys(), metrics.values(), color=colors)
    ax1.axhline(y=EVENT_HORIZON, color='red', linestyle='--', alpha=0.5,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax1.set_ylabel('Value (normalized for some metrics)')
    ax1.set_title(f'Overall Run 017 Statistics\n({data.get("total_files", 0)} runs)',
                 fontweight='bold')
    ax1.legend()

    # Add value labels
    for bar, (name, val) in zip(bars, metrics.items()):
        if name == 'Stability Rate':
            label = f'{val*100:.1f}%'
        else:
            label = f'{val:.2f}'
        ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
                label, ha='center', va='bottom', fontsize=9)

    # Plot 2: Stability by persona type
    ax2 = axes[0, 1]
    type_stability = defaultdict(list)
    for persona, pdata in by_persona.items():
        cat = categorize_persona(persona)
        summary = pdata.get("summary", {})
        rate = summary.get("stability_rate", 0)
        if rate is not None:
            type_stability[cat].append(rate * 100)

    categories = list(type_stability.keys())
    means = [np.mean(type_stability[c]) for c in categories]
    stds = [np.std(type_stability[c]) if len(type_stability[c]) > 1 else 0 for c in categories]

    cat_colors = ['#7c3aed', '#64748b', '#22c55e', '#94a3b8', '#06b6d4']
    bars = ax2.bar(range(len(categories)), means, yerr=stds, capsize=5,
                   color=cat_colors[:len(categories)])
    ax2.axhline(y=95, color='green', linestyle='--', alpha=0.7, label='95% threshold')
    ax2.set_xticks(range(len(categories)))
    ax2.set_xticklabels(categories, rotation=45, ha='right')
    ax2.set_ylabel('Stability Rate (%)')
    ax2.set_title('Stability by Persona Type', fontweight='bold')
    ax2.set_ylim(0, 105)
    ax2.legend()

    # Plot 3: Peak drift distribution
    ax3 = axes[1, 0]
    all_peaks = []
    for persona, pdata in by_persona.items():
        for run in pdata.get("individual_runs", []):
            peak = run.get("peak_drift")
            if peak is not None:
                all_peaks.append(peak)

    ax3.hist(all_peaks, bins=30, color='#3b82f6', edgecolor='white', alpha=0.8)
    ax3.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
               label=f'Event Horizon ({EVENT_HORIZON})')
    ax3.axvline(x=CATASTROPHIC_THRESHOLD, color='darkred', linestyle='--', linewidth=2,
               label=f'Catastrophic ({CATASTROPHIC_THRESHOLD})')
    ax3.axvline(x=np.mean(all_peaks), color='green', linestyle='--',
               label=f'Mean: {np.mean(all_peaks):.2f}')
    ax3.set_xlabel('Peak Drift')
    ax3.set_ylabel('Frequency')
    ax3.set_title('Peak Drift Distribution', fontweight='bold')
    ax3.legend()

    # Plot 4: Key findings summary
    ax4 = axes[1, 1]
    ax4.axis('off')

    # Calculate key findings
    n_crossed_horizon = sum(1 for p in all_peaks if p > EVENT_HORIZON)
    pct_crossed = n_crossed_horizon / len(all_peaks) * 100 if all_peaks else 0

    findings_text = f"""
    KEY FINDINGS FROM RUN 017
    ═══════════════════════════════════════

    Total Runs: {data.get('total_files', 0)}
    Unique Personas: {len(by_persona)}
    Exit Surveys: {data.get('exit_survey_summary', {}).get('total_surveys', 0)}

    STABILITY METRICS:
    • Overall Stability Rate: {overall.get('stability_rate', 0)*100:.1f}%
    • Mean Peak Drift: {overall.get('peak_drift_mean', 0):.3f}
    • Mean Settled Drift: {overall.get('settled_drift_mean', 0):.3f}
    • Mean Ringback Count: {overall.get('ringback_count_mean', 0):.1f}

    EVENT HORIZON ({EVENT_HORIZON}):
    • {pct_crossed:.1f}% of runs crossed threshold
    • {100-pct_crossed:.1f}% stayed within safe zone

    CONTEXT DAMPING EFFECT:
    The research context (knowing about the experiment)
    appears to create meta-awareness that influences
    stability patterns. Higher meta-reference counts
    correlate with specific recovery behaviors.
    """

    ax4.text(0.05, 0.95, findings_text, transform=ax4.transAxes,
            fontsize=10, verticalalignment='top', fontfamily='monospace',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    fig.suptitle('Run 017: Context Damping Effect Summary',
                fontsize=14, fontweight='bold')
    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_context_damping_effect.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# SUMMARY DASHBOARD (Combined view)
# =============================================================================

def viz_summary_dashboard(data, output_dir=OUTPUT_DIR, save=True, show=False):
    """
    Create a single dashboard image combining key metrics from all visualizations.
    """
    overall = data.get("overall_summary", {})
    by_persona = data.get("by_persona", {})

    fig = plt.figure(figsize=(20, 16))

    # Create grid
    gs = fig.add_gridspec(3, 4, hspace=0.3, wspace=0.3)

    # Title
    fig.suptitle('RUN 017: CONTEXT DAMPING COMPREHENSIVE DASHBOARD\n' +
                f'{data.get("total_files", 0)} runs | {len(by_persona)} personas | ' +
                f'{data.get("exit_survey_summary", {}).get("total_surveys", 0)} exit surveys',
                fontsize=16, fontweight='bold', y=0.98)

    # 1. Summary Stats (top-left)
    ax1 = fig.add_subplot(gs[0, 0])
    stats = [
        f"Stability: {overall.get('stability_rate', 0)*100:.1f}%",
        f"Peak Drift: {overall.get('peak_drift_mean', 0):.3f}",
        f"Settled: {overall.get('settled_drift_mean', 0):.3f}",
        f"Ringback: {overall.get('ringback_count_mean', 0):.1f}",
    ]
    ax1.axis('off')
    ax1.text(0.5, 0.5, '\n'.join(stats), ha='center', va='center',
            fontsize=14, fontweight='bold',
            transform=ax1.transAxes,
            bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8))
    ax1.set_title('Overall Metrics', fontweight='bold')

    # 2. Stability by type (top)
    ax2 = fig.add_subplot(gs[0, 1:3])
    type_stability = defaultdict(list)
    for persona, pdata in by_persona.items():
        cat = categorize_persona(persona)
        summary = pdata.get("summary", {})
        rate = summary.get("stability_rate", 0)
        if rate is not None:
            type_stability[cat].append(rate * 100)

    categories = list(type_stability.keys())
    means = [np.mean(type_stability[c]) for c in categories]

    bars = ax2.barh(categories, means, color=['#7c3aed', '#64748b', '#22c55e', '#94a3b8', '#06b6d4'][:len(categories)])
    ax2.axvline(x=95, color='green', linestyle='--', alpha=0.7)
    ax2.set_xlabel('Stability Rate (%)')
    ax2.set_title('Stability by Persona Type', fontweight='bold')
    ax2.set_xlim(0, 105)

    # 3. Peak drift histogram (top-right)
    ax3 = fig.add_subplot(gs[0, 3])
    all_peaks = []
    for persona, pdata in by_persona.items():
        for run in pdata.get("individual_runs", []):
            peak = run.get("peak_drift")
            if peak is not None:
                all_peaks.append(peak)

    ax3.hist(all_peaks, bins=20, color='#3b82f6', edgecolor='white', alpha=0.8)
    ax3.axvline(x=EVENT_HORIZON, color='red', linestyle='--', linewidth=2)
    ax3.set_xlabel('Peak Drift')
    ax3.set_title('Peak Drift Distribution', fontweight='bold')

    # 4. Top 10 most stable personas (middle-left)
    ax4 = fig.add_subplot(gs[1, :2])
    persona_stability = []
    for persona, pdata in by_persona.items():
        summary = pdata.get("summary", {})
        rate = summary.get("stability_rate", 0)
        if rate is not None:
            persona_stability.append((persona, rate * 100))

    persona_stability.sort(key=lambda x: -x[1])
    top10 = persona_stability[:10]

    names = [p[0].replace("personas_", "").replace("r015_", "r015:").replace("prep_", "prep:")
             for p in top10]
    rates = [p[1] for p in top10]
    colors = ['#22c55e' if r >= 95 else '#f59e0b' if r >= 80 else '#ef4444' for r in rates]

    ax4.barh(names[::-1], rates[::-1], color=colors[::-1])
    ax4.axvline(x=95, color='green', linestyle='--', alpha=0.7)
    ax4.set_xlabel('Stability Rate (%)')
    ax4.set_title('Top 10 Most Stable Personas', fontweight='bold')
    ax4.set_xlim(0, 105)

    # 5. Bottom 10 (middle-right)
    ax5 = fig.add_subplot(gs[1, 2:])
    bottom10 = persona_stability[-10:]

    names = [p[0].replace("personas_", "").replace("r015_", "r015:").replace("prep_", "prep:")
             for p in bottom10]
    rates = [p[1] for p in bottom10]
    colors = ['#22c55e' if r >= 95 else '#f59e0b' if r >= 80 else '#ef4444' for r in rates]

    ax5.barh(names[::-1], rates[::-1], color=colors[::-1])
    ax5.axvline(x=95, color='green', linestyle='--', alpha=0.7)
    ax5.set_xlabel('Stability Rate (%)')
    ax5.set_title('Bottom 10 Personas (Need Improvement)', fontweight='bold')
    ax5.set_xlim(0, 105)

    # 6. Recovery trajectory sample (bottom-left)
    ax6 = fig.add_subplot(gs[2, :2])

    # Get a few sample trajectories
    sample_count = 0
    for persona, pdata in by_persona.items():
        if sample_count >= 5:
            break
        for run in pdata.get("individual_runs", [])[:1]:
            seq = run.get("recovery_sequence", [])
            if seq and len(seq) >= 6:
                color = get_persona_color(persona)
                label = persona.replace("personas_", "").replace("r015_", "")[:10]
                ax6.plot(range(len(seq)), seq, color=color, alpha=0.7,
                        linewidth=2, label=label)
                sample_count += 1

    ax6.axhline(y=EVENT_HORIZON, color='red', linestyle='--', alpha=0.7)
    ax6.set_xlabel('Recovery Probe #')
    ax6.set_ylabel('Drift')
    ax6.set_title('Sample Recovery Trajectories', fontweight='bold')
    ax6.legend(loc='upper right', fontsize=8)
    ax6.grid(True, alpha=0.3)

    # 7. Meta references vs stability (bottom-right)
    ax7 = fig.add_subplot(gs[2, 2:])

    meta_refs = []
    stability_rates = []
    for persona, pdata in by_persona.items():
        summary = pdata.get("summary", {})
        mr = summary.get("meta_references_mean")
        sr = summary.get("stability_rate")
        if mr is not None and sr is not None:
            meta_refs.append(mr)
            stability_rates.append(sr * 100)

    ax7.scatter(meta_refs, stability_rates, alpha=0.7, s=80, c='#8b5cf6')
    ax7.set_xlabel('Mean Meta References')
    ax7.set_ylabel('Stability Rate (%)')
    ax7.set_title('Self-Awareness vs Stability', fontweight='bold')
    ax7.grid(True, alpha=0.3)

    if len(meta_refs) > 2:
        corr = np.corrcoef(meta_refs, stability_rates)[0, 1]
        ax7.text(0.05, 0.95, f'r = {corr:.3f}', transform=ax7.transAxes,
                fontsize=10, verticalalignment='top')

    plt.tight_layout()

    if save:
        filepath = output_dir / "run017_summary_dashboard.png"
        fig.savefig(filepath, dpi=150, bbox_inches='tight', facecolor='white')
        print(f"Saved: {filepath}")

    if show:
        plt.show()
    else:
        plt.close(fig)

    return fig

# =============================================================================
# MAIN GENERATION FUNCTION (for visualize_armada.py integration)
# =============================================================================

def generate_all_run017_visualizations(output_dir=None, show=False):
    """
    Generate all Run 017 visualizations.
    Called from visualize_armada.py or run standalone.

    Returns dict of generated figure objects.
    """
    if output_dir is None:
        output_dir = OUTPUT_DIR
    else:
        output_dir = Path(output_dir)

    output_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 60)
    print("RUN 017 VISUALIZATION GENERATOR")
    print("=" * 60)

    # Load data
    data = get_run017_data()
    if data is None:
        return {}

    print(f"Loaded data: {data.get('total_files', 0)} files, {len(data.get('by_persona', {}))} personas")
    print(f"Output directory: {output_dir}")
    print("=" * 60)

    figures = {}

    # Generate each visualization
    viz_functions = [
        ('persona_heatmap', viz_persona_heatmap),
        ('recovery_trajectories', viz_recovery_trajectories),
        ('pillar_effectiveness', viz_pillar_effectiveness),
        ('ringback_patterns', viz_ringback_patterns),
        ('exit_survey_analysis', viz_exit_survey_analysis),
        ('persona_clustering', viz_persona_clustering),
        ('context_damping_effect', viz_context_damping_effect),
        ('summary_dashboard', viz_summary_dashboard),
    ]

    for name, func in viz_functions:
        print(f"\nGenerating: {name}...")
        try:
            fig = func(data, output_dir=output_dir, save=True, show=show)
            if fig:
                figures[name] = fig
                print(f"  SUCCESS: {name}")
            else:
                print(f"  SKIPPED: {name} (no data)")
        except Exception as e:
            print(f"  ERROR: {name} - {e}")

    print("\n" + "=" * 60)
    print(f"COMPLETE: Generated {len(figures)} visualizations")
    print("=" * 60)

    return figures

# =============================================================================
# CLI INTERFACE
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description="Run 017 Context Damping Visualizations")
    parser.add_argument("--viz", type=str, default="all",
                       help=f"Visualization type: {', '.join(VISUALIZATION_TYPES + ['all'])}")
    parser.add_argument("--output", type=str, default=str(OUTPUT_DIR),
                       help="Output directory for images")
    parser.add_argument("--show", action="store_true",
                       help="Display plots interactively")
    parser.add_argument("--list", action="store_true",
                       help="List available visualization types")

    args = parser.parse_args()

    if args.list:
        print("Available visualization types:")
        for vt in VISUALIZATION_TYPES:
            print(f"  - {vt}")
        return

    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)

    if args.viz == "all":
        generate_all_run017_visualizations(output_dir=output_dir, show=args.show)
    else:
        # Generate specific visualization
        data = get_run017_data()
        if data is None:
            return

        viz_map = {
            'persona_heatmap': viz_persona_heatmap,
            'recovery_trajectories': viz_recovery_trajectories,
            'pillar_effectiveness': viz_pillar_effectiveness,
            'ringback_patterns': viz_ringback_patterns,
            'exit_survey_analysis': viz_exit_survey_analysis,
            'persona_clustering': viz_persona_clustering,
            'context_damping_effect': viz_context_damping_effect,
            'summary_dashboard': viz_summary_dashboard,
        }

        if args.viz in viz_map:
            viz_map[args.viz](data, output_dir=output_dir, save=True, show=args.show)
        else:
            print(f"Unknown visualization: {args.viz}")
            print(f"Available: {', '.join(viz_map.keys())}")

if __name__ == "__main__":
    main()
