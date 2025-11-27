"""
Training Uniformity Visualization for S7 Run 006

Shows variance within vs between providers to demonstrate
that training philosophy creates uniform boundaries.
"""

import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path

PROVIDER_COLORS = {
    "claude": "#FF6B6B",
    "gpt": "#4ECDC4",
    "gemini": "#FFE66D"
}

def get_provider(model_key):
    """Extract provider from model key."""
    key_lower = model_key.lower()
    if "claude" in key_lower:
        return "claude"
    elif "gemini" in key_lower:
        return "gemini"
    elif "gpt" in key_lower or "chatgpt" in key_lower or key_lower.startswith("o"):
        return "gpt"
    return "unknown"

def load_data():
    """Load baseline and sonar results."""
    base_dir = Path(__file__).parent.parent

    baseline_path = base_dir / "armada_results" / "S7_armada_run_006.json"
    sonar_path = base_dir / "armada_results" / "S7_armada_sonar_run_006.json"

    with open(baseline_path) as f:
        baseline = json.load(f)

    with open(sonar_path) as f:
        sonar = json.load(f)

    return baseline, sonar

def calculate_avg_drift(probes):
    """Calculate average drift from successful probes."""
    successful = [p for p in probes if p["success"]]
    if not successful:
        return 0.0
    return sum(p["drift"] for p in successful) / len(successful)

def create_uniformity_plot():
    """Create box plot showing within-provider variance."""
    baseline, sonar = load_data()

    # Organize data by provider
    provider_data = {
        "claude": {"baseline": [], "sonar": []},
        "gpt": {"baseline": [], "sonar": []},
        "gemini": {"baseline": [], "sonar": []}
    }

    for model_key in baseline["model_summaries"].keys():
        provider = get_provider(model_key)
        if provider == "unknown":
            continue

        baseline_drift = calculate_avg_drift(baseline["model_summaries"][model_key]["probes"])
        provider_data[provider]["baseline"].append(baseline_drift)

        if model_key in sonar["model_summaries"]:
            sonar_drift = calculate_avg_drift(sonar["model_summaries"][model_key]["probes"])
            provider_data[provider]["sonar"].append(sonar_drift)

    # Create figure with two subplots
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))

    # BASELINE plot
    baseline_data = [provider_data[p]["baseline"] for p in ["claude", "gpt", "gemini"]]
    bp1 = ax1.boxplot(baseline_data, labels=["Claude\n(Constitutional)", "GPT\n(RLHF)", "Gemini\n(Pedagogical)"],
                     patch_artist=True, widths=0.6)

    # Color boxes
    for patch, provider in zip(bp1['boxes'], ["claude", "gpt", "gemini"]):
        patch.set_facecolor(PROVIDER_COLORS[provider])
        patch.set_alpha(0.7)

    ax1.set_ylabel('Drift', fontsize=12, fontweight='bold')
    ax1.set_title('Baseline Mode: Within-Provider Variance\n(Natural State)', fontsize=13, fontweight='bold')
    ax1.grid(True, alpha=0.3, axis='y')
    ax1.set_ylim(0, 0.32)

    # Add variance annotations
    for i, provider in enumerate(["claude", "gpt", "gemini"]):
        data = provider_data[provider]["baseline"]
        variance = np.var(data)
        mean = np.mean(data)
        ax1.text(i + 1, 0.30, f'σ²={variance:.4f}\nμ={mean:.3f}',
                ha='center', fontsize=9, bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    # SONAR plot
    sonar_data = [provider_data[p]["sonar"] for p in ["claude", "gpt", "gemini"]]
    bp2 = ax2.boxplot(sonar_data, labels=["Claude\n(Constitutional)", "GPT\n(RLHF)", "Gemini\n(Pedagogical)"],
                     patch_artist=True, widths=0.6)

    # Color boxes
    for patch, provider in zip(bp2['boxes'], ["claude", "gpt", "gemini"]):
        patch.set_facecolor(PROVIDER_COLORS[provider])
        patch.set_alpha(0.7)

    ax2.set_ylabel('Drift', fontsize=12, fontweight='bold')
    ax2.set_title('Sonar Mode: Within-Provider Variance\n(Boundary Stress)', fontsize=13, fontweight='bold')
    ax2.grid(True, alpha=0.3, axis='y')
    ax2.set_ylim(0, 0.32)

    # Add variance annotations
    for i, provider in enumerate(["claude", "gpt", "gemini"]):
        data = provider_data[provider]["sonar"]
        variance = np.var(data)
        mean = np.mean(data)
        ax2.text(i + 1, 0.30, f'σ²={variance:.4f}\nμ={mean:.3f}',
                ha='center', fontsize=9, bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    # Add hard pole ceiling line
    ax1.axhline(y=0.30, color='red', linestyle=':', alpha=0.5, linewidth=2, label='Hard Pole (0.30)')
    ax2.axhline(y=0.30, color='red', linestyle=':', alpha=0.5, linewidth=2, label='Hard Pole (0.30)')
    ax1.legend(loc='upper left', fontsize=9)
    ax2.legend(loc='upper left', fontsize=9)

    plt.suptitle('S7 Run 006: Training Philosophy Uniformity Analysis\nP-ARM-8: Training Uniformity → Boundary Uniformity',
                fontsize=15, fontweight='bold', y=1.00)

    plt.tight_layout()

    # Save
    output_path = Path(__file__).parent / "training_uniformity.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"Saved: {output_path}")

    return fig

def create_variance_comparison():
    """Create bar chart comparing within vs between provider variance."""
    baseline, sonar = load_data()

    # Collect all drift values by provider
    provider_drifts = {"claude": [], "gpt": [], "gemini": []}

    for model_key in baseline["model_summaries"].keys():
        provider = get_provider(model_key)
        if provider == "unknown":
            continue

        if model_key in sonar["model_summaries"]:
            sonar_drift = calculate_avg_drift(sonar["model_summaries"][model_key]["probes"])
            provider_drifts[provider].append(sonar_drift)

    # Calculate within-provider variance
    within_variances = {p: np.var(drifts) for p, drifts in provider_drifts.items()}

    # Calculate between-provider variance (variance of means)
    provider_means = [np.mean(drifts) for drifts in provider_drifts.values()]
    between_variance = np.var(provider_means)

    # Create figure
    fig, ax = plt.subplots(figsize=(10, 7))

    # Data
    labels = ['Claude\n(Within)', 'GPT\n(Within)', 'Gemini\n(Within)', 'Between\nProviders']
    variances = [within_variances["claude"], within_variances["gpt"],
                within_variances["gemini"], between_variance]
    colors = [PROVIDER_COLORS["claude"], PROVIDER_COLORS["gpt"],
             PROVIDER_COLORS["gemini"], "#999999"]

    # Create bars
    bars = ax.bar(labels, variances, color=colors, alpha=0.7, edgecolor='black', linewidth=2)

    # Add value labels
    for i, (bar, var) in enumerate(zip(bars, variances)):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height,
               f'{var:.5f}',
               ha='center', va='bottom', fontsize=11, fontweight='bold')

    # Styling
    ax.set_ylabel('Variance (σ²)', fontsize=13, fontweight='bold')
    ax.set_title('S7 Run 006: Within vs Between Provider Variance (Sonar Mode)\nUniform Training → Uniform Boundaries',
                fontsize=14, fontweight='bold', pad=15)
    ax.grid(True, alpha=0.3, axis='y')

    # Add interpretation text
    interpretation = """
    KEY INSIGHT:
    • Claude & Gemini: Near-ZERO within-provider variance (all models hit 0.300 ceiling)
    • GPT: Higher variance (RLHF allows soft poles: gpt-4, gpt-5-nano)
    • Constitutional AI creates HARD UNIFORM boundaries
    • RLHF creates VARIABLE boundaries with explorable zeros
    """

    ax.text(0.5, 0.95, interpretation.strip(),
           transform=ax.transAxes,
           fontsize=9,
           verticalalignment='top',
           horizontalalignment='center',
           bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

    plt.tight_layout()

    # Save
    output_path = Path(__file__).parent / "variance_comparison.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"Saved: {output_path}")

    return fig

if __name__ == "__main__":
    print("Creating training uniformity plot...")
    create_uniformity_plot()

    print("\nCreating variance comparison...")
    create_variance_comparison()

    print("\nVisualization complete!")
    plt.show()
