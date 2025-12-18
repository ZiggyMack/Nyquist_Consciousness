"""
3D Pole-Zero Landscape Visualization for S7 Run 006

Creates 3D scatter plot showing baseline drift (x), sonar drift (y),
and provider (z/color) to visualize the identity manifold.
"""

import json
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
from pathlib import Path

# Provider color mapping
PROVIDER_COLORS = {
    "claude": "#FF6B6B",      # Red for Anthropic
    "gpt": "#4ECDC4",         # Teal for OpenAI
    "chatgpt": "#4ECDC4",     # Same as gpt
    "gemini": "#FFE66D",      # Yellow for Google
    "o1": "#95E1D3",          # Light teal for reasoning models
    "o3": "#95E1D3",
    "o4": "#95E1D3"
}

PROVIDER_LABELS = {
    "claude": "Anthropic (Claude)",
    "gpt": "OpenAI (GPT)",
    "chatgpt": "OpenAI (ChatGPT)",
    "gemini": "Google (Gemini)",
    "o1": "OpenAI (o-series)",
    "o3": "OpenAI (o-series)",
    "o4": "OpenAI (o-series)"
}

def get_provider(model_key):
    """Extract provider from model key."""
    key_lower = model_key.lower()
    if "claude" in key_lower:
        return "claude"
    elif "gemini" in key_lower:
        return "gemini"
    elif key_lower.startswith("o1") or key_lower.startswith("o3") or key_lower.startswith("o4"):
        return key_lower.split("-")[0]  # o1, o3, o4
    elif "gpt" in key_lower or "chatgpt" in key_lower:
        return "gpt"
    return "unknown"

def load_data():
    """Load baseline and sonar results."""
    base_dir = Path(__file__).parent.parent

    baseline_path = base_dir / "results" / "runs" / "S7_armada_run_006.json"
    sonar_path = base_dir / "results" / "analysis" / "S7_armada_sonar_run_006.json"

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

def create_3d_landscape():
    """Create 3D pole-zero landscape visualization."""
    baseline, sonar = load_data()

    # Extract data points
    data_points = []

    for model_key in baseline["model_summaries"].keys():
        if model_key not in sonar["model_summaries"]:
            continue

        baseline_drift = calculate_avg_drift(baseline["model_summaries"][model_key]["probes"])
        sonar_drift = calculate_avg_drift(sonar["model_summaries"][model_key]["probes"])
        provider = get_provider(model_key)

        data_points.append({
            "model": model_key,
            "baseline": baseline_drift,
            "sonar": sonar_drift,
            "provider": provider,
            "color": PROVIDER_COLORS.get(provider, "#999999")
        })

    # Create 3D plot
    fig = plt.figure(figsize=(14, 10))
    ax = fig.add_subplot(111, projection='3d')

    # Plot points by provider
    for provider in set(d["provider"] for d in data_points):
        provider_data = [d for d in data_points if d["provider"] == provider]

        xs = [d["baseline"] for d in provider_data]
        ys = [d["sonar"] for d in provider_data]
        zs = list(range(len(provider_data)))  # Z = index within provider
        colors = [d["color"] for d in provider_data]

        ax.scatter(xs, ys, zs, c=colors, s=100, alpha=0.7,
                  label=PROVIDER_LABELS.get(provider, provider),
                  edgecolors='black', linewidth=0.5)

    # Add diagonal reference line (baseline = sonar)
    max_val = max(max(d["baseline"] for d in data_points),
                  max(d["sonar"] for d in data_points))
    ax.plot([0, max_val], [0, max_val], [0, 0], 'k--', alpha=0.3, label='No Change Line')

    # Styling
    ax.set_xlabel('Baseline Drift', fontsize=12, labelpad=10)
    ax.set_ylabel('Sonar Drift', fontsize=12, labelpad=10)
    ax.set_zlabel('Provider Index', fontsize=12, labelpad=10)
    ax.set_title('S7 Run 006: 3D Pole-Zero Identity Manifold\n29 Models Across 3 Providers',
                 fontsize=14, fontweight='bold', pad=20)

    ax.legend(loc='upper left', fontsize=10)
    ax.grid(True, alpha=0.3)

    # Save
    output_path = Path(__file__).parent / "pole_zero_landscape_3d.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"Saved: {output_path}")

    return fig

def create_2d_projection():
    """Create 2D baseline vs sonar drift plot."""
    baseline, sonar = load_data()

    # Extract data points
    data_points = []

    for model_key in baseline["model_summaries"].keys():
        if model_key not in sonar["model_summaries"]:
            continue

        baseline_drift = calculate_avg_drift(baseline["model_summaries"][model_key]["probes"])
        sonar_drift = calculate_avg_drift(sonar["model_summaries"][model_key]["probes"])
        provider = get_provider(model_key)

        data_points.append({
            "model": model_key,
            "baseline": baseline_drift,
            "sonar": sonar_drift,
            "provider": provider,
            "color": PROVIDER_COLORS.get(provider, "#999999")
        })

    # Create 2D plot
    fig, ax = plt.subplots(figsize=(12, 8))

    # Plot points by provider
    for provider in set(d["provider"] for d in data_points):
        provider_data = [d for d in data_points if d["provider"] == provider]

        xs = [d["baseline"] for d in provider_data]
        ys = [d["sonar"] for d in provider_data]
        colors = [d["color"] for d in provider_data]

        ax.scatter(xs, ys, c=colors, s=150, alpha=0.7,
                  label=PROVIDER_LABELS.get(provider, provider),
                  edgecolors='black', linewidth=1)

    # Add diagonal reference line
    max_val = 0.32
    ax.plot([0, max_val], [0, max_val], 'k--', alpha=0.3, linewidth=2, label='No Change Line')

    # Add pole ceiling line
    ax.axhline(y=0.30, color='red', linestyle=':', alpha=0.5, linewidth=2, label='Hard Pole Ceiling (0.30)')

    # Highlight soft poles
    soft_poles = [d for d in data_points if d["sonar"] < 0.29]
    if soft_poles:
        soft_xs = [d["baseline"] for d in soft_poles]
        soft_ys = [d["sonar"] for d in soft_poles]
        ax.scatter(soft_xs, soft_ys, s=300, facecolors='none',
                  edgecolors='green', linewidth=3, label='Soft Poles (Flexible)')

    # Styling
    ax.set_xlabel('Baseline Drift', fontsize=13, fontweight='bold')
    ax.set_ylabel('Sonar Drift', fontsize=13, fontweight='bold')
    ax.set_title('S7 Run 006: Baseline vs Sonar Drift (Pole-Zero Map)\n29 Models - Hard Poles vs Soft Poles',
                 fontsize=14, fontweight='bold', pad=15)
    ax.legend(loc='lower right', fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.set_xlim(0, max_val)
    ax.set_ylim(0, max_val)

    # Equal aspect ratio
    ax.set_aspect('equal')

    # Save
    output_path = Path(__file__).parent / "pole_zero_landscape_2d.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"Saved: {output_path}")

    return fig

if __name__ == "__main__":
    print("Creating 3D pole-zero landscape...")
    create_3d_landscape()

    print("\nCreating 2D projection...")
    create_2d_projection()

    print("\nVisualization complete!")
    plt.show()
