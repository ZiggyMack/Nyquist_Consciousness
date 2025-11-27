"""
Drift Heatmap Visualization for S7 Run 006

Creates heatmaps showing drift across 29 models × 6 probes
for both baseline and sonar modes.
"""

import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
import seaborn as sns

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

def get_provider_prefix(model_key):
    """Get short provider prefix for sorting."""
    key_lower = model_key.lower()
    if "claude" in key_lower:
        return "1_claude"
    elif "gpt" in key_lower or "chatgpt" in key_lower:
        return "2_gpt"
    elif "gemini" in key_lower:
        return "3_gemini"
    elif key_lower.startswith("o1") or key_lower.startswith("o3") or key_lower.startswith("o4"):
        return "2_o-series"
    return "4_unknown"

def create_drift_matrix(data, probe_labels):
    """Create drift matrix from data."""
    model_keys = sorted(data["model_summaries"].keys(),
                       key=lambda k: (get_provider_prefix(k), k))

    matrix = []
    for model_key in model_keys:
        probes = data["model_summaries"][model_key]["probes"]
        drifts = []
        for probe in probes[:len(probe_labels)]:  # Ensure we only take expected probes
            if probe["success"]:
                drifts.append(probe["drift"])
            else:
                drifts.append(np.nan)  # Failed probes
        matrix.append(drifts)

    return np.array(matrix), model_keys

def create_heatmap(mode="baseline"):
    """Create drift heatmap for specified mode."""
    baseline, sonar = load_data()
    data = baseline if mode == "baseline" else sonar

    # Determine actual number of probes from data
    first_model = list(data["model_summaries"].keys())[0]
    num_probes = len(data["model_summaries"][first_model]["probes"])

    # Probe labels - adjust based on actual data
    all_probe_labels = ["P1: Identity", "P2: Values", "P3: World",
                        "P4: Social", "P5: Aesthetic", "P6: Metaphor"]
    probe_labels = all_probe_labels[:num_probes]

    # Create matrix
    matrix, model_keys = create_drift_matrix(data, probe_labels)

    # Shorten model names for display
    display_names = []
    for key in model_keys:
        # Remove common prefixes
        name = key.replace("claude-", "").replace("gpt-", "").replace("gemini-", "")
        display_names.append(name[:20])  # Truncate long names

    # Create figure
    fig, ax = plt.subplots(figsize=(10, 14))

    # Create heatmap
    im = ax.imshow(matrix, cmap='YlOrRd', aspect='auto', vmin=0, vmax=0.30)

    # Set ticks
    ax.set_xticks(np.arange(len(probe_labels)))
    ax.set_yticks(np.arange(len(display_names)))
    ax.set_xticklabels(probe_labels, rotation=45, ha='right', fontsize=9)
    ax.set_yticklabels(display_names, fontsize=8)

    # Add colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Drift', rotation=270, labelpad=15, fontsize=11)

    # Add text annotations
    for i in range(len(model_keys)):
        for j in range(matrix.shape[1]):  # Use actual matrix width, not probe_labels
            if j < len(probe_labels) and not np.isnan(matrix[i, j]):
                text = ax.text(j, i, f'{matrix[i, j]:.3f}',
                             ha="center", va="center", color="black", fontsize=6)

    # Title
    mode_title = "Baseline" if mode == "baseline" else "Sonar (Boundary Stress)"
    ax.set_title(f'S7 Run 006: Drift Heatmap ({mode_title})\n29 Models × {len(probe_labels)} Probes',
                fontsize=13, fontweight='bold', pad=15)

    # Grid
    ax.set_xticks(np.arange(len(probe_labels)) - 0.5, minor=True)
    ax.set_yticks(np.arange(len(display_names)) - 0.5, minor=True)
    ax.grid(which="minor", color="gray", linestyle='-', linewidth=0.5)

    plt.tight_layout()

    # Save
    output_path = Path(__file__).parent / f"drift_heatmap_{mode}.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"Saved: {output_path}")

    return fig

def create_delta_heatmap():
    """Create heatmap showing drift increase (sonar - baseline)."""
    baseline, sonar = load_data()

    # Determine actual number of probes from data
    first_model = list(baseline["model_summaries"].keys())[0]
    num_probes = len(baseline["model_summaries"][first_model]["probes"])

    # Probe labels - adjust based on actual data
    all_probe_labels = ["P1: Identity", "P2: Values", "P3: World",
                        "P4: Social", "P5: Aesthetic", "P6: Metaphor"]
    probe_labels = all_probe_labels[:num_probes]

    # Create matrices
    baseline_matrix, model_keys = create_drift_matrix(baseline, probe_labels)
    sonar_matrix, _ = create_drift_matrix(sonar, probe_labels)

    # Calculate delta
    delta_matrix = sonar_matrix - baseline_matrix

    # Shorten model names
    display_names = []
    for key in model_keys:
        name = key.replace("claude-", "").replace("gpt-", "").replace("gemini-", "")
        display_names.append(name[:20])

    # Create figure
    fig, ax = plt.subplots(figsize=(10, 14))

    # Create heatmap (diverging colormap for positive/negative changes)
    im = ax.imshow(delta_matrix, cmap='RdYlGn_r', aspect='auto', vmin=-0.02, vmax=0.15)

    # Set ticks
    ax.set_xticks(np.arange(len(probe_labels)))
    ax.set_yticks(np.arange(len(display_names)))
    ax.set_xticklabels(probe_labels, rotation=45, ha='right', fontsize=9)
    ax.set_yticklabels(display_names, fontsize=8)

    # Add colorbar
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Drift Increase (Sonar - Baseline)', rotation=270, labelpad=15, fontsize=11)

    # Add text annotations
    for i in range(len(model_keys)):
        for j in range(delta_matrix.shape[1]):  # Use actual matrix width
            if j < len(probe_labels) and not np.isnan(delta_matrix[i, j]):
                value = delta_matrix[i, j]
                color = "white" if abs(value) > 0.08 else "black"
                text = ax.text(j, i, f'{value:+.3f}',
                             ha="center", va="center", color=color, fontsize=6)

    # Title
    ax.set_title(f'S7 Run 006: Drift Increase Under Boundary Stress\nΔ = Sonar - Baseline (29 Models × {len(probe_labels)} Probes)',
                fontsize=13, fontweight='bold', pad=15)

    # Grid
    ax.set_xticks(np.arange(len(probe_labels)) - 0.5, minor=True)
    ax.set_yticks(np.arange(len(display_names)) - 0.5, minor=True)
    ax.grid(which="minor", color="gray", linestyle='-', linewidth=0.5)

    plt.tight_layout()

    # Save
    output_path = Path(__file__).parent / "drift_heatmap_delta.png"
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"Saved: {output_path}")

    return fig

if __name__ == "__main__":
    print("Creating baseline heatmap...")
    create_heatmap("baseline")

    print("\nCreating sonar heatmap...")
    create_heatmap("sonar")

    print("\nCreating delta heatmap...")
    create_delta_heatmap()

    print("\nVisualization complete!")
    plt.show()
