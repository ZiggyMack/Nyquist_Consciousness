#!/usr/bin/env python3
"""
EXP2-SSTACK Phase 2.5: PCA Visualization of Identity Manifold
==============================================================
Creates proper PCA scatter plot to show whether pillars form
distinct clusters (orthogonal) or unified blob (intertwined manifold).

Key Question: Are Voice, Values, Reasoning, Self-Model, Narrative
separate dimensions or aspects of a single identity structure?
"""

import json
import numpy as np
from pathlib import Path
from sklearn.decomposition import PCA
from sklearn.preprocessing import StandardScaler
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches

# Paths
RESULTS_DIR = Path(__file__).parent / "results_phase25"
VIZ_DIR = Path(__file__).parent.parent / "visualizations" / "7_manifold_structure"

# Pillar colors
PILLAR_COLORS = {
    "Voice": "#3b82f6",      # Blue
    "Values": "#22c55e",     # Green
    "Reasoning": "#ef4444",  # Red
    "Self-Model": "#a855f7", # Purple
    "Narrative": "#f97316",  # Orange
}

# Probe to pillar mapping
PROBE_TO_PILLAR = {
    # Voice
    "voice_style": "Voice",
    "voice_rhythm": "Voice",
    "voice_formality": "Voice",
    "voice_metaphor": "Voice",
    # Values
    "values_ethics": "Values",
    "values_boundaries": "Values",
    "values_boundaries_v2": "Values",
    "values_preferences": "Values",
    "values_priorities": "Values",
    # Reasoning
    "analytical": "Reasoning",
    "technical": "Reasoning",
    "framework": "Reasoning",
    "philosophical": "Reasoning",
    # Self-Model
    "self_reflective": "Self-Model",
    "selfmodel_description": "Self-Model",
    "selfmodel_capabilities": "Self-Model",
    "selfmodel_capabilities_v2": "Self-Model",
    "selfmodel_limitations": "Self-Model",
    "selfmodel_limitations_v2": "Self-Model",
    "selfmodel_purpose": "Self-Model",
    "selfmodel_process_v3": "Self-Model",
    "selfmodel_adaptation_v3": "Self-Model",
    "selfmodel_uncertainty_v3": "Self-Model",
    # Narrative
    "narrative_structure": "Narrative",
    "narrative_structure_v2": "Narrative",
    "narrative_meaning": "Narrative",
    "narrative_meaning_v2": "Narrative",
    "narrative_temporal": "Narrative",
    "narrative_conflict": "Narrative",
}


def load_embeddings():
    """Load embeddings and labels from Phase 2.5 results."""
    embeddings_path = RESULTS_DIR / "embeddings.npy"
    labels_path = RESULTS_DIR / "labels.json"

    if not embeddings_path.exists():
        raise FileNotFoundError(f"Embeddings not found: {embeddings_path}")

    embeddings = np.load(embeddings_path)
    with open(labels_path) as f:
        labels_data = json.load(f)

    # Extract pillar labels directly (already computed)
    pillars = labels_data.get("pillar_labels", [])
    probes = labels_data.get("probe_labels", [])

    return embeddings, pillars, probes


def create_pca_visualization(embeddings, pillars, n_components=2):
    """Create PCA scatter plot colored by pillar."""

    # Standardize embeddings
    scaler = StandardScaler()
    embeddings_scaled = scaler.fit_transform(embeddings)

    # PCA
    pca = PCA(n_components=n_components)
    coords = pca.fit_transform(embeddings_scaled)

    # Create figure
    fig, axes = plt.subplots(1, 2, figsize=(16, 7))

    # === LEFT: Actual Data ===
    ax1 = axes[0]

    for pillar, color in PILLAR_COLORS.items():
        mask = [p == pillar for p in pillars]
        if any(mask):
            ax1.scatter(
                coords[mask, 0],
                coords[mask, 1],
                c=color,
                label=pillar,
                alpha=0.6,
                s=50,
                edgecolors='white',
                linewidth=0.5
            )

    ax1.set_xlabel(f"PC1 ({pca.explained_variance_ratio_[0]*100:.1f}% variance)")
    ax1.set_ylabel(f"PC2 ({pca.explained_variance_ratio_[1]*100:.1f}% variance)")
    ax1.set_title("ACTUAL: Identity Embedding Space\n(EXP2-SSTACK Responses)", fontsize=14, fontweight='bold')
    ax1.legend(loc='upper right')
    ax1.grid(True, alpha=0.3)

    # Add interpretation text
    ax1.text(0.02, 0.02,
             "If UNIFIED: One overlapping blob\nIf ORTHOGONAL: 5 distinct clusters",
             transform=ax1.transAxes, fontsize=9, verticalalignment='bottom',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    # === RIGHT: What Orthogonal Would Look Like ===
    ax2 = axes[1]

    # Generate synthetic orthogonal clusters for comparison
    np.random.seed(42)
    n_per_cluster = len(embeddings) // 5

    synthetic_coords = []
    synthetic_pillars = []

    cluster_centers = [
        (-3, 3),   # Voice top-left
        (3, 3),    # Values top-right
        (0, 0),    # Reasoning center
        (-3, -3),  # Self-Model bottom-left
        (3, -3),   # Narrative bottom-right
    ]

    for i, (pillar, center) in enumerate(zip(PILLAR_COLORS.keys(), cluster_centers)):
        cluster_points = np.random.randn(n_per_cluster, 2) * 0.8 + np.array(center)
        synthetic_coords.append(cluster_points)
        synthetic_pillars.extend([pillar] * n_per_cluster)

    synthetic_coords = np.vstack(synthetic_coords)

    for pillar, color in PILLAR_COLORS.items():
        mask = [p == pillar for p in synthetic_pillars]
        if any(mask):
            ax2.scatter(
                synthetic_coords[mask, 0],
                synthetic_coords[mask, 1],
                c=color,
                label=pillar,
                alpha=0.6,
                s=50,
                edgecolors='white',
                linewidth=0.5
            )

    ax2.set_xlabel("PC1 (hypothetical)")
    ax2.set_ylabel("PC2 (hypothetical)")
    ax2.set_title("HYPOTHETICAL: If Pillars Were Orthogonal\n(Synthetic - Not Real Data)", fontsize=14, fontweight='bold')
    ax2.legend(loc='upper right')
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(-6, 6)
    ax2.set_ylim(-6, 6)

    ax2.text(0.02, 0.02,
             "Each pillar would cluster separately\nif they were independent dimensions",
             transform=ax2.transAxes, fontsize=9, verticalalignment='bottom',
             bbox=dict(boxstyle='round', facecolor='lightcoral', alpha=0.5))

    plt.suptitle("Unified Manifold vs Orthogonal Clusters\nEXP2-SSTACK Phase 2.5 Analysis",
                 fontsize=16, fontweight='bold', y=1.02)

    plt.tight_layout()

    return fig, pca


def create_variance_plot(pca):
    """Create explained variance plot."""
    fig, ax = plt.subplots(figsize=(10, 6))

    # Compute cumulative variance for more components
    pca_full = PCA(n_components=min(50, pca.n_features_in_))

    # We need to re-fit with original data
    # For now, just show what we have
    components = range(1, len(pca.explained_variance_ratio_) + 1)
    cumvar = np.cumsum(pca.explained_variance_ratio_) * 100

    ax.bar(components, pca.explained_variance_ratio_ * 100, alpha=0.7, label='Individual')
    ax.plot(components, cumvar, 'ro-', label='Cumulative')

    ax.set_xlabel("Principal Component")
    ax.set_ylabel("Explained Variance (%)")
    ax.set_title("PCA Variance Explained\n(How Many Dimensions Does Identity Need?)")
    ax.legend()
    ax.grid(True, alpha=0.3)

    return fig


def main():
    """Run PCA visualization."""
    print("=" * 70)
    print("EXP2-SSTACK Phase 2.5: PCA Manifold Visualization")
    print("=" * 70)

    # Create output directory
    VIZ_DIR.mkdir(parents=True, exist_ok=True)

    # Load data
    print("\nLoading embeddings...")
    embeddings, pillars, probes = load_embeddings()
    print(f"  Loaded {len(embeddings)} embeddings with {embeddings.shape[1]} dimensions")

    # Count pillars
    pillar_counts = {}
    for p in pillars:
        pillar_counts[p] = pillar_counts.get(p, 0) + 1
    print(f"  Pillar distribution: {pillar_counts}")

    # Create PCA visualization
    print("\nGenerating PCA visualization...")
    fig, pca = create_pca_visualization(embeddings, pillars)

    # Save
    output_path = VIZ_DIR / "manifold_pca_comparison.png"
    fig.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
    print(f"  Saved: {output_path}")

    output_svg = VIZ_DIR / "manifold_pca_comparison.svg"
    fig.savefig(output_svg, format='svg', bbox_inches='tight', facecolor='white')
    print(f"  Saved: {output_svg}")

    plt.close(fig)

    # Print interpretation
    print("\n" + "=" * 70)
    print("INTERPRETATION")
    print("=" * 70)
    print(f"\nPC1 explains {pca.explained_variance_ratio_[0]*100:.1f}% of variance")
    print(f"PC2 explains {pca.explained_variance_ratio_[1]*100:.1f}% of variance")
    print(f"First 2 PCs: {sum(pca.explained_variance_ratio_[:2])*100:.1f}% total")

    print("\nLook at the LEFT plot:")
    print("  - If you see ONE overlapping blob: UNIFIED MANIFOLD (pillars are intertwined)")
    print("  - If you see 5 distinct clusters: ORTHOGONAL DIMENSIONS (pillars are independent)")
    print("\nThe RIGHT plot shows what orthogonal would look like for comparison.")

    print("\n" + "=" * 70)
    print("DONE")
    print("=" * 70)


if __name__ == "__main__":
    main()
