#!/usr/bin/env python3
"""
Generate Visual Pipeline Matrix PNG
Shows which visuals go into which publication pipeline
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

# Data: Visuals x Pipelines
visuals = [
    "oobleck_thermometer.png (E)",
    "oobleck_control_treatment.png (E)",
    "cross_model_comparison.png (A)",
    "perturbation_comparison.png (A)",
    "phase_portrait.png (B)",
    "settling_curves.png (C)",
    "context_damping_summary.png (D)",
    "provider_comparison.png",
    "variance_curve.png (A)",
    "pc_scatter.png (A)",
    "provider_clusters.png (A)",
    "provider_matrix.png (A)",
    "3d_basin.png (B)",
    "stability_basin.png (B)",
    "vortex.png",
    "vortex_x4.png",
    "oobleck_phase_breakdown.png (E)",
    "oobleck_per_model.png (E)",
    "oobleck_cross_platform.png (E)",
    "oobleck_trajectory.png (E)",
]

pipelines = ["Workshop", "arXiv", "Journal", "PopSci", "Education", "Policy", "Funding", "Media"]

# Matrix: 0=not used, 1=primary, 2=appendix
# Rows are visuals, columns are pipelines
matrix = np.array([
    # Workshop, arXiv, Journal, PopSci, Education, Policy, Funding, Media
    [1, 1, 1, 1, 1, 1, 1, 1],  # oobleck_thermometer - ALL
    [1, 1, 1, 0, 0, 1, 1, 0],  # oobleck_control_treatment
    [1, 1, 1, 0, 0, 0, 1, 0],  # cross_model_comparison
    [0, 1, 1, 0, 0, 0, 1, 0],  # perturbation_comparison
    [1, 1, 1, 0, 0, 0, 1, 0],  # phase_portrait
    [1, 1, 1, 0, 0, 0, 1, 0],  # settling_curves
    [0, 1, 1, 0, 0, 1, 1, 0],  # context_damping_summary
    [0, 1, 1, 0, 0, 0, 1, 0],  # provider_comparison
    [0, 2, 1, 0, 1, 0, 1, 0],  # variance_curve
    [0, 2, 1, 0, 0, 0, 0, 0],  # pc_scatter
    [0, 2, 1, 0, 0, 0, 0, 0],  # provider_clusters
    [0, 2, 1, 0, 0, 0, 0, 0],  # provider_matrix
    [0, 2, 1, 0, 0, 0, 0, 0],  # 3d_basin
    [0, 2, 1, 0, 0, 0, 0, 0],  # stability_basin
    [0, 2, 1, 1, 0, 0, 0, 1],  # vortex
    [0, 2, 1, 0, 0, 0, 0, 0],  # vortex_x4
    [0, 2, 1, 0, 0, 0, 0, 0],  # oobleck_phase_breakdown
    [0, 2, 1, 0, 0, 0, 0, 0],  # oobleck_per_model
    [0, 2, 1, 0, 0, 0, 0, 0],  # oobleck_cross_platform
    [0, 2, 1, 0, 0, 0, 0, 0],  # oobleck_trajectory
])

# Create figure
fig, ax = plt.subplots(figsize=(14, 12))

# Color mapping
colors = {0: '#f0f0f0', 1: '#2ecc71', 2: '#3498db'}  # gray, green, blue
color_labels = {0: 'Not Used', 1: 'Primary', 2: 'Appendix'}

# Draw the matrix
for i in range(len(visuals)):
    for j in range(len(pipelines)):
        color = colors[matrix[i, j]]
        rect = mpatches.FancyBboxPatch(
            (j, len(visuals) - 1 - i), 0.9, 0.9,
            boxstyle="round,pad=0.02",
            facecolor=color,
            edgecolor='white',
            linewidth=1
        )
        ax.add_patch(rect)

        # Add checkmark for primary, 'A' for appendix
        if matrix[i, j] == 1:
            ax.text(j + 0.45, len(visuals) - 0.55 - i, '✓',
                   ha='center', va='center', fontsize=14, fontweight='bold', color='white')
        elif matrix[i, j] == 2:
            ax.text(j + 0.45, len(visuals) - 0.55 - i, 'A',
                   ha='center', va='center', fontsize=11, fontweight='bold', color='white')

# Set axis labels
ax.set_xlim(-0.5, len(pipelines))
ax.set_ylim(-0.5, len(visuals))

# Pipeline labels (top)
ax.set_xticks([i + 0.45 for i in range(len(pipelines))])
ax.set_xticklabels(pipelines, fontsize=11, fontweight='bold', rotation=45, ha='left')
ax.xaxis.tick_top()

# Visual labels (left)
ax.set_yticks([i + 0.45 for i in range(len(visuals))])
ax.set_yticklabels(visuals[::-1], fontsize=9, ha='right')

# Remove spines
for spine in ax.spines.values():
    spine.set_visible(False)

# Title
ax.set_title('Visual-to-Pipeline Matrix\nRun 023 IRON CLAD COSINE (750 experiments, 25 models, 5 providers)',
             fontsize=14, fontweight='bold', pad=40)

# Legend
legend_patches = [
    mpatches.Patch(color='#2ecc71', label='Primary Figure (✓)'),
    mpatches.Patch(color='#3498db', label='Appendix (A)'),
    mpatches.Patch(color='#f0f0f0', label='Not Included'),
]
ax.legend(handles=legend_patches, loc='lower right', fontsize=10,
          frameon=True, fancybox=True, shadow=True)

# Add summary stats at bottom
summary_text = """
Pipeline Totals: Workshop=5 | arXiv=20 | Journal=20 | PopSci=2 | Education=2 | Policy=3 | Funding=8 | Media=2
Key Metrics: D=0.80 (Event Horizon) | d=0.698 (Cohen's d) | 92% (Inherent Drift) | p=2.40e-23
"""
fig.text(0.5, 0.02, summary_text, ha='center', fontsize=9, style='italic',
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

plt.tight_layout()
plt.subplots_adjust(bottom=0.1, top=0.88)

# Save
output_path = 'd:/Documents/Nyquist_Consciousness/WHITE-PAPER/figures/audit/visual_pipeline_matrix.png'
plt.savefig(output_path, dpi=150, bbox_inches='tight', facecolor='white')
print(f"Saved: {output_path}")

# Also save SVG
svg_path = output_path.replace('.png', '.svg')
plt.savefig(svg_path, format='svg', bbox_inches='tight', facecolor='white')
print(f"Saved: {svg_path}")

plt.show()
