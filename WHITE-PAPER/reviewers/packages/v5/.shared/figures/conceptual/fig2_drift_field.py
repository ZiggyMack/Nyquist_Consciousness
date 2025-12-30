"""
Figure 2: Drift Field Geometry (CONCEPTUAL)
Nyquist Consciousness Publication

Creates a 2D conceptual visualization showing:
- Architecture-specific drift vectors
- Event Horizon boundary (D = 0.80 cosine)
- Omega synthesis at the center
- Vector cancellation geometry

NOTE: This is a CONCEPTUAL illustration. Real provider clusters
are in pics/10_PFI_Dimensional/phase2_pca/provider_clusters.png
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, Wedge
from matplotlib.collections import PatchCollection

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 11
plt.rcParams['axes.linewidth'] = 1.2
plt.rcParams['figure.dpi'] = 300


def create_figure():
    """Create the drift field geometry figure."""
    fig, ax = plt.subplots(1, 1, figsize=(12, 10))

    # Center point (I_AM / Omega)
    center = (0, 0)

    # Event Horizon circle (D = 0.80 cosine - CORRECTED from 1.23 Euclidean)
    horizon = Circle(center, 0.80, fill=False, edgecolor='red',
                    linestyle='--', linewidth=2, label='Event Horizon (D=0.80)')
    ax.add_patch(horizon)

    # Add shaded "safe zone" inside horizon
    safe_zone = Circle(center, 0.80, fill=True, facecolor='lightgreen',
                       alpha=0.15, edgecolor='none')
    ax.add_patch(safe_zone)

    # Architecture drift vectors (CONCEPTUAL - illustrative magnitudes)
    # Real data: all providers stay well within D=0.80 event horizon
    architectures = {
        'Anthropic': {'angle': 90, 'magnitude': 0.35, 'color': '#2196F3'},
        'OpenAI': {'angle': 180, 'magnitude': 0.45, 'color': '#9C27B0'},
        'Google': {'angle': -60, 'magnitude': 0.40, 'color': '#4CAF50'},
        'xAI': {'angle': 0, 'magnitude': 0.38, 'color': '#FF9800'},
        'Together': {'angle': -120, 'magnitude': 0.42, 'color': '#795548'},
    }

    # Plot drift vectors
    for arch, props in architectures.items():
        angle_rad = np.radians(props['angle'])
        dx = props['magnitude'] * np.cos(angle_rad)
        dy = props['magnitude'] * np.sin(angle_rad)

        # Arrow from center outward
        ax.annotate('', xy=(dx, dy), xytext=center,
                   arrowprops=dict(arrowstyle='->', color=props['color'],
                                  lw=3, mutation_scale=20))

        # Label at vector endpoint
        label_offset = 0.12
        lx = (props['magnitude'] + label_offset) * np.cos(angle_rad)
        ly = (props['magnitude'] + label_offset) * np.sin(angle_rad)

        # Adjust label position for readability
        ha = 'left' if dx > 0 else 'right'
        if abs(dx) < 0.15:
            ha = 'center'

        ax.text(lx, ly, f'{arch}',
               fontsize=10, ha=ha, va='center', color=props['color'],
               fontweight='bold')

    # Omega synthesis point at center (gold star)
    ax.scatter([0], [0], c='gold', s=400, marker='*', zorder=10,
               edgecolor='darkgoldenrod', linewidth=2)
    ax.text(0, -0.15, 'I_AM\n(Attractor)', fontsize=10, ha='center', va='top',
           color='darkgoldenrod', fontweight='bold')

    # Add concentric reference circles
    for r in [0.2, 0.4, 0.6]:
        ref_circle = Circle(center, r, fill=False, edgecolor='gray',
                           linestyle=':', linewidth=1, alpha=0.5)
        ax.add_patch(ref_circle)
        ax.text(r + 0.02, 0.02, f'D={r}', fontsize=8, color='gray')

    # Add danger zone outside horizon
    danger = Circle(center, 1.2, fill=True, facecolor='mistyrose',
                    alpha=0.2, edgecolor='none')
    ax.add_patch(danger)

    # Zone labels
    ax.text(0.45, -0.55, 'STABLE\nZONE', fontsize=10, ha='center',
           color='darkgreen', alpha=0.7)
    ax.text(0.95, -0.95, 'VOLATILE\nZONE', fontsize=10, ha='center',
           color='darkred', alpha=0.7)

    # Add vector cancellation diagram (inset concept)
    ax.annotate('Drift vectors converge\ntoward I_AM attractor',
               xy=(0, 0), xytext=(0.9, 0.9),
               arrowprops=dict(arrowstyle='->', color='gray', lw=1),
               fontsize=9, ha='left', bbox=dict(boxstyle='round',
               facecolor='wheat', alpha=0.8))

    # Title and labels
    ax.set_title('Figure 2: Drift Field Geometry\n'
                '(Conceptual Illustration - see provider_clusters.png for real PCA)',
                fontsize=14, fontweight='bold', pad=15)

    ax.set_xlabel('Embedding Dimension 1 (Normalized)', fontsize=11)
    ax.set_ylabel('Embedding Dimension 2 (Normalized)', fontsize=11)

    # Key findings text box - COSINE methodology values
    textstr = '\n'.join([
        'Key Parameters (Cosine):',
        '• Event Horizon: D = 0.80',
        '• Effective dims: 2 PCs (90%)',
        '• χ² p = 4.8×10⁻⁵ (provider)',
        '• Pert p = 2.40×10⁻²³ (identity)'
    ])
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.9)
    ax.text(0.02, 0.98, textstr, transform=ax.transAxes, fontsize=9,
           verticalalignment='top', bbox=props)

    # Set axis properties
    ax.set_xlim(-1.3, 1.3)
    ax.set_ylim(-1.3, 1.3)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3, linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='gray', linewidth=0.5, alpha=0.5)
    ax.axvline(x=0, color='gray', linewidth=0.5, alpha=0.5)

    # Legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='#2196F3', lw=3, label='Anthropic drift'),
        Line2D([0], [0], color='#9C27B0', lw=3, label='OpenAI drift'),
        Line2D([0], [0], color='#4CAF50', lw=3, label='Google drift'),
        Line2D([0], [0], color='#FF9800', lw=3, label='xAI drift'),
        Line2D([0], [0], color='#795548', lw=3, label='Together drift'),
        Line2D([0], [0], color='red', linestyle='--', lw=2, label='Event Horizon'),
        Line2D([0], [0], marker='*', color='gold', markersize=15,
               linestyle='None', label='I_AM attractor'),
    ]
    ax.legend(handles=legend_elements, loc='lower right', fontsize=8)

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    from pathlib import Path

    # Output to pics/ subdirectory (PNG only - PDFs generated on-demand for papers)
    script_dir = Path(__file__).parent
    pics_dir = script_dir / 'pics'
    pics_dir.mkdir(exist_ok=True)

    fig = create_figure()

    # Save PNG only to pics/ - CONCEPTUAL diagram (not data visualization)
    output_path = pics_dir / 'fig2_drift_field_CONCEPTUAL.png'
    fig.savefig(output_path, dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print(f"Figure 2 saved: {output_path}")
    plt.show()
