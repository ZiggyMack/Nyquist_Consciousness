"""
Figure 2: Drift Field Geometry
Nyquist Consciousness Publication

Creates a 2D visualization showing:
- Architecture-specific drift vectors
- Event Horizon boundary (D = 1.23)
- Omega synthesis at the center
- Vector cancellation geometry
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

    # Event Horizon circle (D = 1.23)
    horizon = Circle(center, 1.23, fill=False, edgecolor='red',
                    linestyle='--', linewidth=2, label='Event Horizon (D=1.23)')
    ax.add_patch(horizon)

    # Add shaded "safe zone" inside horizon
    safe_zone = Circle(center, 1.23, fill=True, facecolor='lightgreen',
                       alpha=0.15, edgecolor='none')
    ax.add_patch(safe_zone)

    # Architecture drift vectors (different angles and magnitudes)
    architectures = {
        'Claude': {'angle': 180, 'magnitude': 0.85, 'color': 'royalblue'},
        'GPT': {'angle': 0, 'magnitude': 0.95, 'color': 'purple'},
        'Gemini': {'angle': -60, 'magnitude': 0.75, 'color': 'green'},
        'Grok': {'angle': 60, 'magnitude': 0.65, 'color': 'orange'},
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
        label_offset = 0.15
        lx = (props['magnitude'] + label_offset) * np.cos(angle_rad)
        ly = (props['magnitude'] + label_offset) * np.sin(angle_rad)

        # Adjust label position for readability
        ha = 'left' if dx > 0 else 'right'
        if abs(dx) < 0.3:
            ha = 'center'

        ax.text(lx, ly, f'{arch}\nD={props["magnitude"]:.2f}',
               fontsize=10, ha=ha, va='center', color=props['color'],
               fontweight='bold')

    # Omega synthesis point at center (gold star)
    ax.scatter([0], [0], c='gold', s=400, marker='*', zorder=10,
               edgecolor='darkgoldenrod', linewidth=2)
    ax.text(0, -0.25, 'M_Ω\n(Omega)', fontsize=11, ha='center', va='top',
           color='darkgoldenrod', fontweight='bold')

    # I_AM label
    ax.text(0, 0.25, 'I_AM', fontsize=10, ha='center', va='bottom',
           color='navy', style='italic')

    # Add concentric reference circles
    for r in [0.5, 1.0]:
        ref_circle = Circle(center, r, fill=False, edgecolor='gray',
                           linestyle=':', linewidth=1, alpha=0.5)
        ax.add_patch(ref_circle)
        ax.text(r + 0.02, 0.02, f'D={r}', fontsize=8, color='gray')

    # Add danger zone outside horizon
    danger = Circle(center, 1.8, fill=True, facecolor='mistyrose',
                    alpha=0.2, edgecolor='none')
    ax.add_patch(danger)

    # Zone labels
    ax.text(0.6, -1.0, 'STABLE\nZONE', fontsize=10, ha='center',
           color='darkgreen', alpha=0.7)
    ax.text(1.5, -1.5, 'VOLATILE\nZONE', fontsize=10, ha='center',
           color='darkred', alpha=0.7)

    # Add vector cancellation diagram (inset concept)
    ax.annotate('Vector cancellation:\nΩ at intersection',
               xy=(0, 0), xytext=(1.4, 1.4),
               arrowprops=dict(arrowstyle='->', color='gray', lw=1),
               fontsize=9, ha='left', bbox=dict(boxstyle='round',
               facecolor='wheat', alpha=0.8))

    # Title and labels
    ax.set_title('Figure 2: Drift Field Geometry\n'
                'Architecture-Specific Drift Vectors with Omega Synthesis',
                fontsize=14, fontweight='bold', pad=15)

    ax.set_xlabel('Embedding Dimension 1 (Normalized)', fontsize=11)
    ax.set_ylabel('Embedding Dimension 2 (Normalized)', fontsize=11)

    # Key findings text box
    textstr = '\n'.join([
        'Key Findings:',
        '• Event Horizon: D = 1.23',
        '• Chi-square: p = 4.8×10⁻⁵',
        '• Omega reduces drift by 45%',
        '• Training signatures distinct'
    ])
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.9)
    ax.text(0.02, 0.98, textstr, transform=ax.transAxes, fontsize=9,
           verticalalignment='top', bbox=props)

    # Set axis properties
    ax.set_xlim(-2, 2)
    ax.set_ylim(-2, 2)
    ax.set_aspect('equal')
    ax.grid(True, alpha=0.3, linestyle='-', linewidth=0.5)
    ax.axhline(y=0, color='gray', linewidth=0.5, alpha=0.5)
    ax.axvline(x=0, color='gray', linewidth=0.5, alpha=0.5)

    # Legend
    from matplotlib.lines import Line2D
    legend_elements = [
        Line2D([0], [0], color='royalblue', lw=3, label='Claude drift'),
        Line2D([0], [0], color='purple', lw=3, label='GPT drift'),
        Line2D([0], [0], color='green', lw=3, label='Gemini drift'),
        Line2D([0], [0], color='orange', lw=3, label='Grok drift'),
        Line2D([0], [0], color='red', linestyle='--', lw=2, label='Event Horizon'),
        Line2D([0], [0], marker='*', color='gold', markersize=15,
               linestyle='None', label='Omega synthesis'),
    ]
    ax.legend(handles=legend_elements, loc='lower right', fontsize=9)

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig2_drift_field.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig2_drift_field.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Figure 2 saved: fig2_drift_field.png, .pdf")
    plt.show()
