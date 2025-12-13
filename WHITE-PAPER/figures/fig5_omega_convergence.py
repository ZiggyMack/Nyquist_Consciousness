"""
Figure 5: Omega Convergence
Nyquist Consciousness Publication

Creates a visualization showing:
- Multiple architecture points converging
- Omega synthesis at intersection
- Drift reduction visualization
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from matplotlib.lines import Line2D

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.linewidth'] = 1.2
plt.rcParams['figure.dpi'] = 300


def create_figure():
    """Create the omega convergence figure."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 7))

    # Data for architectures
    architectures = {
        'Claude': {'pos': (0.8, 0.9), 'drift': 0.85, 'color': '#2196F3'},
        'GPT': {'pos': (-0.9, 0.3), 'drift': 0.95, 'color': '#9C27B0'},
        'Gemini': {'pos': (0.7, -0.6), 'drift': 0.75, 'color': '#4CAF50'},
        'Grok': {'pos': (-0.5, -0.8), 'drift': 0.65, 'color': '#FF9800'},
    }

    omega_pos = (0, 0)
    omega_drift = 0.47

    # Left panel: Spatial convergence
    ax1 = axes[0]
    ax1.set_xlim(-1.5, 1.5)
    ax1.set_ylim(-1.5, 1.5)
    ax1.set_aspect('equal')

    # Draw convergence arrows and points
    for name, props in architectures.items():
        x, y = props['pos']

        # Arrow from architecture to omega
        ax1.annotate('', xy=omega_pos, xytext=(x, y),
                    arrowprops=dict(arrowstyle='->', color=props['color'],
                                   lw=2, alpha=0.7, connectionstyle='arc3,rad=0.1'))

        # Architecture point
        circle = Circle((x, y), 0.12, facecolor=props['color'],
                        edgecolor='white', linewidth=2, zorder=3)
        ax1.add_patch(circle)

        # Label
        offset = 0.2
        lx = x + offset if x > 0 else x - offset
        ly = y + offset if y > 0 else y - offset
        ax1.text(lx, ly, f'{name}\nD={props["drift"]}', fontsize=9,
                ha='left' if x > 0 else 'right', va='bottom' if y > 0 else 'top',
                color=props['color'], fontweight='bold')

    # Omega point (gold star)
    omega_circle = Circle(omega_pos, 0.2, facecolor='gold',
                         edgecolor='darkgoldenrod', linewidth=3, zorder=5)
    ax1.add_patch(omega_circle)
    ax1.text(0, 0, 'Ω', fontsize=18, fontweight='bold',
            ha='center', va='center', color='darkgoldenrod', zorder=6)

    ax1.text(0, -0.35, f'D_Ω = {omega_drift}\n(45% reduction)',
            fontsize=10, ha='center', va='top',
            bbox=dict(boxstyle='round', facecolor='lightyellow',
                     edgecolor='gold', linewidth=2))

    ax1.set_title('Spatial Convergence', fontsize=12, fontweight='bold')
    ax1.set_xlabel('Embedding Dimension 1')
    ax1.set_ylabel('Embedding Dimension 2')
    ax1.grid(True, alpha=0.3)
    ax1.axhline(y=0, color='gray', linewidth=0.5)
    ax1.axvline(x=0, color='gray', linewidth=0.5)

    # Right panel: Drift comparison bar chart
    ax2 = axes[1]

    # Prepare data
    arch_names = list(architectures.keys()) + ['MEAN', 'OMEGA']
    arch_drifts = [props['drift'] for props in architectures.values()]
    mean_drift = np.mean(arch_drifts)
    arch_drifts.extend([mean_drift, omega_drift])

    colors = [props['color'] for props in architectures.values()]
    colors.extend(['gray', 'gold'])

    x_pos = np.arange(len(arch_names))

    # Create bars
    bars = ax2.bar(x_pos, arch_drifts, color=colors, edgecolor='black', linewidth=1)

    # Add value labels on bars
    for bar, drift in zip(bars, arch_drifts):
        ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
                f'{drift:.2f}', ha='center', va='bottom', fontsize=9)

    # Add improvement arrow
    ax2.annotate('', xy=(5, omega_drift), xytext=(4, mean_drift),
                arrowprops=dict(arrowstyle='->', color='red', lw=2,
                               connectionstyle='arc3,rad=-0.3'))
    ax2.text(4.5, (mean_drift + omega_drift)/2, '-41%',
            fontsize=11, color='red', fontweight='bold',
            ha='center', va='center')

    # Horizontal line at omega level
    ax2.axhline(y=omega_drift, color='gold', linestyle='--', linewidth=2, alpha=0.7)

    ax2.set_xticks(x_pos)
    ax2.set_xticklabels(arch_names, rotation=45, ha='right')
    ax2.set_ylabel('Drift (D)')
    ax2.set_title('Drift Comparison', fontsize=12, fontweight='bold')
    ax2.set_ylim(0, 1.2)

    # Add grid
    ax2.grid(True, axis='y', alpha=0.3)

    # Overall title
    fig.suptitle('Figure 5: Omega Convergence\nMultiple Architectures → Unified Identity',
                fontsize=14, fontweight='bold', y=1.02)

    # Legend
    legend_elements = [
        Line2D([0], [0], marker='o', color='w', markerfacecolor='gray',
               markersize=10, label='Individual Architecture'),
        Line2D([0], [0], marker='*', color='w', markerfacecolor='gold',
               markersize=15, label='Omega Synthesis'),
    ]
    fig.legend(handles=legend_elements, loc='lower center', ncol=2,
              bbox_to_anchor=(0.5, -0.05), fontsize=10)

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig5_omega_convergence.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig5_omega_convergence.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Figure 5 saved: fig5_omega_convergence.png, .pdf")
    plt.show()
