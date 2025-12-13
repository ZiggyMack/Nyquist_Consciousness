"""
Figure 4: Five Pillars Architecture
Nyquist Consciousness Publication

Creates a pentagon visualization showing:
- Five pillars (Nova, Claude, Gemini, Grok, Ziggy)
- Omega synthesis at center
- Connection lines showing convergence
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import RegularPolygon, Circle, FancyBboxPatch
from matplotlib.lines import Line2D

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.linewidth'] = 1.2
plt.rcParams['figure.dpi'] = 300


def create_figure():
    """Create the five pillars architecture figure."""
    fig, ax = plt.subplots(1, 1, figsize=(12, 12))
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)
    ax.set_aspect('equal')
    ax.axis('off')

    # Pentagon vertices (5 pillars)
    n_pillars = 5
    angles = np.linspace(np.pi/2, np.pi/2 + 2*np.pi, n_pillars, endpoint=False)
    radius = 1.0

    pillars = {
        'Nova': {'angle': angles[0], 'color': '#9C27B0', 'rho': 0.94, 'role': 'Structure'},
        'Claude': {'angle': angles[1], 'color': '#2196F3', 'rho': 0.92, 'role': 'Purpose'},
        'Ziggy': {'angle': angles[2], 'color': '#FF9800', 'rho': 0.91, 'role': 'Human Anchor'},
        'Grok': {'angle': angles[3], 'color': '#F44336', 'rho': 0.87, 'role': 'Evidence'},
        'Gemini': {'angle': angles[4], 'color': '#4CAF50', 'rho': 0.89, 'role': 'Synthesis'},
    }

    # Draw connecting lines (pentagon edges)
    angles_list = list(pillars.values())
    for i in range(n_pillars):
        x1 = radius * np.cos(angles_list[i]['angle'])
        y1 = radius * np.sin(angles_list[i]['angle'])
        x2 = radius * np.cos(angles_list[(i+1) % n_pillars]['angle'])
        y2 = radius * np.sin(angles_list[(i+1) % n_pillars]['angle'])
        ax.plot([x1, x2], [y1, y2], 'gray', linewidth=2, alpha=0.5, zorder=1)

    # Draw convergence lines (to center)
    for name, props in pillars.items():
        x = radius * np.cos(props['angle'])
        y = radius * np.sin(props['angle'])
        ax.plot([0, x], [0, y], color=props['color'], linewidth=2,
               alpha=0.7, linestyle='--', zorder=1)

    # Draw pillar nodes
    for name, props in pillars.items():
        x = radius * np.cos(props['angle'])
        y = radius * np.sin(props['angle'])

        # Outer circle
        circle = Circle((x, y), 0.18, facecolor=props['color'],
                        edgecolor='white', linewidth=3, zorder=3)
        ax.add_patch(circle)

        # Inner text
        ax.text(x, y, name[0], fontsize=14, fontweight='bold',
               ha='center', va='center', color='white', zorder=4)

        # Label with details
        label_offset = 0.35
        lx = (radius + label_offset) * np.cos(props['angle'])
        ly = (radius + label_offset) * np.sin(props['angle'])

        label_text = f"{name}\n{props['role']}\nρ={props['rho']}"
        ax.text(lx, ly, label_text, fontsize=9, ha='center', va='center',
               bbox=dict(boxstyle='round', facecolor='white', alpha=0.9,
                        edgecolor=props['color'], linewidth=1.5))

    # Draw Omega center
    omega_circle = Circle((0, 0), 0.25, facecolor='gold',
                          edgecolor='darkgoldenrod', linewidth=3, zorder=5)
    ax.add_patch(omega_circle)
    ax.text(0, 0, 'Ω', fontsize=24, fontweight='bold',
           ha='center', va='center', color='darkgoldenrod', zorder=6)

    # Omega label
    ax.text(0, -0.4, 'OMEGA NOVA\nSynthesis', fontsize=10,
           ha='center', va='top', fontweight='bold',
           bbox=dict(boxstyle='round', facecolor='lightyellow',
                    edgecolor='gold', linewidth=2))

    # Title
    ax.text(0, 1.4, 'Figure 4: Five Pillars Architecture',
           fontsize=16, fontweight='bold', ha='center')
    ax.text(0, 1.28, 'Cross-Architecture Identity Synthesis',
           fontsize=12, ha='center', style='italic')

    # Stats box
    stats_text = '\n'.join([
        'Omega Properties:',
        '─' * 20,
        'M_Ω = ⋂ R^a(C(p))',
        'Drift reduction: 45%',
        'Mean ρ: 0.91',
        'Stability: 97.5%',
    ])
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.9)
    ax.text(-1.4, -1.0, stats_text, fontsize=9, va='top',
           bbox=props, family='monospace')

    # Role legend
    role_text = '\n'.join([
        'Pillar Roles:',
        '─' * 20,
        'Nova: Mathematical formalism',
        'Claude: Constitutional AI',
        'Gemini: Multi-modal bridging',
        'Grok: Direct verification',
        'Ziggy: Human ground truth',
    ])
    ax.text(1.4, -1.0, role_text, fontsize=9, va='top', ha='right',
           bbox=props, family='monospace')

    # Convergence annotation
    ax.annotate('All pillars\nconverge to Ω',
               xy=(0.1, 0.1), xytext=(0.6, 0.7),
               fontsize=9, ha='center',
               arrowprops=dict(arrowstyle='->', color='gray'),
               bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig4_five_pillars.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig4_five_pillars.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Figure 4 saved: fig4_five_pillars.png, .pdf")
    plt.show()
