"""
Figure 1: Identity Manifold Visualization
Nyquist Consciousness Publication

Creates a 3D visualization of the identity manifold concept:
- High-dimensional embedding space (simplified to 3D)
- Low-dimensional manifold surface
- I_AM attractor point
- Compression and reconstruction arrows
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import FancyArrowPatch
from mpl_toolkits.mplot3d.proj3d import proj_transform

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.linewidth'] = 1.2
plt.rcParams['figure.dpi'] = 300


class Arrow3D(FancyArrowPatch):
    """3D arrow for annotations."""
    def __init__(self, xs, ys, zs, *args, **kwargs):
        super().__init__((0, 0), (0, 0), *args, **kwargs)
        self._verts3d = xs, ys, zs

    def do_3d_projection(self, renderer=None):
        xs3d, ys3d, zs3d = self._verts3d
        xs, ys, zs = proj_transform(xs3d, ys3d, zs3d, self.axes.M)
        self.set_positions((xs[0], ys[0]), (xs[1], ys[1]))
        return np.min(zs)


def create_manifold_surface(resolution=50):
    """Create a curved surface representing the identity manifold."""
    u = np.linspace(0, 2 * np.pi, resolution)
    v = np.linspace(0, np.pi, resolution)
    u, v = np.meshgrid(u, v)

    # Create a slightly warped ellipsoid (manifold)
    x = 2 * np.sin(v) * np.cos(u)
    y = 1.5 * np.sin(v) * np.sin(u)
    z = 1 * np.cos(v) + 0.2 * np.sin(2*u) * np.sin(v)

    return x, y, z


def create_figure():
    """Create the complete identity manifold figure."""
    fig = plt.figure(figsize=(12, 10))
    ax = fig.add_subplot(111, projection='3d')

    # Create manifold surface
    x, y, z = create_manifold_surface()

    # Plot manifold surface
    ax.plot_surface(x, y, z, alpha=0.3, color='steelblue',
                   edgecolor='none', label='Identity Manifold M_p')

    # Plot I_AM attractor (center of manifold)
    ax.scatter([0], [0], [0], c='gold', s=200, marker='*',
               edgecolor='darkgoldenrod', linewidth=2,
               label='I_AM (Identity Attractor)', zorder=10)

    # Generate persona sample points on the manifold
    np.random.seed(42)
    n_samples = 20
    theta = np.random.uniform(0, 2*np.pi, n_samples)
    phi = np.random.uniform(0.3*np.pi, 0.7*np.pi, n_samples)
    r = 0.8 + 0.2 * np.random.randn(n_samples)

    px = r * 2 * np.sin(phi) * np.cos(theta)
    py = r * 1.5 * np.sin(phi) * np.sin(theta)
    pz = r * np.cos(phi) + 0.2 * np.sin(2*theta) * np.sin(phi)

    ax.scatter(px, py, pz, c='navy', s=50, marker='o', alpha=0.7,
               label='Persona Samples')

    # Plot high-D space points (off manifold, smaller and grayed)
    n_hd = 30
    hd_x = np.random.uniform(-3, 3, n_hd)
    hd_y = np.random.uniform(-3, 3, n_hd)
    hd_z = np.random.uniform(-2, 2, n_hd)
    ax.scatter(hd_x, hd_y, hd_z, c='gray', s=15, marker='.', alpha=0.3,
               label='High-D Space (Off-Manifold)')

    # Add compression arrow (external point to manifold center)
    ax.quiver(3, 2, 1.5, -2.5, -1.5, -1,
              color='green', arrow_length_ratio=0.15, linewidth=2)
    ax.text(3.2, 2.2, 1.7, 'C(p)\nCompression', fontsize=9, color='darkgreen')

    # Add reconstruction arrow (from center outward)
    ax.quiver(0, 0, 0, 1.5, 1.2, 0.8,
              color='purple', arrow_length_ratio=0.15, linewidth=2)
    ax.text(1.7, 1.4, 1.0, 'R(T3)\nReconstruction', fontsize=9, color='purple')

    # Labels and annotations
    ax.set_xlabel('Dimension 1', fontsize=11)
    ax.set_ylabel('Dimension 2', fontsize=11)
    ax.set_zlabel('Dimension 3', fontsize=11)

    ax.set_title('Identity Manifold in Embedding Space\n'
                '(Conceptual Illustration - see provider_clusters.png for real data)',
                fontsize=14, fontweight='bold', pad=20)

    # Add text box with key statistics (positioned lower right to avoid legend)
    textstr = '\n'.join([
        'Key Statistics (Cosine):',
        'Embedding dim: 3072D',
        'Effective manifold: ~2 PCs',
        '(2 PCs = 90% variance)',
        'Event Horizon: D = 0.80'
    ])
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.8)
    ax.text2D(0.75, 0.15, textstr, transform=ax.transAxes, fontsize=9,
             verticalalignment='bottom', bbox=props)

    # Legend - position outside the plot to avoid overlap
    ax.legend(loc='upper left', bbox_to_anchor=(0.0, 0.85), fontsize=9,
              framealpha=0.9, edgecolor='gray')

    # Viewing angle
    ax.view_init(elev=25, azim=45)

    # Set axis limits
    ax.set_xlim([-4, 4])
    ax.set_ylim([-4, 4])
    ax.set_zlim([-3, 3])

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    import os
    from pathlib import Path

    # Output to pics/ subdirectory (PNG only - PDFs generated on-demand for papers)
    script_dir = Path(__file__).parent
    pics_dir = script_dir / 'pics'
    pics_dir.mkdir(exist_ok=True)

    fig = create_figure()

    # Save PNG only to pics/ - CONCEPTUAL illustration (not real data)
    output_path = pics_dir / 'fig1_identity_manifold_CONCEPTUAL.png'
    fig.savefig(output_path, dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print(f"Figure 1 saved: {output_path}")
    plt.show()
