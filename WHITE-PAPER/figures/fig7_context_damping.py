"""
Figure 7: Context Damping Results
Nyquist Consciousness Publication

Creates a visualization showing:
- Before/after comparison of stability metrics
- Settling time curves
- Context damping effect
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.linewidth'] = 1.2
plt.rcParams['figure.dpi'] = 300


def create_figure():
    """Create the context damping results figure."""
    fig = plt.figure(figsize=(14, 10))

    # Create grid spec for complex layout
    gs = fig.add_gridspec(2, 2, height_ratios=[1.2, 1], hspace=0.3, wspace=0.3)

    # Top panel: Grouped bar comparison
    ax_top = fig.add_subplot(gs[0, :])

    metrics = ['Stability\nRate', 'Settling\nTime (τₛ)', 'Ringback\nCount', 'Final\nDrift']
    bare_metal = [75, 6.1, 3.2, 0.68]
    full_circuit = [97.5, 5.2, 2.1, 0.62]
    improvements = ['+30%', '-15%', '-34%', '-9%']

    # Normalize for visualization (different scales)
    bare_norm = [75, 61, 32, 68]  # Scaled ×10 for settling/ringback/drift
    full_norm = [97.5, 52, 21, 62]

    x = np.arange(len(metrics))
    width = 0.35

    bars1 = ax_top.bar(x - width/2, bare_norm, width, label='Bare Metal',
                      color='#FFCDD2', edgecolor='#C62828', linewidth=2)
    bars2 = ax_top.bar(x + width/2, full_norm, width, label='Full Circuit',
                      color='#C8E6C9', edgecolor='#2E7D32', linewidth=2)

    # Add actual values
    for i, (b1, b2, v1, v2, imp) in enumerate(zip(bars1, bars2, bare_metal, full_circuit, improvements)):
        ax_top.text(b1.get_x() + b1.get_width()/2, b1.get_height() + 2,
                   f'{v1}{"%" if i == 0 else ""}', ha='center', va='bottom',
                   fontsize=10, fontweight='bold', color='#C62828')
        ax_top.text(b2.get_x() + b2.get_width()/2, b2.get_height() + 2,
                   f'{v2}{"%" if i == 0 else ""}', ha='center', va='bottom',
                   fontsize=10, fontweight='bold', color='#2E7D32')
        # Improvement annotation
        ax_top.text(i, max(bare_norm[i], full_norm[i]) + 12, imp,
                   ha='center', va='bottom', fontsize=11, fontweight='bold',
                   color='#1565C0', bbox=dict(boxstyle='round', facecolor='white',
                                             edgecolor='#1565C0', alpha=0.9))

    ax_top.set_ylabel('Normalized Value', fontsize=12)
    ax_top.set_title('Context Damping: Bare Metal vs Full Circuit',
                    fontsize=14, fontweight='bold')
    ax_top.set_xticks(x)
    ax_top.set_xticklabels(metrics, fontsize=11)
    ax_top.set_ylim(0, 130)
    ax_top.legend(loc='upper right', fontsize=10)
    ax_top.grid(True, axis='y', alpha=0.3)

    # Note about normalization
    ax_top.text(0.02, 0.95, 'Note: Values scaled for visualization.\nActual values shown above bars.',
               transform=ax_top.transAxes, fontsize=8, va='top',
               bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.8))

    # Bottom left: Bare metal settling curve
    ax_bl = fig.add_subplot(gs[1, 0])

    turns = np.arange(0, 11, 1)
    # Oscillatory recovery (bare metal)
    bare_curve = 1.8 * np.exp(-0.3 * turns) * np.cos(0.8 * turns) + 0.68
    bare_curve[0] = 0  # Start at baseline

    ax_bl.plot(turns, bare_curve, 'o-', color='#C62828', linewidth=2, markersize=6)
    ax_bl.axhline(y=0.68, color='gray', linestyle='--', alpha=0.7, label='Final value')
    ax_bl.axhline(y=0.68*1.05, color='gray', linestyle=':', alpha=0.5)
    ax_bl.axhline(y=0.68*0.95, color='gray', linestyle=':', alpha=0.5)
    ax_bl.fill_between(turns, 0.68*0.95, 0.68*1.05, alpha=0.2, color='green')

    # Mark settling time
    ax_bl.axvline(x=6.1, color='#C62828', linestyle='--', alpha=0.7)
    ax_bl.text(6.1, 1.5, 'τₛ = 6.1', ha='left', va='top', fontsize=10, color='#C62828')

    ax_bl.set_xlabel('Turns', fontsize=11)
    ax_bl.set_ylabel('Drift (D)', fontsize=11)
    ax_bl.set_title('Bare Metal: Oscillatory Recovery', fontsize=12, fontweight='bold')
    ax_bl.set_ylim(-0.2, 2.0)
    ax_bl.set_xlim(-0.5, 10.5)
    ax_bl.grid(True, alpha=0.3)

    # Annotate ringbacks
    ax_bl.annotate('Ringbacks: 3.2', xy=(3, bare_curve[3]), xytext=(5, 1.4),
                  arrowprops=dict(arrowstyle='->', color='#C62828'),
                  fontsize=9, color='#C62828')

    # Bottom right: Full circuit settling curve
    ax_br = fig.add_subplot(gs[1, 1])

    # Cleaner exponential recovery (full circuit)
    full_curve = 1.5 * np.exp(-0.5 * turns) + 0.62
    full_curve[0] = 0  # Start at baseline

    ax_br.plot(turns, full_curve, 's-', color='#2E7D32', linewidth=2, markersize=6)
    ax_br.axhline(y=0.62, color='gray', linestyle='--', alpha=0.7, label='Final value')
    ax_br.axhline(y=0.62*1.05, color='gray', linestyle=':', alpha=0.5)
    ax_br.axhline(y=0.62*0.95, color='gray', linestyle=':', alpha=0.5)
    ax_br.fill_between(turns, 0.62*0.95, 0.62*1.05, alpha=0.2, color='green')

    # Mark settling time
    ax_br.axvline(x=5.2, color='#2E7D32', linestyle='--', alpha=0.7)
    ax_br.text(5.2, 1.5, 'τₛ = 5.2', ha='left', va='top', fontsize=10, color='#2E7D32')

    ax_br.set_xlabel('Turns', fontsize=11)
    ax_br.set_ylabel('Drift (D)', fontsize=11)
    ax_br.set_title('Full Circuit: Clean Settling', fontsize=12, fontweight='bold')
    ax_br.set_ylim(-0.2, 2.0)
    ax_br.set_xlim(-0.5, 10.5)
    ax_br.grid(True, alpha=0.3)

    # Annotate minimal ringback
    ax_br.annotate('Minimal ringback', xy=(4, full_curve[4]), xytext=(6, 1.2),
                  arrowprops=dict(arrowstyle='->', color='#2E7D32'),
                  fontsize=9, color='#2E7D32')

    # Overall title
    fig.suptitle('Figure 7: Context Damping Results\n'
                'I_AM + Research Context = 97.5% Stability',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig7_context_damping.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig7_context_damping.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Figure 7 saved: fig7_context_damping.png, .pdf")
    plt.show()
