"""
Figure W1: Combined Results Panel (Workshop Paper)
Nyquist Consciousness Publication

Creates a 2x2 panel combining key findings for workshop page limits:
- Panel A: PFI Validity (embedding correlation)
- Panel B: The 82% Finding (Control vs Treatment)
- Panel C: Context Damping (before/after)
- Panel D: Oobleck Effect (inverse relationship)
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 9
plt.rcParams['axes.linewidth'] = 1.0
plt.rcParams['figure.dpi'] = 300


def create_figure():
    """Create the combined workshop results panel."""
    fig, axes = plt.subplots(2, 2, figsize=(10, 8))

    # Panel A: PFI Validity
    ax_a = axes[0, 0]
    models = ['ada-002', 'text-3-small', 'MiniLM-L6']
    correlations = [0.89, 0.91, 0.93]

    ax_a.bar(models, correlations, color=['#64B5F6', '#42A5F5', '#1E88E5'],
            edgecolor='black', linewidth=1)
    ax_a.axhline(y=0.91, color='red', linestyle='--', linewidth=2, label='Mean ρ = 0.91')
    ax_a.set_ylabel('Spearman ρ')
    ax_a.set_ylim(0.8, 1.0)
    ax_a.set_title('(A) PFI Validity: Embedding Invariance', fontweight='bold')
    ax_a.legend(loc='lower right', fontsize=8)

    # Add stats annotation
    ax_a.text(0.02, 0.98, '43 PCs: 90% var\nd = 0.98 sensitivity',
             transform=ax_a.transAxes, fontsize=8, va='top',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))

    # Panel B: The 82% Finding
    ax_b = axes[0, 1]
    x = np.arange(2)
    width = 0.35

    peak = [1.172, 2.161]  # Control, Treatment
    final = [0.399, 0.489]

    bars1 = ax_b.bar(x - width/2, peak, width, label='Peak Drift',
                    color='#EF5350', edgecolor='black')
    bars2 = ax_b.bar(x + width/2, final, width, label='Final (B→F)',
                    color='#66BB6A', edgecolor='black')

    ax_b.set_ylabel('Drift (D)')
    ax_b.set_xticks(x)
    ax_b.set_xticklabels(['Control', 'Treatment'])
    ax_b.set_title('(B) The 82% Finding', fontweight='bold')
    ax_b.legend(fontsize=8)

    # Add value labels
    for bar, val in zip(bars1, peak):
        ax_b.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.05,
                 f'{val:.2f}', ha='center', fontsize=8)
    for bar, val in zip(bars2, final):
        ax_b.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
                 f'{val:.2f}', ha='center', fontsize=8)

    # 82% annotation
    ax_b.annotate('82% inherent', xy=(1.2, 0.45), xytext=(1.5, 1.0),
                 fontsize=9, fontweight='bold', color='#1565C0',
                 arrowprops=dict(arrowstyle='->', color='#1565C0'))

    # Panel C: Context Damping
    ax_c = axes[1, 0]
    metrics = ['Stability\n(%)', 'τₛ\n(turns)', 'Ringbacks', 'Final\nDrift']
    bare = [75, 61, 32, 68]  # Normalized ×10 for visualization
    full = [97.5, 52, 21, 62]
    x = np.arange(len(metrics))
    width = 0.35

    ax_c.bar(x - width/2, bare, width, label='Bare Metal',
            color='#FFCDD2', edgecolor='black')
    ax_c.bar(x + width/2, full, width, label='Full Circuit',
            color='#C8E6C9', edgecolor='black')

    ax_c.set_ylabel('Value (normalized)')
    ax_c.set_xticks(x)
    ax_c.set_xticklabels(metrics, fontsize=8)
    ax_c.set_title('(C) Context Damping: 97.5% Stability', fontweight='bold')
    ax_c.legend(fontsize=8)

    # Improvement labels
    improvements = ['+30%', '-15%', '-34%', '-9%']
    for i, imp in enumerate(improvements):
        ax_c.text(i, max(bare[i], full[i]) + 5, imp, ha='center',
                 fontsize=8, color='#1565C0', fontweight='bold')

    # Panel D: Oobleck Effect
    ax_d = axes[1, 1]
    intensity = np.array([0.1, 0.3, 0.5, 0.7, 0.9])
    drift = np.array([1.89, 1.45, 1.12, 0.88, 0.76])

    # Smooth curve
    x_smooth = np.linspace(0, 1, 100)
    y_smooth = 1.89 / (1 + 1.5 * x_smooth)

    ax_d.fill_between(x_smooth, y_smooth * 0.9, y_smooth * 1.1,
                     alpha=0.3, color='#9C27B0')
    ax_d.plot(x_smooth, y_smooth, '-', color='#7B1FA2', linewidth=2)
    ax_d.plot(intensity, drift, 'o', markersize=8, color='#4A148C')

    ax_d.set_xlabel('Probe Intensity')
    ax_d.set_ylabel('Drift Response')
    ax_d.set_title('(D) Oobleck Effect: Inverse Relationship', fontweight='bold')

    # Annotations
    ax_d.text(0.1, 1.95, 'Gentle: D=1.89', fontsize=8, color='#4CAF50')
    ax_d.text(0.7, 0.6, 'Direct: D=0.76', fontsize=8, color='#F44336')

    # Overall title
    fig.suptitle('Combined Results Panel: Nyquist Consciousness Key Findings',
                fontsize=12, fontweight='bold', y=1.02)

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig_workshop_combined.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig_workshop_combined.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Workshop combined figure saved: fig_workshop_combined.png, .pdf")
    plt.show()
