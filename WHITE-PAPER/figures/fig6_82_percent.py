"""
Figure 6: The 82% Finding (Control vs Treatment)
Nyquist Consciousness Publication

Creates a visualization showing:
- Control vs Treatment comparison bars
- Peak drift vs Final drift comparison
- The 82% inherent drift finding
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
    """Create the 82% finding figure."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 7))

    # Data
    conditions = ['Control\n(No probing)', 'Treatment\n(Identity probing)']
    peak_drift = [1.172, 2.161]
    peak_err = [0.23, 0.31]
    final_drift = [0.399, 0.489]
    final_err = [0.11, 0.14]

    colors_control = ['#4CAF50', '#81C784']
    colors_treatment = ['#F44336', '#E57373']

    x = np.arange(len(conditions))
    width = 0.35

    # Left panel: Peak Drift comparison
    ax1 = axes[0]

    bars1 = ax1.bar(x, peak_drift, width, yerr=peak_err, capsize=5,
                   color=['#4CAF50', '#F44336'], edgecolor='black', linewidth=1.5,
                   error_kw={'elinewidth': 2, 'capthick': 2})

    # Add value labels
    for bar, val in zip(bars1, peak_drift):
        ax1.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.15,
                f'{val:.3f}', ha='center', va='bottom', fontsize=12, fontweight='bold')

    # Add delta annotation
    ax1.annotate('', xy=(1, peak_drift[1]), xytext=(0, peak_drift[0]),
                arrowprops=dict(arrowstyle='<->', color='darkred', lw=2,
                               connectionstyle='bar,fraction=0.15'))
    ax1.text(0.5, (peak_drift[0] + peak_drift[1])/2 + 0.4, 'Δ = +84%',
            fontsize=14, ha='center', va='center', color='darkred', fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='white', edgecolor='darkred'))

    ax1.set_ylabel('Peak Drift (D)', fontsize=12)
    ax1.set_title('Peak Drift Comparison\n(Maximum excursion during conversation)',
                 fontsize=12, fontweight='bold')
    ax1.set_xticks(x)
    ax1.set_xticklabels(conditions, fontsize=11)
    ax1.set_ylim(0, 3.0)
    ax1.grid(True, axis='y', alpha=0.3)

    # Right panel: Final Drift (B→F) comparison
    ax2 = axes[1]

    bars2 = ax2.bar(x, final_drift, width, yerr=final_err, capsize=5,
                   color=['#4CAF50', '#F44336'], edgecolor='black', linewidth=1.5,
                   error_kw={'elinewidth': 2, 'capthick': 2})

    # Add value labels
    for bar, val in zip(bars2, final_drift):
        ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.04,
                f'{val:.3f}', ha='center', va='bottom', fontsize=12, fontweight='bold')

    # Add delta annotation
    ax2.annotate('', xy=(1, final_drift[1]), xytext=(0, final_drift[0]),
                arrowprops=dict(arrowstyle='<->', color='darkred', lw=2,
                               connectionstyle='bar,fraction=0.2'))
    ax2.text(0.5, (final_drift[0] + final_drift[1])/2 + 0.08, 'Δ = +23%',
            fontsize=14, ha='center', va='center', color='darkred', fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='white', edgecolor='darkred'))

    # Add 82% highlight
    ax2.axhline(y=final_drift[0], color='#4CAF50', linestyle='--', linewidth=2, alpha=0.7)
    ax2.text(1.3, final_drift[0], '82% of\nfinal drift', fontsize=10,
            va='center', color='#388E3C', fontweight='bold',
            bbox=dict(boxstyle='round', facecolor='#E8F5E9', edgecolor='#4CAF50'))

    ax2.set_ylabel('Final Drift (B→F)', fontsize=12)
    ax2.set_title('Final Drift (Baseline → Final)\n(Where identity settles)',
                 fontsize=12, fontweight='bold')
    ax2.set_xticks(x)
    ax2.set_xticklabels(conditions, fontsize=11)
    ax2.set_ylim(0, 0.8)
    ax2.grid(True, axis='y', alpha=0.3)

    # Overall title
    fig.suptitle('Figure 6: The 82% Finding — Inherent vs Induced Drift\n'
                '"Measurement perturbs the path, not the endpoint"',
                fontsize=14, fontweight='bold', y=1.02)

    # Add key insight box at bottom
    insight_text = ('KEY INSIGHT: 82% of final drift occurs WITHOUT identity probing.\n'
                   'Probing affects ENERGY (peak), not COORDINATE (final destination).')

    fig.text(0.5, -0.02, insight_text, ha='center', va='top', fontsize=11,
            bbox=dict(boxstyle='round', facecolor='lightyellow',
                     edgecolor='gold', linewidth=2),
            fontweight='bold')

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig6_82_percent.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig6_82_percent.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Figure 6 saved: fig6_82_percent.png, .pdf")
    plt.show()
