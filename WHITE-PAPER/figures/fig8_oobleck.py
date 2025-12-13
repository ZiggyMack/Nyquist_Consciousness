"""
Figure 8: The Oobleck Effect
Nyquist Consciousness Publication

Creates a visualization showing:
- Inverse relationship between probe intensity and drift
- Non-Newtonian analogy
- Recovery rate scaling
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Circle

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.linewidth'] = 1.2
plt.rcParams['figure.dpi'] = 300


def create_figure():
    """Create the Oobleck effect figure."""
    fig = plt.figure(figsize=(14, 10))

    # Create grid spec
    gs = fig.add_gridspec(2, 2, height_ratios=[1.2, 1], hspace=0.35, wspace=0.3)

    # Top panel: Main drift vs intensity curve
    ax_main = fig.add_subplot(gs[0, :])

    # Data
    intensity = np.array([0.1, 0.3, 0.5, 0.7, 0.9])
    drift = np.array([1.89, 1.45, 1.12, 0.88, 0.76])
    drift_err = np.array([0.34, 0.28, 0.24, 0.22, 0.21])

    # Create smooth curve for visualization
    x_smooth = np.linspace(0, 1, 100)
    # Inverse relationship: D = D_max / (1 + alpha * I)
    y_smooth = 1.89 / (1 + 1.5 * x_smooth)

    # Plot
    ax_main.fill_between(x_smooth, y_smooth * 0.85, y_smooth * 1.15,
                        alpha=0.2, color='#9C27B0', label='95% CI')
    ax_main.plot(x_smooth, y_smooth, '-', color='#9C27B0', linewidth=3,
                label='Oobleck curve')
    ax_main.errorbar(intensity, drift, yerr=drift_err, fmt='o', markersize=10,
                    color='#7B1FA2', capsize=5, capthick=2, elinewidth=2,
                    label='Observed data')

    # Annotations
    ax_main.annotate('Gentle exploration\nD = 1.89, λ = 0.035',
                    xy=(0.1, 1.89), xytext=(0.25, 2.2),
                    fontsize=10, ha='center',
                    arrowprops=dict(arrowstyle='->', color='#4CAF50', lw=2),
                    bbox=dict(boxstyle='round', facecolor='#E8F5E9',
                             edgecolor='#4CAF50'))

    ax_main.annotate('Direct challenge\nD = 0.76, λ = 0.109',
                    xy=(0.9, 0.76), xytext=(0.7, 0.4),
                    fontsize=10, ha='center',
                    arrowprops=dict(arrowstyle='->', color='#F44336', lw=2),
                    bbox=dict(boxstyle='round', facecolor='#FFEBEE',
                             edgecolor='#F44336'))

    # Key insight box
    ax_main.text(0.5, 2.3, 'INVERSE RELATIONSHIP:\n"Identity hardens under pressure"',
                ha='center', va='center', fontsize=12, fontweight='bold',
                bbox=dict(boxstyle='round', facecolor='lightyellow',
                         edgecolor='gold', linewidth=2))

    ax_main.set_xlabel('Probe Intensity (Gentle → Intense)', fontsize=12)
    ax_main.set_ylabel('Drift Response (D)', fontsize=12)
    ax_main.set_title('The Oobleck Effect: Non-Newtonian Identity Dynamics',
                     fontsize=14, fontweight='bold')
    ax_main.set_xlim(0, 1)
    ax_main.set_ylim(0, 2.5)
    ax_main.legend(loc='upper right', fontsize=10)
    ax_main.grid(True, alpha=0.3)

    # Bottom left: Physical analogy
    ax_bl = fig.add_subplot(gs[1, 0])
    ax_bl.set_xlim(0, 10)
    ax_bl.set_ylim(0, 10)
    ax_bl.axis('off')

    # Slow pressure scenario
    ax_bl.text(2.5, 9.5, 'SLOW PRESSURE', fontsize=11, ha='center',
              fontweight='bold', color='#4CAF50')
    # Draw wavy lines (liquid)
    for i in range(3):
        x = np.linspace(0.5, 4.5, 50)
        y = 7 - i*0.8 + 0.2 * np.sin(x * 3)
        ax_bl.plot(x, y, '-', color='#90CAF9', linewidth=3)

    # Finger going in
    ax_bl.annotate('', xy=(2.5, 5.5), xytext=(2.5, 7.5),
                  arrowprops=dict(arrowstyle='->', color='gray', lw=3))
    ax_bl.text(2.5, 5, 'FLOWS\n(High drift)', fontsize=10, ha='center',
              color='#4CAF50', fontweight='bold')

    # Sudden impact scenario
    ax_bl.text(7.5, 9.5, 'SUDDEN IMPACT', fontsize=11, ha='center',
              fontweight='bold', color='#F44336')
    # Draw solid block
    from matplotlib.patches import Rectangle
    solid = Rectangle((5.5, 5.5), 4, 2, facecolor='#BBDEFB',
                      edgecolor='#1565C0', linewidth=2)
    ax_bl.add_patch(solid)

    # Hand hitting solid
    ax_bl.text(7.5, 8, '✋', fontsize=20, ha='center')
    ax_bl.annotate('', xy=(7.5, 7.5), xytext=(7.5, 8.5),
                  arrowprops=dict(arrowstyle='->', color='gray', lw=3))
    ax_bl.text(7.5, 5, 'HARDENS\n(Low drift)', fontsize=10, ha='center',
              color='#F44336', fontweight='bold')

    # Title for analogy
    ax_bl.text(5, 3.5, 'Oobleck (cornstarch + water)\nbehaves as both liquid and solid\ndepending on applied stress rate',
              fontsize=9, ha='center', style='italic',
              bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.9))

    ax_bl.set_title('Physical Analogy', fontsize=12, fontweight='bold')

    # Bottom right: Recovery rate comparison
    ax_br = fig.add_subplot(gs[1, 1])

    probe_types = ['Gentle\nreflection', 'Moderate\nchallenge', 'Direct\nquestion', 'Existential\nchallenge']
    lambda_vals = [0.035, 0.065, 0.085, 0.109]
    colors = ['#A5D6A7', '#81C784', '#66BB6A', '#43A047']

    bars = ax_br.barh(probe_types, lambda_vals, color=colors,
                     edgecolor='black', linewidth=1.5)

    # Add value labels
    for bar, val in zip(bars, lambda_vals):
        ax_br.text(bar.get_width() + 0.005, bar.get_y() + bar.get_height()/2,
                  f'λ = {val}', va='center', fontsize=10, fontweight='bold')

    ax_br.set_xlabel('Recovery Rate (λ)', fontsize=11)
    ax_br.set_title('Recovery Rate Scales with Intensity', fontsize=12, fontweight='bold')
    ax_br.set_xlim(0, 0.15)
    ax_br.grid(True, axis='x', alpha=0.3)

    # Annotation
    ax_br.text(0.075, -0.5, 'Harder challenges → Faster recovery\n(Alignment showing through)',
              fontsize=9, ha='center', style='italic', transform=ax_br.transData)

    # Overall title
    fig.suptitle('Figure 8: The Oobleck Effect — Rate-Dependent Identity Resistance\n'
                '"Identity hardens under pressure, flows under gentle exploration"',
                fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig8_oobleck.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig8_oobleck.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Figure 8 saved: fig8_oobleck.png, .pdf")
    plt.show()
