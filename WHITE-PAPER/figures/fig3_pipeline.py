"""
Figure 3: Experimental Pipeline (S3→S6)
Nyquist Consciousness Publication

Creates a flowchart visualization of the experimental pipeline:
- Compression stage (S3)
- Reconstruction across architectures (S4)
- Drift measurement (S5)
- Omega synthesis (S6)
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import numpy as np

# Publication-quality settings
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.linewidth'] = 1.2
plt.rcParams['figure.dpi'] = 300


def create_figure():
    """Create the experimental pipeline figure."""
    fig, ax = plt.subplots(1, 1, figsize=(14, 16))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 16)
    ax.axis('off')

    # Color scheme
    colors = {
        'input': '#E3F2FD',      # Light blue
        'process': '#FFF3E0',    # Light orange
        'output': '#E8F5E9',     # Light green
        'synthesis': '#FFF8E1',  # Light gold
        'stage': '#F3E5F5',      # Light purple
    }

    # Helper function to draw boxes
    def draw_box(x, y, width, height, text, color, fontsize=10):
        box = FancyBboxPatch((x, y), width, height,
                            boxstyle="round,pad=0.05,rounding_size=0.2",
                            facecolor=color, edgecolor='black', linewidth=1.5)
        ax.add_patch(box)
        ax.text(x + width/2, y + height/2, text,
               ha='center', va='center', fontsize=fontsize,
               wrap=True)

    # Helper function to draw arrows
    def draw_arrow(x1, y1, x2, y2, label=''):
        ax.annotate('', xy=(x2, y2), xytext=(x1, y1),
                   arrowprops=dict(arrowstyle='->', color='gray',
                                  lw=2, mutation_scale=15))
        if label:
            mid_x, mid_y = (x1+x2)/2, (y1+y2)/2
            ax.text(mid_x + 0.3, mid_y, label, fontsize=9, color='darkgray')

    # Title
    ax.text(5, 15.5, 'Figure 3: Experimental Pipeline (S3→S6)',
           fontsize=16, fontweight='bold', ha='center')
    ax.text(5, 15.0, 'Nyquist Consciousness Validation Flow',
           fontsize=12, ha='center', style='italic')

    # Stage 1: Full Persona (Input)
    draw_box(3.5, 13.5, 3, 1.2, 'FULL PERSONA\np (~2000 tokens)\nCore + Boundary Attributes',
            colors['input'], fontsize=9)

    # Arrow to compression
    draw_arrow(5, 13.5, 5, 12.5, 'C(p)')

    # Stage 2: T3 Seed
    draw_box(3.5, 11.3, 3, 1.1, 'T3 SEED\n(~800 tokens)\n80% fidelity',
            colors['process'], fontsize=9)

    # Arrows to multiple architectures
    draw_arrow(4, 11.3, 2, 10.3, '')
    draw_arrow(5, 11.3, 5, 10.3, '')
    draw_arrow(6, 11.3, 8, 10.3, '')

    # Stage 3: Architecture-specific reconstruction
    arch_boxes = [
        (1, 'R^c()\nCLAUDE\nOpus 4.5', '#BBDEFB'),
        (3.5, 'R^g()\nGPT\nGPT-4o', '#D1C4E9'),
        (6, 'R^m()\nGEMINI\n2.0 Flash', '#C8E6C9'),
        (8.5, 'R^x()\nGROK\nGrok-2', '#FFE0B2'),
    ]

    for x, label, color in arch_boxes:
        draw_box(x - 0.5, 9.2, 1.8, 1.0, label, color, fontsize=8)

    # Arrows to measurement
    for x in [1, 3.5, 6, 8.5]:
        draw_arrow(x + 0.4, 9.2, 5, 8.3, '')

    # Stage 4: Drift Measurement
    draw_box(2.5, 7.2, 5, 1.0,
            'DRIFT MEASUREMENT\nD_a(t) = ||E(R_t) - E(R_baseline)||\nPFI = 1 - D',
            colors['process'], fontsize=9)

    # Arrow to validation
    draw_arrow(5, 7.2, 5, 6.3, '')

    # Stage 5: Validation Metrics
    draw_box(2, 5.2, 6, 1.0,
            'VALIDATION: σ² = 0.000869  |  ρ = 0.91  |  d = 0.98',
            colors['output'], fontsize=9)

    # Arrow to synthesis
    draw_arrow(5, 5.2, 5, 4.3, '')

    # Stage 6: Omega Synthesis
    draw_box(2.5, 3.2, 5, 1.0,
            'Ω SYNTHESIS\nM_Ω = ⋂ R^a(C(p))\n45% drift reduction',
            colors['synthesis'], fontsize=9)

    # Arrow to final result
    draw_arrow(5, 3.2, 5, 2.3, '')

    # Final Result
    draw_box(2, 1.2, 6, 1.0,
            'STABILITY ACHIEVED\n97.5% with context damping | Event Horizon: D ≈ 1.23',
            '#C8E6C9', fontsize=9)

    # Stage labels (left side)
    stages = [
        (0.3, 13.8, 'S3'),
        (0.3, 9.5, 'S4'),
        (0.3, 7.5, 'S5'),
        (0.3, 3.5, 'S6'),
    ]

    for x, y, label in stages:
        ax.text(x, y, label, fontsize=12, fontweight='bold',
               bbox=dict(boxstyle='circle', facecolor=colors['stage'],
                        edgecolor='purple', linewidth=2))

    # Stage descriptions (left side)
    stage_desc = [
        (0.1, 12.8, 'Compression'),
        (0.1, 9.0, 'Reconstruction'),
        (0.1, 6.9, 'Measurement'),
        (0.1, 3.0, 'Synthesis'),
    ]

    for x, y, label in stage_desc:
        ax.text(x, y, label, fontsize=8, rotation=90, va='bottom')

    # Key statistics box (right side)
    stats_text = '\n'.join([
        'Key Statistics:',
        '',
        'Compression: 40%',
        'Fidelity: ≥80%',
        'Architectures: 4+',
        'Total runs: 21',
        'Ships tested: 42+',
        'Chi-square p: 4.8×10⁻⁵',
    ])

    props = dict(boxstyle='round', facecolor='wheat', alpha=0.9)
    ax.text(9.8, 8, stats_text, fontsize=9, va='top', ha='right',
           bbox=props, family='monospace')

    plt.tight_layout()
    return fig


if __name__ == '__main__':
    fig = create_figure()

    # Save in multiple formats
    fig.savefig('fig3_pipeline.png', dpi=300, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    fig.savefig('fig3_pipeline.pdf', bbox_inches='tight',
                facecolor='white', edgecolor='none')

    print("Figure 3 saved: fig3_pipeline.png, .pdf")
    plt.show()
