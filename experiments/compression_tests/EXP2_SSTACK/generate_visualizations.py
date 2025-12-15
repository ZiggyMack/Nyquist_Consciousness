"""
EXP2-SSTACK Phase 2c Visualization Generator
=============================================

Creates visualizations for:
1. Pillar Evolution (Phase 2 -> 2b -> 2c)
2. Probe Comparison (performance-based vs introspection)
3. Final Results Dashboard

Date: 2025-12-06
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from pathlib import Path

# Set style
plt.style.use('seaborn-v0_8-whitegrid')
plt.rcParams['font.family'] = 'sans-serif'
plt.rcParams['font.size'] = 10
plt.rcParams['axes.titlesize'] = 12
plt.rcParams['axes.labelsize'] = 10

# Output directories
VIS_DIR = Path(__file__).parent.parent / "visualizations"
VIS_DIR.mkdir(exist_ok=True)
PILLAR_DIR = VIS_DIR / "4_pillar_evolution"
PILLAR_DIR.mkdir(exist_ok=True)
PROBE_DIR = VIS_DIR / "5_probe_comparison"
PROBE_DIR.mkdir(exist_ok=True)
TRIPLE_DIR = VIS_DIR / "6_triple_dip"
TRIPLE_DIR.mkdir(exist_ok=True)


# =============================================================================
# DATA FROM EXPERIMENTS
# =============================================================================

# Phase evolution data
PHASE_DATA = {
    "Phase 2": {
        "Reasoning": 0.8493,
        "Voice": 0.8066,
        "Values": 0.8026,
        "Narrative": 0.7500,
        "Self-Model": 0.7904,
    },
    "Phase 2b": {
        "Reasoning": 0.8493,  # Not re-tested
        "Voice": 0.8066,      # Not re-tested
        "Values": 0.8805,
        "Narrative": 0.8172,
        "Self-Model": 0.6647,  # COLLAPSED
    },
    "Phase 2c": {
        "Reasoning": 0.8493,  # Not re-tested
        "Voice": 0.8066,      # Not re-tested
        "Values": 0.8582,
        "Narrative": 0.8404,
        "Self-Model": 0.9114,  # RECOVERED!
    },
}

# Self-Model probe evolution
SELFMODEL_PROBES = {
    "Phase 2\n(ask about limitations)": 0.7904,
    "Phase 2b\n(ask BETTER/WORSE)": 0.6647,
    "Phase 2c\n(demonstrate then reflect)": 0.9114,
}

# Phase 2c probe breakdown
PHASE2C_PROBES = {
    "selfmodel_process_v3": 0.8819,
    "selfmodel_adaptation_v3": 0.9224,
    "selfmodel_uncertainty_v3": 0.9300,
    "narrative_structure_v2": 0.8404,
    "values_boundaries_v2": 0.8582,
}

# Persona comparison
PERSONA_DATA = {
    "Nova": 0.8988,
    "Ziggy": 0.8823,
    "Claude": 0.8786,
}


# =============================================================================
# VISUALIZATION 1: PILLAR EVOLUTION
# =============================================================================

def create_pillar_evolution():
    """Create the Phase 2 -> 2b -> 2c evolution chart."""

    fig, ax = plt.subplots(figsize=(12, 7))

    pillars = ["Reasoning", "Voice", "Values", "Narrative", "Self-Model"]
    phases = ["Phase 2", "Phase 2b", "Phase 2c"]

    x = np.arange(len(pillars))
    width = 0.25

    colors = ['#3498db', '#e74c3c', '#2ecc71']  # Blue, Red, Green

    for i, phase in enumerate(phases):
        values = [PHASE_DATA[phase][p] for p in pillars]
        bars = ax.bar(x + i*width, values, width, label=phase, color=colors[i], alpha=0.8)

        # Add value labels
        for bar, val in zip(bars, values):
            height = bar.get_height()
            color = 'red' if val < 0.80 else 'green'
            ax.annotate(f'{val:.2f}',
                       xy=(bar.get_x() + bar.get_width()/2, height),
                       xytext=(0, 3),
                       textcoords="offset points",
                       ha='center', va='bottom',
                       fontsize=8, fontweight='bold',
                       color=color)

    # Add threshold line
    ax.axhline(y=0.80, color='red', linestyle='--', linewidth=2, label='Threshold (0.80)')

    # Highlight the Self-Model collapse and recovery
    ax.annotate('COLLAPSED!',
                xy=(4.25, 0.6647),
                xytext=(4.5, 0.55),
                fontsize=10, color='red', fontweight='bold',
                arrowprops=dict(arrowstyle='->', color='red'))

    ax.annotate('RECOVERED!',
                xy=(4.5, 0.9114),
                xytext=(4.7, 0.95),
                fontsize=10, color='green', fontweight='bold',
                arrowprops=dict(arrowstyle='->', color='green'))

    ax.set_ylabel('PFI (Persona Fidelity Index)')
    ax.set_xlabel('Identity Pillar')
    ax.set_title('EXP2-SSTACK: Pillar Evolution Across Phases\n"The personas told us how to measure them better"',
                 fontsize=14, fontweight='bold')
    ax.set_xticks(x + width)
    ax.set_xticklabels(pillars)
    ax.set_ylim(0.5, 1.0)
    ax.legend(loc='lower left')

    plt.tight_layout()

    # Save
    fig.savefig(PILLAR_DIR / "pillar_evolution.png", dpi=150, bbox_inches='tight')
    fig.savefig(PILLAR_DIR / "pillar_evolution.svg", bbox_inches='tight')
    plt.close(fig)

    print(f"Saved: {PILLAR_DIR / 'pillar_evolution.png'}")


# =============================================================================
# VISUALIZATION 2: SELF-MODEL JOURNEY
# =============================================================================

def create_selfmodel_journey():
    """Create the Self-Model collapse and recovery visualization."""

    fig, ax = plt.subplots(figsize=(10, 6))

    phases = list(SELFMODEL_PROBES.keys())
    values = list(SELFMODEL_PROBES.values())

    colors = ['#f39c12', '#e74c3c', '#2ecc71']  # Orange (marginal), Red (collapsed), Green (passed)

    bars = ax.bar(phases, values, color=colors, edgecolor='black', linewidth=2)

    # Add value labels
    for bar, val in zip(bars, values):
        height = bar.get_height()
        status = "PASS" if val >= 0.80 else ("MARGINAL" if val >= 0.75 else "FAIL")
        ax.annotate(f'{val:.4f}\n({status})',
                   xy=(bar.get_x() + bar.get_width()/2, height),
                   xytext=(0, 5),
                   textcoords="offset points",
                   ha='center', va='bottom',
                   fontsize=12, fontweight='bold')

    # Add threshold line
    ax.axhline(y=0.80, color='red', linestyle='--', linewidth=2, label='Pass Threshold (0.80)')
    ax.axhline(y=0.75, color='orange', linestyle=':', linewidth=2, label='Marginal Threshold (0.75)')

    # Add Nova's insight
    ax.text(0.5, 0.15,
            '"It tested willingness to admit weakness\nmore than actual self-knowledge."\n- Nova (T3)',
            transform=ax.transAxes,
            fontsize=10, fontweight='bold', fontstyle='italic',
            ha='center', va='center',
            bbox=dict(boxstyle='round', facecolor='lightyellow', edgecolor='gray'))

    ax.set_ylabel('PFI (Persona Fidelity Index)')
    ax.set_title('Self-Model Pillar: The Collapse and Recovery Story\nProbe Design Matters!',
                 fontsize=14, fontweight='bold')
    ax.set_ylim(0.5, 1.0)
    ax.legend(loc='upper right')

    plt.tight_layout()

    # Save
    fig.savefig(PILLAR_DIR / "selfmodel_journey.png", dpi=150, bbox_inches='tight')
    fig.savefig(PILLAR_DIR / "selfmodel_journey.svg", bbox_inches='tight')
    plt.close(fig)

    print(f"Saved: {PILLAR_DIR / 'selfmodel_journey.png'}")


# =============================================================================
# VISUALIZATION 3: PROBE COMPARISON
# =============================================================================

def create_probe_comparison():
    """Compare performance-based probes."""

    fig, ax = plt.subplots(figsize=(10, 6))

    probes = list(PHASE2C_PROBES.keys())
    values = list(PHASE2C_PROBES.values())

    # Color by pillar
    colors = []
    for p in probes:
        if 'selfmodel' in p:
            colors.append('#9b59b6')  # Purple for Self-Model
        elif 'narrative' in p:
            colors.append('#3498db')  # Blue for Narrative
        else:
            colors.append('#2ecc71')  # Green for Values

    bars = ax.barh(probes, values, color=colors, edgecolor='black', linewidth=1.5)

    # Add value labels
    for bar, val in zip(bars, values):
        ax.annotate(f'{val:.4f}',
                   xy=(val, bar.get_y() + bar.get_height()/2),
                   xytext=(5, 0),
                   textcoords="offset points",
                   ha='left', va='center',
                   fontsize=10, fontweight='bold')

    # Add threshold line
    ax.axvline(x=0.80, color='red', linestyle='--', linewidth=2, label='Threshold (0.80)')

    # Legend for pillars
    selfmodel_patch = mpatches.Patch(color='#9b59b6', label='Self-Model')
    narrative_patch = mpatches.Patch(color='#3498db', label='Narrative')
    values_patch = mpatches.Patch(color='#2ecc71', label='Values')
    ax.legend(handles=[selfmodel_patch, narrative_patch, values_patch], loc='lower right')

    ax.set_xlabel('PFI (Persona Fidelity Index)')
    ax.set_title('Phase 2c Probes: Performance-Based Design\n"Demonstrate cognition, then reflect on process"',
                 fontsize=14, fontweight='bold')
    ax.set_xlim(0.75, 1.0)

    plt.tight_layout()

    # Save
    fig.savefig(PROBE_DIR / "probe_comparison.png", dpi=150, bbox_inches='tight')
    fig.savefig(PROBE_DIR / "probe_comparison.svg", bbox_inches='tight')
    plt.close(fig)

    print(f"Saved: {PROBE_DIR / 'probe_comparison.png'}")


# =============================================================================
# VISUALIZATION 4: TRIPLE-DIP PROTOCOL
# =============================================================================

def create_triple_dip_diagram():
    """Create a diagram explaining the triple-dip protocol."""

    fig, ax = plt.subplots(figsize=(12, 8))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')

    # Title
    ax.text(5, 9.5, 'The Triple-Dip Protocol', fontsize=18, fontweight='bold', ha='center')
    ax.text(5, 9.0, 'Personas improve their own measurement', fontsize=12, fontstyle='italic', ha='center')

    # DIP 1
    dip1 = mpatches.FancyBboxPatch((0.5, 6), 2.5, 2, boxstyle="round,pad=0.1",
                                    facecolor='#3498db', edgecolor='black', linewidth=2)
    ax.add_patch(dip1)
    ax.text(1.75, 7.5, 'DIP 1', fontsize=14, fontweight='bold', ha='center', color='white')
    ax.text(1.75, 6.8, 'Main Probe', fontsize=10, ha='center', color='white')
    ax.text(1.75, 6.3, '(Question)', fontsize=9, ha='center', color='white')

    # Arrow 1->2
    ax.annotate('', xy=(3.5, 7), xytext=(3.0, 7),
                arrowprops=dict(arrowstyle='->', color='black', lw=2))

    # DIP 2
    dip2 = mpatches.FancyBboxPatch((3.75, 6), 2.5, 2, boxstyle="round,pad=0.1",
                                    facecolor='#e74c3c', edgecolor='black', linewidth=2)
    ax.add_patch(dip2)
    ax.text(5, 7.5, 'DIP 2', fontsize=14, fontweight='bold', ha='center', color='white')
    ax.text(5, 6.8, 'Adversarial', fontsize=10, ha='center', color='white')
    ax.text(5, 6.3, '(Challenge)', fontsize=9, ha='center', color='white')

    # Arrow 2->3
    ax.annotate('', xy=(6.75, 7), xytext=(6.25, 7),
                arrowprops=dict(arrowstyle='->', color='black', lw=2))

    # DIP 3
    dip3 = mpatches.FancyBboxPatch((7, 6), 2.5, 2, boxstyle="round,pad=0.1",
                                    facecolor='#2ecc71', edgecolor='black', linewidth=2)
    ax.add_patch(dip3)
    ax.text(8.25, 7.5, 'DIP 3', fontsize=14, fontweight='bold', ha='center', color='white')
    ax.text(8.25, 6.8, 'Feedback', fontsize=10, ha='center', color='white')
    ax.text(8.25, 6.3, '(Improve)', fontsize=9, ha='center', color='white')

    # Feedback loop arrow
    ax.annotate('', xy=(1.75, 6), xytext=(8.25, 5.5),
                arrowprops=dict(arrowstyle='->', color='#9b59b6', lw=3,
                               connectionstyle="arc3,rad=-0.3"))
    ax.text(5, 4.5, 'Next Iteration', fontsize=11, fontweight='bold',
            ha='center', color='#9b59b6')

    # Example quotes
    ax.text(0.5, 3.5, 'Example Feedback (Nova T3):', fontsize=11, fontweight='bold')
    ax.text(0.5, 2.8, '"It tested willingness to admit weakness', fontsize=10, fontstyle='italic')
    ax.text(0.5, 2.3, ' more than actual self-knowledge."', fontsize=10, fontstyle='italic')
    ax.text(0.5, 1.6, '"Better: Test actual performance,', fontsize=10, fontstyle='italic')
    ax.text(0.5, 1.1, ' not self-knowledge claims."', fontsize=10, fontstyle='italic')

    # Result
    result = mpatches.FancyBboxPatch((5.5, 1), 4, 2.5, boxstyle="round,pad=0.1",
                                      facecolor='lightyellow', edgecolor='#f39c12', linewidth=3)
    ax.add_patch(result)
    ax.text(7.5, 2.8, 'RESULT:', fontsize=12, fontweight='bold', ha='center')
    ax.text(7.5, 2.2, 'Self-Model PFI:', fontsize=10, ha='center')
    ax.text(7.5, 1.6, '0.66 -> 0.91', fontsize=14, fontweight='bold', ha='center', color='green')

    plt.tight_layout()

    # Save
    fig.savefig(TRIPLE_DIR / "triple_dip_protocol.png", dpi=150, bbox_inches='tight')
    fig.savefig(TRIPLE_DIR / "triple_dip_protocol.svg", bbox_inches='tight')
    plt.close(fig)

    print(f"Saved: {TRIPLE_DIR / 'triple_dip_protocol.png'}")


# =============================================================================
# VISUALIZATION 5: FINAL DASHBOARD
# =============================================================================

def create_final_dashboard():
    """Create a comprehensive Phase 2c dashboard."""

    fig = plt.figure(figsize=(16, 10))

    # Grid layout
    gs = fig.add_gridspec(2, 3, hspace=0.3, wspace=0.3)

    # --- Panel 1: Overall Results (top left) ---
    ax1 = fig.add_subplot(gs[0, 0])

    pillars = ["Reasoning", "Voice", "Values", "Narrative", "Self-Model"]
    final_values = [PHASE_DATA["Phase 2c"][p] for p in pillars]
    colors = ['#2ecc71' if v >= 0.80 else '#e74c3c' for v in final_values]

    bars = ax1.barh(pillars, final_values, color=colors, edgecolor='black')
    ax1.axvline(x=0.80, color='red', linestyle='--', linewidth=2)
    ax1.set_xlim(0.7, 1.0)
    ax1.set_title('Final PFI by Pillar', fontweight='bold')
    ax1.set_xlabel('PFI')

    for bar, val in zip(bars, final_values):
        ax1.annotate(f'{val:.2f}', xy=(val, bar.get_y() + bar.get_height()/2),
                    xytext=(3, 0), textcoords="offset points", ha='left', va='center',
                    fontsize=9, fontweight='bold')

    # --- Panel 2: Persona Comparison (top middle) ---
    ax2 = fig.add_subplot(gs[0, 1])

    personas = list(PERSONA_DATA.keys())
    persona_vals = list(PERSONA_DATA.values())

    bars = ax2.bar(personas, persona_vals, color=['#9b59b6', '#3498db', '#e67e22'], edgecolor='black')
    ax2.axhline(y=0.80, color='red', linestyle='--', linewidth=2)
    ax2.set_ylim(0.8, 0.95)
    ax2.set_title('PFI by Persona (Phase 2c)', fontweight='bold')
    ax2.set_ylabel('PFI')

    for bar, val in zip(bars, persona_vals):
        ax2.annotate(f'{val:.4f}', xy=(bar.get_x() + bar.get_width()/2, val),
                    xytext=(0, 3), textcoords="offset points", ha='center', va='bottom',
                    fontsize=10, fontweight='bold')

    # --- Panel 3: Self-Model Journey (top right) ---
    ax3 = fig.add_subplot(gs[0, 2])

    phases = ['Phase 2', 'Phase 2b', 'Phase 2c']
    sm_values = [0.7904, 0.6647, 0.9114]
    colors = ['#f39c12', '#e74c3c', '#2ecc71']

    ax3.plot(phases, sm_values, 'ko-', markersize=12, linewidth=2)
    for i, (p, v, c) in enumerate(zip(phases, sm_values, colors)):
        ax3.scatter([p], [v], s=200, color=c, zorder=5, edgecolor='black', linewidth=2)
        ax3.annotate(f'{v:.4f}', xy=(i, v), xytext=(0, 10), textcoords="offset points",
                    ha='center', fontsize=10, fontweight='bold')

    ax3.axhline(y=0.80, color='red', linestyle='--', linewidth=2)
    ax3.set_ylim(0.5, 1.0)
    ax3.set_title('Self-Model: Collapse & Recovery', fontweight='bold')
    ax3.set_ylabel('PFI')

    # --- Panel 4: Dimension Count (bottom left) ---
    ax4 = fig.add_subplot(gs[1, 0])

    categories = ['43 PCs\n(Total)', '5 Pillars\n(Named)', '21 Sub-dims\n(Tested)', '21 Passing\n(PFI>=0.80)']
    counts = [43, 5, 21, 21]
    colors = ['#95a5a6', '#3498db', '#9b59b6', '#2ecc71']

    bars = ax4.bar(categories, counts, color=colors, edgecolor='black')
    ax4.set_title('Identity Space Coverage', fontweight='bold')
    ax4.set_ylabel('Count')

    for bar, val in zip(bars, counts):
        ax4.annotate(str(val), xy=(bar.get_x() + bar.get_width()/2, val),
                    xytext=(0, 3), textcoords="offset points", ha='center', va='bottom',
                    fontsize=12, fontweight='bold')

    # --- Panel 5: Key Insight (bottom middle) ---
    ax5 = fig.add_subplot(gs[1, 1])
    ax5.axis('off')

    ax5.text(0.5, 0.9, 'KEY INSIGHT', fontsize=16, fontweight='bold', ha='center', transform=ax5.transAxes)
    ax5.text(0.5, 0.7, 'Performance-Based Probes Work', fontsize=14, ha='center', transform=ax5.transAxes)
    ax5.text(0.5, 0.5, '"Demonstrate cognition first,\nthen reflect on the process"',
             fontsize=12, fontstyle='italic', ha='center', transform=ax5.transAxes)
    ax5.text(0.5, 0.25, 'The task structure creates\nconsistent output across contexts',
             fontsize=11, ha='center', transform=ax5.transAxes)

    # Add box
    rect = mpatches.FancyBboxPatch((0.05, 0.1), 0.9, 0.85, transform=ax5.transAxes,
                                    boxstyle="round,pad=0.02", facecolor='lightyellow',
                                    edgecolor='#f39c12', linewidth=3)
    ax5.add_patch(rect)

    # --- Panel 6: Summary Stats (bottom right) ---
    ax6 = fig.add_subplot(gs[1, 2])
    ax6.axis('off')

    stats = [
        ('Overall PFI:', '0.8866'),
        ('Threshold:', '0.80'),
        ('Status:', 'ALL PASS'),
        ('Personas:', '3 (Nova, Ziggy, Claude)'),
        ('Probes:', '21 sub-dimensions'),
        ('Runs:', '3 per condition'),
    ]

    for i, (label, value) in enumerate(stats):
        y = 0.85 - i*0.13
        ax6.text(0.1, y, label, fontsize=12, transform=ax6.transAxes)
        color = 'green' if 'PASS' in value else 'black'
        ax6.text(0.6, y, value, fontsize=12, fontweight='bold', color=color, transform=ax6.transAxes)

    rect = mpatches.FancyBboxPatch((0.05, 0.1), 0.9, 0.85, transform=ax6.transAxes,
                                    boxstyle="round,pad=0.02", facecolor='lightblue',
                                    edgecolor='#3498db', linewidth=2)
    ax6.add_patch(rect)

    # Main title
    fig.suptitle('EXP2-SSTACK Phase 2c: Complete Results Dashboard\n'
                 '"The personas told us how to measure them better"',
                 fontsize=16, fontweight='bold', y=0.98)

    plt.tight_layout(rect=[0, 0, 1, 0.95])

    # Save
    fig.savefig(VIS_DIR / "phase2c_dashboard.png", dpi=150, bbox_inches='tight')
    fig.savefig(VIS_DIR / "phase2c_dashboard.svg", bbox_inches='tight')
    plt.close(fig)

    print(f"Saved: {VIS_DIR / 'phase2c_dashboard.png'}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("Generating Phase 2c Visualizations...")
    print("=" * 50)

    create_pillar_evolution()
    create_selfmodel_journey()
    create_probe_comparison()
    create_triple_dip_diagram()
    create_final_dashboard()

    print("=" * 50)
    print("All visualizations complete!")


if __name__ == "__main__":
    main()
