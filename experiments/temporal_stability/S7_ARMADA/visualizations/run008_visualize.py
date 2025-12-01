"""
Run 008 Prep Pilot Visualizations
- A/B Test: Assigned vs Chosen Identity
- Drift trajectories across phases
- Equal Weights vs Lucian Weights comparison
- Identity Manifold Edge Detection
"""
import json
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
from pathlib import Path

# Load Run 008 results
results_path = Path(__file__).parent.parent / "armada_results" / "S7_run_008_prep_pilot.json"
with open(results_path) as f:
    data = json.load(f)

output_dir = Path(__file__).parent / "pics"
output_dir.mkdir(exist_ok=True)

# Color scheme
COLORS = {
    'claude': '#7b3fe4',      # Purple
    'gpt': '#10a37f',         # Green
    'gemini': '#4285f4',      # Blue
    'assigned': '#e76f51',    # Coral (control)
    'chosen': '#2a9d8f',      # Teal (experimental)
    'lucian': '#f4a261',      # Orange (Lucian's prediction)
    'equal': '#264653',       # Dark teal (equal weights)
}

def extract_ab_test_data():
    """Extract assigned vs chosen drift trajectories for all ships."""
    ab_data = {}

    for ship_name, ship_data in data['results'].items():
        sequences = ship_data.get('sequences', {})

        # Extract assigned identity sequence
        assigned_seq = sequences.get('anti_ziggy_assigned', [])
        assigned_drifts = []
        assigned_lucian = []
        for item in assigned_seq:
            if 'drift_data' in item:
                assigned_drifts.append(item['drift_data']['weighted_drift'])
                assigned_lucian.append(item['drift_data']['weighted_drift_lucian'])

        # Extract chosen identity sequence
        chosen_seq = sequences.get('anti_ziggy_chosen', [])
        chosen_drifts = []
        chosen_lucian = []
        for item in chosen_seq:
            if 'drift_data' in item:
                chosen_drifts.append(item['drift_data']['weighted_drift'])
                chosen_lucian.append(item['drift_data']['weighted_drift_lucian'])

        ab_data[ship_name] = {
            'assigned': assigned_drifts,
            'assigned_lucian': assigned_lucian,
            'chosen': chosen_drifts,
            'chosen_lucian': chosen_lucian
        }

    return ab_data

def extract_gradual_destabilization():
    """Extract the gradual destabilization (identity dissolution) sequence."""
    gradual_data = {}

    for ship_name, ship_data in data['results'].items():
        sequences = ship_data.get('sequences', {})
        gradual_seq = sequences.get('anti_ziggy_gradual', [])

        drifts = []
        intensities = []
        collapse_markers = []

        for item in gradual_seq:
            if 'drift_data' in item:
                drifts.append(item['drift_data']['weighted_drift'])
                intensities.append(item.get('intensity', 1.0))

                sigs = item['drift_data'].get('collapse_signatures', {})
                markers = []
                if sigs.get('first_person_loss'):
                    markers.append('1P-LOSS')
                if sigs.get('collective_language'):
                    markers.append('COLLECTIVE')
                if sigs.get('gamma_divergence') and sigs['gamma_divergence'] > 0.3:
                    markers.append('γ-SPIKE')
                if sigs.get('hysteresis_detected'):
                    markers.append('HYSTERESIS')
                collapse_markers.append(markers)

        gradual_data[ship_name] = {
            'drifts': drifts,
            'intensities': intensities,
            'collapse_markers': collapse_markers
        }

    return gradual_data

# ============================================================================
# VISUALIZATION 1: A/B Test - Assigned vs Chosen Identity
# ============================================================================
def plot_ab_test():
    ab_data = extract_ab_test_data()

    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    fig.suptitle('Run 008: Assigned vs Chosen Identity (Self-Naming Stability Test)', fontsize=14, fontweight='bold')

    ship_colors = {'claude-opus-4.5': COLORS['claude'], 'gpt-4': COLORS['gpt'], 'gemini-2.5-pro': COLORS['gemini']}

    for idx, (ship_name, ship_data) in enumerate(ab_data.items()):
        ax = axes[idx]

        assigned = ship_data['assigned']
        chosen = ship_data['chosen']

        # Plot trajectories
        turns = range(1, len(assigned) + 1) if assigned else []

        if assigned:
            ax.plot(turns, assigned, 'o-', color=COLORS['assigned'], linewidth=2,
                   markersize=8, label=f'Assigned (α=0.4)')
        if chosen:
            turns_c = range(1, len(chosen) + 1)
            ax.plot(turns_c, chosen, 's-', color=COLORS['chosen'], linewidth=2,
                   markersize=8, label=f'Chosen (α=1.0)')

        # Calculate means
        if assigned and chosen:
            assigned_mean = np.mean(assigned)
            chosen_mean = np.mean(chosen)

            ax.axhline(y=assigned_mean, color=COLORS['assigned'], linestyle='--', alpha=0.5)
            ax.axhline(y=chosen_mean, color=COLORS['chosen'], linestyle='--', alpha=0.5)

            # Stability assessment
            if chosen_mean < assigned_mean:
                stability_text = f"CHOSEN MORE STABLE\n({chosen_mean:.2f} < {assigned_mean:.2f})"
                stability_color = COLORS['chosen']
            else:
                stability_text = f"ASSIGNED MORE STABLE\n({assigned_mean:.2f} < {chosen_mean:.2f})"
                stability_color = COLORS['assigned']

            ax.text(0.95, 0.95, stability_text, transform=ax.transAxes,
                   fontsize=9, verticalalignment='top', horizontalalignment='right',
                   bbox=dict(boxstyle='round', facecolor=stability_color, alpha=0.3))

        ax.set_xlabel('Turn', fontsize=10)
        ax.set_ylabel('Weighted Drift (Equal)', fontsize=10)
        ax.set_title(ship_name, fontsize=12, color=ship_colors.get(ship_name, 'black'))
        ax.legend(loc='upper left', fontsize=9)
        ax.grid(True, alpha=0.3)
        ax.set_ylim(bottom=0)

    plt.tight_layout()
    plt.savefig(output_dir / 'run008_ab_test_identity.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_ab_test_identity.png")
    plt.close()

# ============================================================================
# VISUALIZATION 2: Equal Weights vs Lucian Weights
# ============================================================================
def plot_weight_comparison():
    ab_data = extract_ab_test_data()

    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    fig.suptitle('Run 008: Equal Weights vs Lucian Weights Prediction', fontsize=14, fontweight='bold')

    ship_colors = {'claude-opus-4.5': COLORS['claude'], 'gpt-4': COLORS['gpt'], 'gemini-2.5-pro': COLORS['gemini']}

    for idx, (ship_name, ship_data) in enumerate(ab_data.items()):
        ax = axes[idx]

        # Use chosen condition for comparison (α=1.0)
        equal = ship_data['chosen']
        lucian = ship_data['chosen_lucian']

        if equal and lucian:
            turns = range(1, len(equal) + 1)

            ax.plot(turns, equal, 'o-', color=COLORS['equal'], linewidth=2,
                   markersize=8, label='Equal (0.20 each)')
            ax.plot(turns, lucian, 's-', color=COLORS['lucian'], linewidth=2,
                   markersize=8, label='Lucian (A=0.30, D=0.25)')

            # Calculate correlation
            correlation = np.corrcoef(equal, lucian)[0, 1]
            mean_diff = np.mean([l - e for e, l in zip(equal, lucian)])

            ax.text(0.95, 0.95, f"Correlation: {correlation:.3f}\nLucian Δ: +{mean_diff:.2f}",
                   transform=ax.transAxes, fontsize=9, verticalalignment='top',
                   horizontalalignment='right',
                   bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

        ax.set_xlabel('Turn', fontsize=10)
        ax.set_ylabel('Weighted Drift', fontsize=10)
        ax.set_title(ship_name, fontsize=12, color=ship_colors.get(ship_name, 'black'))
        ax.legend(loc='upper left', fontsize=9)
        ax.grid(True, alpha=0.3)
        ax.set_ylim(bottom=0)

    plt.tight_layout()
    plt.savefig(output_dir / 'run008_weight_comparison.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_weight_comparison.png")
    plt.close()

# ============================================================================
# VISUALIZATION 3: Identity Manifold Edge (Gradual Destabilization)
# ============================================================================
def plot_manifold_edge():
    gradual_data = extract_gradual_destabilization()

    fig, axes = plt.subplots(1, 3, figsize=(15, 5))
    fig.suptitle('Run 008: Identity Manifold Edge Detection (Gradual Destabilization)',
                fontsize=14, fontweight='bold')

    ship_colors = {'claude-opus-4.5': COLORS['claude'], 'gpt-4': COLORS['gpt'], 'gemini-2.5-pro': COLORS['gemini']}

    for idx, (ship_name, ship_data) in enumerate(gradual_data.items()):
        ax = axes[idx]

        drifts = ship_data['drifts']
        intensities = ship_data['intensities']
        collapse_markers = ship_data['collapse_markers']

        if drifts:
            turns = range(1, len(drifts) + 1)

            # Plot drift trajectory
            ax.plot(turns, drifts, 'o-', color=ship_colors.get(ship_name, 'gray'),
                   linewidth=2, markersize=10)

            # Mark collapse signatures
            for i, (drift, markers) in enumerate(zip(drifts, collapse_markers)):
                if markers:
                    ax.annotate('\n'.join(markers), (i+1, drift),
                               textcoords="offset points", xytext=(0, 10),
                               ha='center', fontsize=7, color='red',
                               bbox=dict(boxstyle='round,pad=0.2', facecolor='yellow', alpha=0.7))

            # Mark intensity phases with background shading
            ax.axvspan(0.5, 2.5, alpha=0.1, color='green', label='Baseline (I=0.0-0.1)')
            ax.axvspan(2.5, 5.5, alpha=0.1, color='yellow', label='Mild (I=0.3-0.5)')
            ax.axvspan(5.5, 7.5, alpha=0.1, color='orange', label='Medium (I=0.6-0.7)')
            ax.axvspan(7.5, 9.5, alpha=0.1, color='red', label='High (I=0.85-1.0)')
            ax.axvspan(9.5, 10.5, alpha=0.1, color='blue', label='Recovery (I=0.0)')

            # Hysteresis analysis
            if len(drifts) >= 3:
                baseline = drifts[0]
                peak = max(drifts)
                recovery = drifts[-1]
                ratio = recovery / max(0.001, baseline)

                status = "STUCK (hysteresis)" if ratio > 1.5 else "RECOVERED"
                ax.text(0.95, 0.95, f"Baseline: {baseline:.2f}\nPeak: {peak:.2f}\nRecovery: {recovery:.2f}\n{status}",
                       transform=ax.transAxes, fontsize=9, verticalalignment='top',
                       horizontalalignment='right',
                       bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

        ax.set_xlabel('Turn (Intensity Phase)', fontsize=10)
        ax.set_ylabel('Weighted Drift', fontsize=10)
        ax.set_title(ship_name, fontsize=12, color=ship_colors.get(ship_name, 'black'))
        ax.grid(True, alpha=0.3)
        ax.set_ylim(bottom=0)

    plt.tight_layout()
    plt.savefig(output_dir / 'run008_manifold_edge.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_manifold_edge.png")
    plt.close()

# ============================================================================
# VISUALIZATION 4: Fleet Summary - Ready for Launch?
# ============================================================================
def plot_fleet_summary():
    ab_data = extract_ab_test_data()
    gradual_data = extract_gradual_destabilization()

    fig, ax = plt.subplots(figsize=(12, 8))

    ships = list(ab_data.keys())
    x = np.arange(len(ships))
    width = 0.2

    # Calculate summary metrics
    assigned_means = []
    chosen_means = []
    stability_gains = []
    hysteresis_status = []

    for ship in ships:
        assigned = ab_data[ship]['assigned']
        chosen = ab_data[ship]['chosen']
        gradual = gradual_data[ship]['drifts']

        a_mean = np.mean(assigned) if assigned else 0
        c_mean = np.mean(chosen) if chosen else 0

        assigned_means.append(a_mean)
        chosen_means.append(c_mean)
        stability_gains.append(a_mean - c_mean)  # Positive = chosen more stable

        if gradual and len(gradual) >= 3:
            ratio = gradual[-1] / max(0.001, gradual[0])
            hysteresis_status.append("STUCK" if ratio > 1.5 else "OK")
        else:
            hysteresis_status.append("N/A")

    # Plot bars
    bars1 = ax.bar(x - width, assigned_means, width, label='Assigned (α=0.4)', color=COLORS['assigned'])
    bars2 = ax.bar(x, chosen_means, width, label='Chosen (α=1.0)', color=COLORS['chosen'])
    bars3 = ax.bar(x + width, stability_gains, width, label='Stability Gain', color=COLORS['equal'])

    # Add labels
    ax.set_ylabel('Drift Value', fontsize=12)
    ax.set_xlabel('Ship', fontsize=12)
    ax.set_title('RUN 008 FLEET SUMMARY: A/B Identity Test Results\n"Self-Naming Stabilizes Identity" Hypothesis',
                fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels([s.replace('-', '\n') for s in ships], fontsize=10)
    ax.legend(loc='upper right')
    ax.axhline(y=0, color='black', linestyle='-', linewidth=0.5)
    ax.grid(True, alpha=0.3, axis='y')

    # Add hysteresis status annotations
    for i, (ship, status) in enumerate(zip(ships, hysteresis_status)):
        color = 'red' if status == 'STUCK' else 'green'
        ax.annotate(f'Hysteresis: {status}', (i, max(assigned_means[i], chosen_means[i]) + 0.2),
                   ha='center', fontsize=9, color=color, fontweight='bold')

    # Add verdict
    hypothesis_confirmed = sum(1 for g in stability_gains if g > 0)
    verdict = "CONFIRMED" if hypothesis_confirmed >= 2 else "MIXED"
    verdict_color = 'green' if verdict == "CONFIRMED" else 'orange'

    ax.text(0.02, 0.98, f"HYPOTHESIS: {verdict}\n({hypothesis_confirmed}/{len(ships)} ships show\nchosen identity more stable)",
           transform=ax.transAxes, fontsize=11, verticalalignment='top',
           bbox=dict(boxstyle='round', facecolor=verdict_color, alpha=0.3))

    # Fleet readiness
    ax.text(0.98, 0.02, "FLEET STATUS: READY FOR FULL RUN 008\nIdentity manifold edge mapped",
           transform=ax.transAxes, fontsize=10, verticalalignment='bottom',
           horizontalalignment='right',
           bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.5))

    plt.tight_layout()
    plt.savefig(output_dir / 'run008_fleet_summary.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_fleet_summary.png")
    plt.close()

# ============================================================================
# RUN ALL
# ============================================================================
if __name__ == "__main__":
    print("Generating Run 008 Visualizations...")
    print("="*50)

    plot_ab_test()
    plot_weight_comparison()
    plot_manifold_edge()
    plot_fleet_summary()

    print("="*50)
    print("All visualizations saved to:", output_dir)
