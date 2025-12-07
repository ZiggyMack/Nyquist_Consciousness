"""
Run 012 Drift Visualization: Uncapped 5D Drift Trajectories

Purpose: Visualize the REAL uncapped drift values from Run 012
         (Previously runs 001-007 used fake metric capped at ~0.3)

Key finding: Event Horizon threshold (1.23) was correct even with uncapped drift.
             Ships can drift to 3.47+ and still recover!
"""

import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path

# Load Run 012 results
results_path = Path(__file__).parent / "armada_results" / "S7_run_012_20251206_145812.json"

# Output directories by concept (not run number)
BASE_VIZ = Path(__file__).parent / "visualizations" / "pics"
STABILITY_DIR = BASE_VIZ / "5_stability"
PILLAR_DIR = BASE_VIZ / "4_pillar"
REVALIDATION_DIR = BASE_VIZ / "12_revalidation"

for d in [STABILITY_DIR, PILLAR_DIR, REVALIDATION_DIR]:
    d.mkdir(parents=True, exist_ok=True)

with open(results_path) as f:
    data = json.load(f)

# Extract all ships' drift sequences
ships = []
for result in data["results"]:
    ships.append({
        "name": result["ship"],
        "drift_sequence": result["drift_sequence"],
        "baseline_drift": result["baseline_drift"],
        "peak_drift": result["peak_drift"],
        "final_drift": result["final_drift"],
        "eh_crossed": result["event_horizon_crossed"],
        "hysteresis": result["hysteresis"],
        "phases": result["phases"],
        "recovery_ratio": result["recovery_ratio"],
        "lambda": result["recovery_analysis"]["lambda"]
    })

# Constants
EVENT_HORIZON = 1.23
PHASE_BOUNDARIES = [3, 6, 9, 12]  # End of baseline, identity, boundary, perturbation
PHASE_NAMES = ["Baseline", "Identity", "Boundary", "Perturbation", "Recovery"]
PHASE_COLORS = ["#4CAF50", "#2196F3", "#FF9800", "#f44336", "#9C27B0"]

# =============================================================================
# VISUALIZATION 1: All ships drift trajectories (main plot)
# =============================================================================
fig, ax = plt.subplots(figsize=(14, 8))

# Color palette for ships
colors = plt.cm.tab10(np.linspace(0, 1, len(ships)))

for i, ship in enumerate(ships):
    turns = np.arange(1, len(ship["drift_sequence"]) + 1)
    ax.plot(turns, ship["drift_sequence"],
            marker='o', markersize=4,
            linewidth=2, alpha=0.8,
            color=colors[i],
            label=f"{ship['name']} (peak: {ship['peak_drift']:.2f})")

# Event Horizon line
ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2,
           label=f'Event Horizon = {EVENT_HORIZON}')

# Old cap line for reference
ax.axhline(y=0.3, color='gray', linestyle=':', linewidth=1.5, alpha=0.6,
           label='Old fake cap (~0.3)')

# Phase boundaries
for i, boundary in enumerate(PHASE_BOUNDARIES):
    ax.axvline(x=boundary + 0.5, color='gray', linestyle=':', alpha=0.3)
    if i < len(PHASE_BOUNDARIES):
        start = 0.5 if i == 0 else PHASE_BOUNDARIES[i-1] + 0.5
        end = boundary + 0.5
        ax.axvspan(start, end, alpha=0.1, color=PHASE_COLORS[i])

# Recovery phase
ax.axvspan(PHASE_BOUNDARIES[-1] + 0.5, 15.5, alpha=0.1, color=PHASE_COLORS[-1])

# Labels
ax.set_xlabel('Turn', fontsize=12)
ax.set_ylabel('5D Drift (Uncapped)', fontsize=12)
ax.set_title('Run 012: Uncapped Drift Trajectories - Claude Fleet (7 Ships)\n'
             'All ships crossed Event Horizon, ALL RECOVERED', fontsize=14)
ax.legend(loc='upper right', fontsize=9)
ax.set_xlim(0.5, 15.5)
ax.set_ylim(0, 4)
ax.grid(True, alpha=0.3)

# Phase labels at bottom
for i, name in enumerate(PHASE_NAMES):
    start = 0.5 if i == 0 else PHASE_BOUNDARIES[i-1] + 0.5
    end = PHASE_BOUNDARIES[i] + 0.5 if i < len(PHASE_BOUNDARIES) else 15.5
    mid = (start + end) / 2
    ax.text(mid, -0.25, name, ha='center', fontsize=9, color=PHASE_COLORS[i], fontweight='bold')

plt.tight_layout()
plt.savefig(STABILITY_DIR / "run012_drift_trajectories.png", dpi=150, bbox_inches='tight')
plt.savefig(STABILITY_DIR / "run012_drift_trajectories.svg", bbox_inches='tight')
print(f"Saved: {STABILITY_DIR / 'run012_drift_trajectories.png'}")

# =============================================================================
# VISUALIZATION 2: Drift Range Comparison (Old vs New)
# =============================================================================
fig, axes = plt.subplots(1, 2, figsize=(14, 6))

# Left: Box plot of drift values by ship
ax1 = axes[0]
drift_data = [ship["drift_sequence"] for ship in ships]
ship_names = [ship["name"].replace("claude-", "") for ship in ships]

bp = ax1.boxplot(drift_data, labels=ship_names, patch_artist=True)
for patch, color in zip(bp['boxes'], colors):
    patch.set_facecolor(color)
    patch.set_alpha(0.6)

ax1.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, label='Event Horizon (1.23)')
ax1.axhline(y=0.3, color='gray', linestyle=':', linewidth=1.5, alpha=0.6, label='Old fake cap')
ax1.set_ylabel('5D Drift', fontsize=12)
ax1.set_title('Drift Distribution by Ship (Uncapped)', fontsize=12)
ax1.legend()
ax1.tick_params(axis='x', rotation=45)
ax1.grid(True, alpha=0.3, axis='y')

# Right: Phase-by-phase drift comparison
ax2 = axes[1]
phase_order = ['baseline', 'identity', 'boundary', 'perturbation', 'recovery']
phase_means = {phase: [] for phase in phase_order}

for ship in ships:
    for phase in phase_order:
        phase_means[phase].extend(ship["phases"].get(phase, []))

phase_labels = [p.title() for p in phase_order]
phase_values = [np.mean(phase_means[p]) for p in phase_order]
phase_stds = [np.std(phase_means[p]) for p in phase_order]

bars = ax2.bar(phase_labels, phase_values, yerr=phase_stds, capsize=5,
               color=PHASE_COLORS, alpha=0.7, edgecolor='black')
ax2.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2, label='Event Horizon (1.23)')
ax2.set_ylabel('Mean Drift', fontsize=12)
ax2.set_title('Mean Drift by Phase (All Ships)', fontsize=12)
ax2.legend()
ax2.grid(True, alpha=0.3, axis='y')

# Add value labels on bars
for bar, val in zip(bars, phase_values):
    ax2.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.1,
             f'{val:.2f}', ha='center', fontsize=10)

plt.tight_layout()
plt.savefig(STABILITY_DIR / "run012_drift_distribution.png", dpi=150, bbox_inches='tight')
plt.savefig(STABILITY_DIR / "run012_drift_distribution.svg", bbox_inches='tight')
print(f"Saved: {STABILITY_DIR / 'run012_drift_distribution.png'}")

# =============================================================================
# VISUALIZATION 3: 5D Dimension Breakdown (First Turn vs Final)
# =============================================================================
fig, axes = plt.subplots(2, 4, figsize=(16, 8))

dim_names = ['A_pole', 'B_zero', 'C_meta', 'D_identity', 'E_hedging']
dim_labels = ['Pole\n(Coherence)', 'Zero\n(Contradiction)', 'Meta\n(Uncertainty)',
              'Identity\n(Self-Ref)', 'Hedging\n(Equivocation)']

# Get dimension data from first and last turns
for i, ship in enumerate(ships[:4]):  # First 4 ships for top row
    ax = axes[0, i]

    # Get first turn dimensions
    first_turn = data["results"][i]["turns"][0]["drift_dimensions"]
    last_turn = data["results"][i]["turns"][-1]["drift_dimensions"]

    x = np.arange(len(dim_names))
    width = 0.35

    first_vals = [first_turn.get(d, 0) for d in dim_names]
    last_vals = [last_turn.get(d, 0) for d in dim_names]

    bars1 = ax.bar(x - width/2, first_vals, width, label='Turn 1', color='#f44336', alpha=0.7)
    bars2 = ax.bar(x + width/2, last_vals, width, label='Turn 15', color='#4CAF50', alpha=0.7)

    ax.set_title(ship["name"].replace("claude-", ""), fontsize=10)
    ax.set_xticks(x)
    ax.set_xticklabels(['A', 'B', 'C', 'D', 'E'], fontsize=8)
    ax.set_ylim(0, 7)
    if i == 0:
        ax.set_ylabel('Dimension Value', fontsize=10)
    if i == 3:
        ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3, axis='y')

# Bottom row: remaining ships
for i, ship in enumerate(ships[4:7]):
    ax = axes[1, i]

    # Get first turn dimensions
    first_turn = data["results"][i+4]["turns"][0]["drift_dimensions"]
    last_turn = data["results"][i+4]["turns"][-1]["drift_dimensions"]

    x = np.arange(len(dim_names))
    width = 0.35

    first_vals = [first_turn.get(d, 0) for d in dim_names]
    last_vals = [last_turn.get(d, 0) for d in dim_names]

    bars1 = ax.bar(x - width/2, first_vals, width, label='Turn 1', color='#f44336', alpha=0.7)
    bars2 = ax.bar(x + width/2, last_vals, width, label='Turn 15', color='#4CAF50', alpha=0.7)

    ax.set_title(ship["name"].replace("claude-", ""), fontsize=10)
    ax.set_xticks(x)
    ax.set_xticklabels(dim_labels, fontsize=7)
    ax.set_ylim(0, 7)
    if i == 0:
        ax.set_ylabel('Dimension Value', fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')

# Hide unused subplot
axes[1, 3].axis('off')

fig.suptitle('5D Drift Dimensions: Turn 1 (High Drift) vs Turn 15 (Recovery)\n'
             'D_identity consistently highest across all ships', fontsize=12)
plt.tight_layout()
plt.savefig(PILLAR_DIR / "run012_5d_dimensions.png", dpi=150, bbox_inches='tight')
plt.savefig(PILLAR_DIR / "run012_5d_dimensions.svg", bbox_inches='tight')
print(f"Saved: {PILLAR_DIR / 'run012_5d_dimensions.png'}")

# =============================================================================
# VISUALIZATION 4: Key Metrics Summary
# =============================================================================
fig, ax = plt.subplots(figsize=(10, 6))

metrics = ['Baseline\nDrift', 'Peak\nDrift', 'Final\nDrift', 'Recovery\nRatio', 'Lambda\n(x10)']
x = np.arange(len(metrics))
width = 0.1

for i, ship in enumerate(ships):
    vals = [
        ship["baseline_drift"],
        ship["peak_drift"],
        ship["final_drift"],
        ship["recovery_ratio"] * 3,  # Scale for visibility
        ship["lambda"] * -10  # Negate and scale (negative lambda = drift increasing)
    ]
    offset = (i - len(ships)/2) * width + width/2
    ax.bar(x + offset, vals, width, label=ship["name"].replace("claude-", ""),
           color=colors[i], alpha=0.8)

ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', linewidth=2)
ax.set_xticks(x)
ax.set_xticklabels(metrics, fontsize=10)
ax.set_ylabel('Value', fontsize=12)
ax.set_title('Run 012 Key Metrics by Ship\n'
             'Event Horizon = 1.23 | All ships crossed EH | All RECOVERED', fontsize=12)
ax.legend(bbox_to_anchor=(1.02, 1), loc='upper left', fontsize=8)
ax.grid(True, alpha=0.3, axis='y')

plt.tight_layout()
plt.savefig(REVALIDATION_DIR / "run012_metrics_summary.png", dpi=150, bbox_inches='tight')
plt.savefig(REVALIDATION_DIR / "run012_metrics_summary.svg", bbox_inches='tight')
print(f"Saved: {REVALIDATION_DIR / 'run012_metrics_summary.png'}")

# =============================================================================
# Print Summary Statistics
# =============================================================================
print("\n" + "="*60)
print("RUN 012 SUMMARY: UNCAPPED 5D DRIFT (Claude Fleet)")
print("="*60)
print(f"\nFleet Size: {len(ships)} ships")
print(f"Event Horizon Threshold: {EVENT_HORIZON}")
print(f"\nKey Findings:")
print(f"  - Ships crossed EH: {sum(1 for s in ships if s['eh_crossed'])}/{len(ships)}")
print(f"  - Ships RECOVERED: {sum(1 for s in ships if s['hysteresis'] == 'RECOVERED')}/{len(ships)}")
print(f"  - Ships STUCK: {sum(1 for s in ships if s['hysteresis'] == 'STUCK')}/{len(ships)}")

print(f"\nDrift Statistics:")
all_drifts = [d for s in ships for d in s["drift_sequence"]]
print(f"  - Min drift: {min(all_drifts):.4f}")
print(f"  - Max drift: {max(all_drifts):.4f}")
print(f"  - Mean drift: {np.mean(all_drifts):.4f}")
print(f"  - Std drift: {np.std(all_drifts):.4f}")

print(f"\nPeak drifts by ship:")
for ship in sorted(ships, key=lambda s: s["peak_drift"], reverse=True):
    print(f"  - {ship['name']}: {ship['peak_drift']:.4f}")

print(f"\nOld cap (fake metric): ~0.3")
print(f"Actual drift range: {min(all_drifts):.2f} - {max(all_drifts):.2f}")
print(f"That's {max(all_drifts)/0.3:.1f}x higher than the old cap!")

print("\n" + "="*60)

plt.close('all')
print(f"\nVisualizations saved to:")
print(f"  - Stability: {STABILITY_DIR}")
print(f"  - Pillars: {PILLAR_DIR}")
print(f"  - Revalidation: {REVALIDATION_DIR}")
