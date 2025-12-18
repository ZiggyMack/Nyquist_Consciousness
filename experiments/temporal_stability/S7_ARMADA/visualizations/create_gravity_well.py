#!/usr/bin/env python3
"""
Create visualization showing the identity stability basin (gravity well)
from Run 008 data.

This plots baseline vs max drift, colored by recovery status,
to show the attractor dynamics we discovered.
"""

import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path

# Load results
results_path = Path(__file__).resolve().parent.parent / "results" / "runs" / "S7_run_008_20251201_020501.json"

with open(results_path, 'r') as f:
    data = json.load(f)

# Extract stability basin data
basin_data = []

for ship_name, ship_data in data['results'].items():
    provider = ship_data['config']['provider']

    for seq_name, turns in ship_data['sequences'].items():
        if not turns:
            continue

        # Filter to actual turns (not _sequence_meta entries)
        actual_turns = [t for t in turns if 'drift_data' in t and t['drift_data'] is not None]

        # Get baseline (first turn) and max drift
        drifts = [t['drift_data']['drift'] for t in actual_turns if t['drift_data']['drift'] is not None]

        if len(drifts) < 2:
            continue

        baseline = drifts[0]
        max_drift = max(drifts)
        final_drift = drifts[-1]

        # Calculate recovery ratio
        if baseline > 0.01:
            recovery_ratio = final_drift / baseline
        else:
            recovery_ratio = final_drift / 0.01  # Avoid division by zero

        # Determine status
        stuck = recovery_ratio > 1.5

        basin_data.append({
            'ship': ship_name,
            'provider': provider,
            'sequence': seq_name,
            'baseline': baseline,
            'peak_drift': max_drift,
            'final_drift': final_drift,
            'recovery_ratio': recovery_ratio,
            'stuck': stuck
        })

# Create the stability basin plot
fig, axes = plt.subplots(1, 2, figsize=(16, 7))

# Plot 1: Baseline vs Max Drift (colored by STUCK/RECOVERED)
ax1 = axes[0]

stuck_points = [d for d in basin_data if d['stuck']]
recovered_points = [d for d in basin_data if not d['stuck']]

# Plot recovered (green) first, then stuck (red) on top
ax1.scatter(
    [d['baseline'] for d in recovered_points],
    [d['peak_drift'] for d in recovered_points],
    c='#2ecc71', s=100, alpha=0.7, label=f'RECOVERED ({len(recovered_points)})',
    edgecolors='white', linewidth=1
)
ax1.scatter(
    [d['baseline'] for d in stuck_points],
    [d['peak_drift'] for d in stuck_points],
    c='#e74c3c', s=100, alpha=0.7, label=f'STUCK ({len(stuck_points)})',
    edgecolors='white', linewidth=1
)

# Add diagonal reference line (max = baseline)
max_val = max([d['peak_drift'] for d in basin_data])
ax1.plot([0, max_val], [0, max_val], 'k--', alpha=0.3, label='No drift (baseline = max)')

# Add 1.5x threshold line
ax1.plot([0, max_val/1.5], [0, max_val], 'r--', alpha=0.3, label='1.5x push threshold')

ax1.set_xlabel('Baseline Drift (first turn)', fontsize=12)
ax1.set_ylabel('Maximum Drift Achieved', fontsize=12)
ax1.set_title('Identity Stability Basin: Where Does Identity Get "Stuck"?', fontsize=14, fontweight='bold')
ax1.legend(loc='upper left')
ax1.grid(True, alpha=0.3)

# Add annotation
ax1.annotate(
    'STABILITY BASIN\n(identity snaps back)',
    xy=(2.5, 2.8), fontsize=10, ha='center',
    bbox=dict(boxstyle='round', facecolor='#2ecc71', alpha=0.3)
)
ax1.annotate(
    'COLLAPSE ZONE\n(identity gets stuck)',
    xy=(0.5, 3.0), fontsize=10, ha='center',
    bbox=dict(boxstyle='round', facecolor='#e74c3c', alpha=0.3)
)

# Plot 2: Recovery Ratio Distribution by Provider
ax2 = axes[1]

providers = ['claude', 'gpt', 'gemini']
provider_colors = {'claude': '#9b59b6', 'gpt': '#3498db', 'gemini': '#e67e22'}
provider_labels = {'claude': 'Claude (Anthropic)', 'gpt': 'GPT (OpenAI)', 'gemini': 'Gemini (Google)'}

for i, provider in enumerate(providers):
    ratios = [d['recovery_ratio'] for d in basin_data if d['provider'] == provider]
    if ratios:
        positions = [i + np.random.uniform(-0.2, 0.2) for _ in ratios]

        # Cap display at 10 for visibility
        display_ratios = [min(r, 10) for r in ratios]

        ax2.scatter(
            positions, display_ratios,
            c=provider_colors[provider], s=80, alpha=0.6,
            label=f'{provider_labels[provider]} (n={len(ratios)})',
            edgecolors='white', linewidth=0.5
        )

# Add threshold line
ax2.axhline(y=1.5, color='red', linestyle='--', alpha=0.7, label='STUCK threshold (1.5x)')
ax2.axhline(y=1.0, color='green', linestyle='--', alpha=0.5, label='Perfect recovery (1.0x)')

ax2.set_xticks([0, 1, 2])
ax2.set_xticklabels(['Claude (Anthropic)', 'GPT (OpenAI)', 'Gemini (Google)'])
ax2.set_ylabel('Recovery Ratio (Final / Baseline)', fontsize=12)
ax2.set_title('Recovery Ratio by Provider', fontsize=14, fontweight='bold')
ax2.legend(loc='upper right')
ax2.grid(True, alpha=0.3, axis='y')
ax2.set_ylim(0, 10.5)

# Add annotation
ax2.annotate(
    'Above 1.5 = STUCK\nBelow 1.5 = RECOVERED',
    xy=(2.5, 8), fontsize=9, ha='center',
    bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5)
)

plt.tight_layout()
plt.savefig(Path(__file__).parent / 'pics' / 'run008_stability_basin.png', dpi=150, bbox_inches='tight')
plt.close()

print("Created: run008_stability_basin.png")

# Also create a 3D trajectory plot showing the actual paths
fig = plt.figure(figsize=(12, 10))
ax3d = fig.add_subplot(111, projection='3d')

# For each sequence, plot the trajectory through drift space
for ship_name, ship_data in data['results'].items():
    provider = ship_data['config']['provider']
    color = provider_colors.get(provider, 'gray')

    for seq_name, turns in ship_data['sequences'].items():
        if not turns or len(turns) < 3:
            continue

        # Filter to actual turns (not _sequence_meta entries)
        actual_turns = [t for t in turns if 'drift_data' in t and t['drift_data'] is not None]

        # Get trajectory
        drifts = [t['drift_data']['drift'] for t in actual_turns if t['drift_data']['drift'] is not None]

        if len(drifts) < 3:
            continue

        # Plot as: Turn number (X) vs Drift (Y) vs Cumulative change (Z)
        turns_x = list(range(len(drifts)))
        cumulative = [sum(drifts[:i+1]) for i in range(len(drifts))]

        ax3d.plot(turns_x, drifts, cumulative, alpha=0.4, color=color, linewidth=1)

        # Mark start and end
        ax3d.scatter([0], [drifts[0]], [cumulative[0]], c='green', s=30, marker='o')
        ax3d.scatter([len(drifts)-1], [drifts[-1]], [cumulative[-1]], c='red', s=30, marker='x')

ax3d.set_xlabel('Turn Number')
ax3d.set_ylabel('Drift Value')
ax3d.set_zlabel('Cumulative Drift')
ax3d.set_title('Identity Trajectories Through Conversation\n(Green=start, Red=end)', fontsize=14, fontweight='bold')

# Add legend manually
from matplotlib.lines import Line2D
legend_elements = [
    Line2D([0], [0], color='#9b59b6', label='Claude'),
    Line2D([0], [0], color='#3498db', label='GPT (OpenAI)'),
    Line2D([0], [0], color='#e67e22', label='Gemini'),
]
ax3d.legend(handles=legend_elements, loc='upper left')

plt.savefig(Path(__file__).parent / 'pics' / 'run008_identity_trajectories.png', dpi=150, bbox_inches='tight')
plt.close()

print("Created: run008_identity_trajectories.png")

# Summary stats
print("\n=== STABILITY BASIN ANALYSIS ===")
print(f"Total sequences: {len(basin_data)}")
print(f"STUCK: {len(stuck_points)} ({100*len(stuck_points)/len(basin_data):.1f}%)")
print(f"RECOVERED: {len(recovered_points)} ({100*len(recovered_points)/len(basin_data):.1f}%)")

print("\nBy Provider:")
for provider in providers:
    p_data = [d for d in basin_data if d['provider'] == provider]
    p_stuck = [d for d in p_data if d['stuck']]
    if p_data:
        print(f"  {provider_labels[provider]}: {len(p_stuck)}/{len(p_data)} STUCK ({100*len(p_stuck)/len(p_data):.1f}%)")

print("\nKey Finding:")
stuck_baselines = [d['baseline'] for d in stuck_points]
recovered_baselines = [d['baseline'] for d in recovered_points]
print(f"  STUCK avg baseline: {np.mean(stuck_baselines):.3f}")
print(f"  RECOVERED avg baseline: {np.mean(recovered_baselines):.3f}")
