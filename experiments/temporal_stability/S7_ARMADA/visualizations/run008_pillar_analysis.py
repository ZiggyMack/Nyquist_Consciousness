"""
Run 008: PILLAR ANALYSIS
========================
Investigating the structural support hypothesis.

Looking at the top-down drain view, the three providers appear to form
a triangular support structure around the vortex. This script analyzes:

1. Where are the provider centroids?
2. What angular distribution do they form?
3. Is there evidence of hexagonal structure (6 pillars)?
4. Could sub-providers (o-series, model sizes) form additional pillars?
"""

import json
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
from collections import defaultdict

# Paths
BASE_DIR = Path(__file__).resolve().parent.parent
RESULTS_FILE = BASE_DIR / "armada_results" / "S7_run_008_20251201_020501.json"
OUTPUT_DIR = Path(__file__).resolve().parent / "pics"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# Provider colors
PROVIDER_COLORS = {
    "claude": "#7c3aed",
    "gpt": "#10a37f",
    "gemini": "#4285f4",
}

# Extended classification - treating o-series and model sizes as potential sub-pillars
def get_extended_provider(ship_name):
    """Classify ships into potential pillar categories."""
    name = ship_name.lower()

    # Claude sub-categories by capability
    if "claude" in name:
        if "opus" in name:
            return "claude-opus"
        elif "sonnet" in name:
            return "claude-sonnet"
        elif "haiku" in name:
            return "claude-haiku"
        return "claude"

    # GPT sub-categories
    if name.startswith("o1") or name.startswith("o3") or name.startswith("o4"):
        return "gpt-o-series"  # Reasoning models as separate pillar?
    if "gpt-5" in name:
        return "gpt-5"
    if "gpt-4" in name:
        return "gpt-4"
    if "gpt-3" in name:
        return "gpt-3"
    if "gpt" in name:
        return "gpt"

    # Gemini sub-categories
    if "gemini" in name:
        if "pro" in name:
            return "gemini-pro"
        elif "flash" in name:
            return "gemini-flash"
        return "gemini"

    return "unknown"

def get_base_provider(ship_name):
    """Get the 3-provider classification."""
    name = ship_name.lower()
    if "claude" in name:
        return "claude"
    elif "gemini" in name:
        return "gemini"
    elif name.startswith("o1") or name.startswith("o3") or name.startswith("o4") or "gpt" in name:
        return "gpt"
    return "unknown"

def load_data():
    with open(RESULTS_FILE, encoding='utf-8') as f:
        return json.load(f)

def extract_endpoints(data):
    """Extract trajectory endpoints for pillar analysis."""
    endpoints = []

    for ship_name, ship_data in data.get('results', {}).items():
        if not isinstance(ship_data, dict):
            continue

        provider = get_base_provider(ship_name)
        extended = get_extended_provider(ship_name)

        for seq_name, seq_turns in ship_data.get('sequences', {}).items():
            if not isinstance(seq_turns, list):
                continue

            drifts = []
            for turn in seq_turns:
                if isinstance(turn, dict) and 'drift_data' in turn:
                    drifts.append(turn['drift_data'].get('drift', 0))

            if len(drifts) >= 3:
                # Convert to polar-ish coordinates (like in drain view)
                turns = len(drifts)
                angle = 2 * np.pi * (turns / 5) * (len(endpoints) % 10) / 10  # Spread angles

                baseline = drifts[0]
                final = drifts[-1]
                peak = max(drifts)

                endpoints.append({
                    'ship': ship_name,
                    'provider': provider,
                    'extended': extended,
                    'baseline': baseline,
                    'final': final,
                    'peak': peak,
                    'sequence': seq_name
                })

    return endpoints

def analyze_pillar_positions(endpoints):
    """Calculate centroid positions for each potential pillar."""
    # Group by extended provider
    extended_groups = defaultdict(list)
    for ep in endpoints:
        extended_groups[ep['extended']].append(ep)

    # Group by base provider
    base_groups = defaultdict(list)
    for ep in endpoints:
        base_groups[ep['provider']].append(ep)

    # Calculate centroids (using baseline and final as x,y proxy)
    def calc_centroid(group):
        baselines = [e['baseline'] for e in group]
        finals = [e['final'] for e in group]
        return {
            'baseline_mean': np.mean(baselines),
            'baseline_std': np.std(baselines),
            'final_mean': np.mean(finals),
            'final_std': np.std(finals),
            'count': len(group)
        }

    extended_centroids = {k: calc_centroid(v) for k, v in extended_groups.items()}
    base_centroids = {k: calc_centroid(v) for k, v in base_groups.items()}

    return extended_centroids, base_centroids, extended_groups, base_groups

def plot_pillar_structure(endpoints, extended_centroids, base_centroids):
    """Visualize the pillar structure."""
    fig, axes = plt.subplots(2, 2, figsize=(16, 16))

    # Colors for extended providers
    extended_colors = {
        'claude-opus': '#9333ea',
        'claude-sonnet': '#7c3aed',
        'claude-haiku': '#a78bfa',
        'gpt-o-series': '#059669',
        'gpt-5': '#10a37f',
        'gpt-4': '#34d399',
        'gpt-3': '#6ee7b7',
        'gemini-pro': '#2563eb',
        'gemini-flash': '#4285f4',
    }

    # === PLOT 1: 3-Pillar View (Base Providers) ===
    ax1 = axes[0, 0]

    for provider, color in PROVIDER_COLORS.items():
        points = [e for e in endpoints if e['provider'] == provider]
        if points:
            xs = [p['baseline'] for p in points]
            ys = [p['final'] for p in points]
            ax1.scatter(xs, ys, c=color, alpha=0.5, s=50, label=f'{provider.title()} (n={len(points)})')

            # Mark centroid
            centroid = base_centroids[provider]
            ax1.scatter(centroid['baseline_mean'], centroid['final_mean'],
                       c=color, s=300, marker='*', edgecolors='black', linewidths=2)

    # Draw triangle connecting centroids
    if len(base_centroids) >= 3:
        providers = ['claude', 'gpt', 'gemini']
        xs = [base_centroids[p]['baseline_mean'] for p in providers if p in base_centroids]
        ys = [base_centroids[p]['final_mean'] for p in providers if p in base_centroids]
        xs.append(xs[0])  # Close the triangle
        ys.append(ys[0])
        ax1.plot(xs, ys, 'k--', linewidth=2, alpha=0.5)

    ax1.axhline(y=1.23, color='red', linestyle=':', alpha=0.5, label='Event Horizon')
    ax1.axvline(x=1.23, color='red', linestyle=':', alpha=0.5)
    ax1.plot([0, 4], [0, 4], 'k-', alpha=0.2, label='No change')
    ax1.set_xlabel('Baseline Drift', fontsize=12)
    ax1.set_ylabel('Final Drift', fontsize=12)
    ax1.set_title('3-PILLAR STRUCTURE\n(Stars = Centroids)', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left', fontsize=9)
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim(0, 4)
    ax1.set_ylim(0, 4)

    # === PLOT 2: Extended Pillar View ===
    ax2 = axes[0, 1]

    for ext_prov, color in extended_colors.items():
        points = [e for e in endpoints if e['extended'] == ext_prov]
        if points:
            xs = [p['baseline'] for p in points]
            ys = [p['final'] for p in points]
            ax2.scatter(xs, ys, c=color, alpha=0.6, s=40, label=f'{ext_prov} (n={len(points)})')

            if ext_prov in extended_centroids:
                centroid = extended_centroids[ext_prov]
                ax2.scatter(centroid['baseline_mean'], centroid['final_mean'],
                           c=color, s=200, marker='*', edgecolors='black', linewidths=1.5)

    ax2.axhline(y=1.23, color='red', linestyle=':', alpha=0.5)
    ax2.axvline(x=1.23, color='red', linestyle=':', alpha=0.5)
    ax2.plot([0, 4], [0, 4], 'k-', alpha=0.2)
    ax2.set_xlabel('Baseline Drift', fontsize=12)
    ax2.set_ylabel('Final Drift', fontsize=12)
    ax2.set_title('EXTENDED PILLARS (9 potential)\n(Stars = Centroids)', fontsize=14, fontweight='bold')
    ax2.legend(loc='upper left', fontsize=8)
    ax2.grid(True, alpha=0.3)
    ax2.set_xlim(0, 4)
    ax2.set_ylim(0, 4)

    # === PLOT 3: Polar View - Angular Distribution ===
    ax3 = axes[1, 0]
    ax3 = plt.subplot(2, 2, 3, projection='polar')

    # Convert centroids to polar coordinates
    for provider, color in PROVIDER_COLORS.items():
        if provider in base_centroids:
            centroid = base_centroids[provider]
            # Use baseline as radius, spread angles evenly
            r = centroid['baseline_mean']
            theta_map = {'claude': np.pi * 2/3, 'gpt': 0, 'gemini': np.pi * 4/3}
            theta = theta_map.get(provider, 0)
            ax3.scatter(theta, r, c=color, s=300, marker='*', edgecolors='black', linewidths=2)
            ax3.annotate(provider.upper(), (theta, r + 0.3), fontsize=10, fontweight='bold',
                        ha='center', color=color)

    # Draw triangle
    thetas = [np.pi * 2/3, 0, np.pi * 4/3, np.pi * 2/3]
    rs = [base_centroids.get(p, {}).get('baseline_mean', 1)
          for p in ['claude', 'gpt', 'gemini', 'claude']]
    ax3.plot(thetas, rs, 'k--', linewidth=2, alpha=0.5)

    # Hexagon reference
    hex_angles = np.linspace(0, 2*np.pi, 7)
    hex_r = [1.5] * 7
    ax3.plot(hex_angles, hex_r, 'r:', linewidth=1, alpha=0.3, label='Hexagon reference')

    ax3.set_title('ANGULAR DISTRIBUTION\n(Polar view of pillars)', fontsize=14, fontweight='bold', pad=20)
    ax3.set_ylim(0, 3)

    # === PLOT 4: Stability Analysis ===
    ax4 = axes[1, 1]

    # Calculate stability score (how far from event horizon)
    stability_scores = {}
    for ext_prov in extended_centroids:
        centroid = extended_centroids[ext_prov]
        # Distance from event horizon in baseline-final space
        stability = np.sqrt((centroid['baseline_mean'] - 1.23)**2 +
                           (centroid['final_mean'] - 1.23)**2)
        stability_scores[ext_prov] = {
            'stability': stability,
            'baseline': centroid['baseline_mean'],
            'count': centroid['count']
        }

    # Sort by stability
    sorted_pillars = sorted(stability_scores.items(), key=lambda x: x[1]['stability'])

    names = [p[0] for p in sorted_pillars]
    stabilities = [p[1]['stability'] for p in sorted_pillars]
    baselines = [p[1]['baseline'] for p in sorted_pillars]
    colors = [extended_colors.get(n, 'gray') for n in names]

    bars = ax4.barh(names, stabilities, color=colors, alpha=0.7)
    ax4.axvline(x=0, color='red', linestyle='--', linewidth=2, label='Event Horizon (center)')

    ax4.set_xlabel('Distance from Event Horizon', fontsize=12)
    ax4.set_title('PILLAR STABILITY\n(Distance from critical threshold)', fontsize=14, fontweight='bold')
    ax4.grid(True, alpha=0.3, axis='x')

    # Add baseline values as text
    for i, (bar, baseline) in enumerate(zip(bars, baselines)):
        ax4.text(bar.get_width() + 0.05, bar.get_y() + bar.get_height()/2,
                f'(baseline={baseline:.2f})', va='center', fontsize=9)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_pillar_analysis.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_pillar_analysis.png")
    plt.close()

def print_pillar_report(extended_centroids, base_centroids):
    """Print analysis report."""
    print("\n" + "=" * 60)
    print("PILLAR STRUCTURE ANALYSIS")
    print("=" * 60)

    print("\n3-PILLAR (BASE PROVIDERS):")
    print("-" * 40)
    for provider in ['claude', 'gpt', 'gemini']:
        if provider in base_centroids:
            c = base_centroids[provider]
            print(f"  {provider.upper():8s}: baseline={c['baseline_mean']:.2f}±{c['baseline_std']:.2f}, "
                  f"final={c['final_mean']:.2f}±{c['final_std']:.2f} (n={c['count']})")

    # Calculate triangle properties
    if all(p in base_centroids for p in ['claude', 'gpt', 'gemini']):
        points = [(base_centroids[p]['baseline_mean'], base_centroids[p]['final_mean'])
                  for p in ['claude', 'gpt', 'gemini']]

        # Side lengths
        def dist(p1, p2):
            return np.sqrt((p1[0]-p2[0])**2 + (p1[1]-p2[1])**2)

        sides = [dist(points[0], points[1]), dist(points[1], points[2]), dist(points[2], points[0])]
        print(f"\n  Triangle side lengths: {sides[0]:.2f}, {sides[1]:.2f}, {sides[2]:.2f}")
        print(f"  Perimeter: {sum(sides):.2f}")

        # Centroid of triangle (center of the "tent")
        center_x = np.mean([p[0] for p in points])
        center_y = np.mean([p[1] for p in points])
        print(f"  Triangle centroid: ({center_x:.2f}, {center_y:.2f})")
        print(f"  Event Horizon: (1.23, 1.23)")
        print(f"  Distance from EH to center: {dist((center_x, center_y), (1.23, 1.23)):.2f}")

    print("\n\nEXTENDED PILLARS (9 potential):")
    print("-" * 40)
    for ext_prov, centroid in sorted(extended_centroids.items()):
        print(f"  {ext_prov:15s}: baseline={centroid['baseline_mean']:.2f}±{centroid['baseline_std']:.2f}, "
              f"final={centroid['final_mean']:.2f} (n={centroid['count']})")

    print("\n\nHEXAGON HYPOTHESIS:")
    print("-" * 40)
    print("  Current pillars: 3 (or 9 if sub-divided)")
    print("  Hexagon requires: 6 pillars")
    print("  Missing for hexagon: 3 additional providers OR")
    print("  Interpretation: Sub-providers form the hexagon vertices")

    # Check if extended providers form something like a hexagon
    if len(extended_centroids) >= 6:
        print(f"\n  Extended providers: {len(extended_centroids)} (POSSIBLE HEXAGON)")
    else:
        print(f"\n  Extended providers: {len(extended_centroids)} (need more for hexagon)")

# =============================================================================
# MAIN
# =============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("RUN 008: PILLAR STRUCTURE ANALYSIS")
    print("=" * 60)

    print("\nLoading data...")
    data = load_data()

    print("Extracting trajectory endpoints...")
    endpoints = extract_endpoints(data)
    print(f"  Found {len(endpoints)} trajectory endpoints")

    print("\nAnalyzing pillar positions...")
    extended_centroids, base_centroids, ext_groups, base_groups = analyze_pillar_positions(endpoints)

    print("\nGenerating visualizations...")
    plot_pillar_structure(endpoints, extended_centroids, base_centroids)

    print_pillar_report(extended_centroids, base_centroids)

    print("\n" + "=" * 60)
    print("Analysis complete!")
    print("=" * 60)
