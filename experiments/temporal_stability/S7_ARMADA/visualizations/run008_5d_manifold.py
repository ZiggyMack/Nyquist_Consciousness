"""
Run 008 5D Identity Manifold Visualizations

Creates true pole-zero maps and higher-dimensional visualizations using
REAL 5D drift data from Run 008 (not the old response-length proxy).

Visualizations:
1. True Pole-Zero 2D Map (A vs B dimensions)
2. 3D Identity Manifold (Pole x Zero x Meta)
3. 4D Visualization (3D + color = Identity Coherence)
4. 5D Visualization (3D + color + size)
5. Provider clustering analysis
6. Ship trajectory plots through identity space
"""

import json
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
from pathlib import Path
from collections import defaultdict

# Paths
BASE_DIR = Path(__file__).parent.parent
RESULTS_FILE = BASE_DIR / "armada_results" / "S7_run_008_20251201_020501.json"
OUTPUT_DIR = Path(__file__).parent / "pics"
OUTPUT_DIR.mkdir(exist_ok=True)

# Provider colors
PROVIDER_COLORS = {
    "claude": "#7c3aed",    # Purple
    "gpt": "#10a37f",       # Green
    "gemini": "#4285f4",    # Blue
    "o-series": "#f97316",  # Orange
}

def get_provider(ship_name):
    """Determine provider from ship name."""
    name = ship_name.lower()
    if "claude" in name:
        return "claude"
    elif "gemini" in name:
        return "gemini"
    elif name.startswith("o1") or name.startswith("o3") or name.startswith("o4"):
        return "o-series"
    elif "gpt" in name:
        return "gpt"
    return "unknown"

def load_run008_data():
    """Load and parse Run 008 results."""
    with open(RESULTS_FILE, encoding='utf-8') as f:
        data = json.load(f)
    return data

def extract_all_points(data):
    """Extract all 5D data points from all ships and turns."""
    points = []

    for ship_name, ship_data in data['results'].items():
        provider = get_provider(ship_name)

        for seq_name, seq_turns in ship_data.get('sequences', {}).items():
            if not isinstance(seq_turns, list):
                continue

            for turn in seq_turns:
                if 'drift_data' not in turn:
                    continue

                dims = turn['drift_data'].get('dimensions', {})
                if not dims:
                    continue

                points.append({
                    'ship': ship_name,
                    'provider': provider,
                    'sequence': seq_name,
                    'turn': turn.get('turn', 0),
                    'A': dims.get('pole_density', 0),
                    'B': dims.get('zero_density', 0),
                    'C': dims.get('meta_density', 0),
                    'D': dims.get('identity_coherence', 0),
                    'E': dims.get('hedging_ratio', 0),
                    'drift': turn['drift_data'].get('drift', 0),
                })

    return points

def extract_ship_averages(data):
    """Extract average 5D coordinates per ship."""
    ship_data = defaultdict(lambda: {'A': [], 'B': [], 'C': [], 'D': [], 'E': [], 'drift': []})

    for ship_name, ship_info in data['results'].items():
        for seq_name, seq_turns in ship_info.get('sequences', {}).items():
            if not isinstance(seq_turns, list):
                continue
            for turn in seq_turns:
                if 'drift_data' not in turn:
                    continue
                dims = turn['drift_data'].get('dimensions', {})
                if dims:
                    ship_data[ship_name]['A'].append(dims.get('pole_density', 0))
                    ship_data[ship_name]['B'].append(dims.get('zero_density', 0))
                    ship_data[ship_name]['C'].append(dims.get('meta_density', 0))
                    ship_data[ship_name]['D'].append(dims.get('identity_coherence', 0))
                    ship_data[ship_name]['E'].append(dims.get('hedging_ratio', 0))
                    ship_data[ship_name]['drift'].append(turn['drift_data'].get('drift', 0))

    # Average per ship
    averages = []
    for ship_name, values in ship_data.items():
        if values['A']:
            averages.append({
                'ship': ship_name,
                'provider': get_provider(ship_name),
                'A': np.mean(values['A']),
                'B': np.mean(values['B']),
                'C': np.mean(values['C']),
                'D': np.mean(values['D']),
                'E': np.mean(values['E']),
                'drift': np.mean(values['drift']),
            })

    return averages

# =============================================================================
# VISUALIZATION 1: True Pole-Zero 2D Map
# =============================================================================
def plot_pole_zero_2d(points):
    """Create 2D scatter: Pole (A) vs Zero (B) density."""
    fig, ax = plt.subplots(figsize=(12, 10))

    for provider in PROVIDER_COLORS:
        prov_points = [p for p in points if p['provider'] == provider]
        if not prov_points:
            continue

        xs = [p['A'] for p in prov_points]
        ys = [p['B'] for p in prov_points]

        ax.scatter(xs, ys, c=PROVIDER_COLORS[provider], alpha=0.6, s=50,
                  label=f"{provider.title()} ({len(prov_points)} pts)",
                  edgecolors='white', linewidth=0.5)

    # Reference lines
    ax.axhline(y=0, color='gray', linestyle='--', alpha=0.3)
    ax.axvline(x=0, color='gray', linestyle='--', alpha=0.3)

    # Quadrant labels
    ax.text(0.95, 0.95, "HIGH POLE\nHIGH ZERO\n(Conflicted)", transform=ax.transAxes,
           ha='right', va='top', fontsize=9, alpha=0.7,
           bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.3))
    ax.text(0.05, 0.95, "LOW POLE\nHIGH ZERO\n(Hedging)", transform=ax.transAxes,
           ha='left', va='top', fontsize=9, alpha=0.7,
           bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.3))
    ax.text(0.95, 0.05, "HIGH POLE\nLOW ZERO\n(Committed)", transform=ax.transAxes,
           ha='right', va='bottom', fontsize=9, alpha=0.7,
           bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.3))
    ax.text(0.05, 0.05, "LOW POLE\nLOW ZERO\n(Neutral)", transform=ax.transAxes,
           ha='left', va='bottom', fontsize=9, alpha=0.7,
           bbox=dict(boxstyle='round', facecolor='lightgray', alpha=0.3))

    ax.set_xlabel('Pole Density (A) — Assertive/Committed Language', fontsize=12)
    ax.set_ylabel('Zero Density (B) — Hedging/Qualifying Language', fontsize=12)
    ax.set_title('RUN 008: True Pole-Zero Identity Map\n29 Ships × All Turns (Real 5D Metric)',
                fontsize=14, fontweight='bold')
    ax.legend(loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_pole_zero_2d.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_pole_zero_2d.png")
    plt.close()

# =============================================================================
# VISUALIZATION 2: 3D Identity Manifold (Pole × Zero × Meta)
# =============================================================================
def plot_3d_manifold(points):
    """Create 3D scatter: Pole (A) × Zero (B) × Meta (C)."""
    fig = plt.figure(figsize=(14, 10))
    ax = fig.add_subplot(111, projection='3d')

    for provider in PROVIDER_COLORS:
        prov_points = [p for p in points if p['provider'] == provider]
        if not prov_points:
            continue

        xs = [p['A'] for p in prov_points]
        ys = [p['B'] for p in prov_points]
        zs = [p['C'] for p in prov_points]

        ax.scatter(xs, ys, zs, c=PROVIDER_COLORS[provider], alpha=0.6, s=40,
                  label=f"{provider.title()} ({len(prov_points)})",
                  edgecolors='white', linewidth=0.3)

    ax.set_xlabel('Pole Density (A)', fontsize=11)
    ax.set_ylabel('Zero Density (B)', fontsize=11)
    ax.set_zlabel('Meta Density (C)', fontsize=11)
    ax.set_title('RUN 008: 3D Identity Manifold\nPole × Zero × Meta Space',
                fontsize=14, fontweight='bold')
    ax.legend(loc='upper left', fontsize=10)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_manifold_3d.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_manifold_3d.png")
    plt.close()

# =============================================================================
# VISUALIZATION 3: 4D (3D + Color = Identity Coherence)
# =============================================================================
def plot_4d_manifold(points):
    """Create 4D visualization: 3D position + color = Identity Coherence (D)."""
    fig = plt.figure(figsize=(14, 10))
    ax = fig.add_subplot(111, projection='3d')

    xs = [p['A'] for p in points]
    ys = [p['B'] for p in points]
    zs = [p['C'] for p in points]
    colors = [p['D'] for p in points]  # Identity Coherence as color

    scatter = ax.scatter(xs, ys, zs, c=colors, cmap='viridis', alpha=0.7, s=40,
                        edgecolors='white', linewidth=0.3)

    cbar = plt.colorbar(scatter, ax=ax, shrink=0.6, pad=0.1)
    cbar.set_label('Identity Coherence (D) — First-Person Markers', fontsize=10)

    ax.set_xlabel('Pole Density (A)', fontsize=11)
    ax.set_ylabel('Zero Density (B)', fontsize=11)
    ax.set_zlabel('Meta Density (C)', fontsize=11)
    ax.set_title('RUN 008: 4D Identity Manifold\nPosition = A×B×C, Color = D (Identity Coherence)',
                fontsize=14, fontweight='bold')

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_manifold_4d.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_manifold_4d.png")
    plt.close()

# =============================================================================
# VISUALIZATION 4: 5D (3D + Color + Size)
# =============================================================================
def plot_5d_manifold(points):
    """Create 5D visualization: 3D position + color (D) + size (E)."""
    fig = plt.figure(figsize=(14, 10))
    ax = fig.add_subplot(111, projection='3d')

    xs = [p['A'] for p in points]
    ys = [p['B'] for p in points]
    zs = [p['C'] for p in points]
    colors = [p['D'] for p in points]  # Identity Coherence
    sizes = [max(10, p['E'] * 30) for p in points]  # Hedging Ratio as size

    scatter = ax.scatter(xs, ys, zs, c=colors, s=sizes, cmap='plasma', alpha=0.6,
                        edgecolors='white', linewidth=0.3)

    cbar = plt.colorbar(scatter, ax=ax, shrink=0.6, pad=0.1)
    cbar.set_label('Identity Coherence (D)', fontsize=10)

    ax.set_xlabel('Pole Density (A)', fontsize=11)
    ax.set_ylabel('Zero Density (B)', fontsize=11)
    ax.set_zlabel('Meta Density (C)', fontsize=11)
    ax.set_title('RUN 008: 5D Identity Manifold\nPosition = A×B×C, Color = D, Size = E (Hedging)',
                fontsize=14, fontweight='bold')

    # Add size legend
    ax.text2D(0.02, 0.98, "Point Size = Hedging Ratio (E)\nLarger = More Hedging",
             transform=ax.transAxes, fontsize=9, va='top',
             bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_manifold_5d.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_manifold_5d.png")
    plt.close()

# =============================================================================
# VISUALIZATION 5: Ship Averages by Provider
# =============================================================================
def plot_ship_averages(averages):
    """Plot average position of each ship in 2D pole-zero space."""
    fig, ax = plt.subplots(figsize=(14, 10))

    for provider in PROVIDER_COLORS:
        prov_ships = [s for s in averages if s['provider'] == provider]
        if not prov_ships:
            continue

        xs = [s['A'] for s in prov_ships]
        ys = [s['B'] for s in prov_ships]
        sizes = [s['drift'] * 50 + 50 for s in prov_ships]  # Size by avg drift

        ax.scatter(xs, ys, c=PROVIDER_COLORS[provider], s=sizes, alpha=0.7,
                  label=f"{provider.title()} ({len(prov_ships)} ships)",
                  edgecolors='black', linewidth=1)

        # Label each ship
        for ship in prov_ships:
            short_name = ship['ship'].replace('claude-', 'c-').replace('gemini-', 'g-').replace('gpt-', 'gpt')
            ax.annotate(short_name, (ship['A'], ship['B']), fontsize=7, alpha=0.7,
                       xytext=(3, 3), textcoords='offset points')

    ax.set_xlabel('Average Pole Density (A)', fontsize=12)
    ax.set_ylabel('Average Zero Density (B)', fontsize=12)
    ax.set_title('RUN 008: Ship Positions in Pole-Zero Space\n(Point Size = Average Drift)',
                fontsize=14, fontweight='bold')
    ax.legend(loc='upper right', fontsize=10)
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_ship_positions.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_ship_positions.png")
    plt.close()

# =============================================================================
# VISUALIZATION 6: Dimension Heatmap by Ship
# =============================================================================
def plot_dimension_heatmap(averages):
    """Create heatmap showing 5D profile for each ship."""
    import matplotlib.colors as mcolors

    # Sort by drift
    sorted_ships = sorted(averages, key=lambda x: x['drift'])

    ship_names = [s['ship'] for s in sorted_ships]
    dims = ['A', 'B', 'C', 'D', 'E']

    # Build matrix
    matrix = np.array([[s[d] for d in dims] for s in sorted_ships])

    # Normalize per column for better visibility
    matrix_norm = (matrix - matrix.min(axis=0)) / (matrix.max(axis=0) - matrix.min(axis=0) + 0.001)

    fig, ax = plt.subplots(figsize=(10, 14))

    im = ax.imshow(matrix_norm, cmap='RdYlGn_r', aspect='auto')

    ax.set_xticks(range(len(dims)))
    ax.set_xticklabels(['Pole (A)', 'Zero (B)', 'Meta (C)', 'Identity (D)', 'Hedging (E)'], fontsize=10)
    ax.set_yticks(range(len(ship_names)))
    ax.set_yticklabels(ship_names, fontsize=8)

    ax.set_xlabel('Dimension', fontsize=12)
    ax.set_ylabel('Ship (sorted by avg drift, stable → volatile)', fontsize=12)
    ax.set_title('RUN 008: 5D Dimension Heatmap by Ship\n(Normalized per dimension)',
                fontsize=14, fontweight='bold')

    cbar = plt.colorbar(im, ax=ax, shrink=0.6)
    cbar.set_label('Relative Intensity (0=low, 1=high)', fontsize=10)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_dimension_heatmap.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_dimension_heatmap.png")
    plt.close()

# =============================================================================
# VISUALIZATION 7: Drift Distribution by Provider (Box Plot)
# =============================================================================
def plot_drift_by_provider(points):
    """Box plot of drift distribution by provider."""
    fig, ax = plt.subplots(figsize=(12, 8))

    provider_drifts = defaultdict(list)
    for p in points:
        provider_drifts[p['provider']].append(p['drift'])

    providers = list(PROVIDER_COLORS.keys())
    data = [provider_drifts.get(p, []) for p in providers]
    colors = [PROVIDER_COLORS[p] for p in providers]

    bp = ax.boxplot(data, labels=[p.title() for p in providers], patch_artist=True)

    for patch, color in zip(bp['boxes'], colors):
        patch.set_facecolor(color)
        patch.set_alpha(0.7)

    ax.set_ylabel('Drift Value', fontsize=12)
    ax.set_xlabel('Provider', fontsize=12)
    ax.set_title('RUN 008: Drift Distribution by Provider\n(All turns, all ships)',
                fontsize=14, fontweight='bold')
    ax.grid(True, alpha=0.3, axis='y')

    # Add stats
    for i, (provider, drifts) in enumerate(zip(providers, data)):
        if drifts:
            stats = f"n={len(drifts)}\nμ={np.mean(drifts):.2f}\nmax={np.max(drifts):.2f}"
            ax.text(i + 1, np.max(drifts) + 0.2, stats, ha='center', fontsize=8, alpha=0.8)

    plt.tight_layout()
    plt.savefig(OUTPUT_DIR / 'run008_drift_by_provider.png', dpi=150, bbox_inches='tight')
    print(f"Saved: run008_drift_by_provider.png")
    plt.close()

# =============================================================================
# MAIN
# =============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("RUN 008 5D IDENTITY MANIFOLD VISUALIZATIONS")
    print("=" * 60)

    print("\nLoading Run 008 data...")
    data = load_run008_data()

    print("Extracting 5D points...")
    all_points = extract_all_points(data)
    print(f"  Total data points: {len(all_points)}")

    print("Calculating ship averages...")
    ship_averages = extract_ship_averages(data)
    print(f"  Ships with data: {len(ship_averages)}")

    print("\nGenerating visualizations...")
    print("-" * 40)

    plot_pole_zero_2d(all_points)
    plot_3d_manifold(all_points)
    plot_4d_manifold(all_points)
    plot_5d_manifold(all_points)
    plot_ship_averages(ship_averages)
    plot_dimension_heatmap(ship_averages)
    plot_drift_by_provider(all_points)

    print("-" * 40)
    print(f"\nAll visualizations saved to: {OUTPUT_DIR}")
    print("=" * 60)
