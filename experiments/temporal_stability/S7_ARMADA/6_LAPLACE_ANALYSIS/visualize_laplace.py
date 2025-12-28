"""
Laplace Analysis Visualization

Creates pole-zero plots and stability analysis visualizations from
the Laplace analysis results.

UPDATED 2025-12-27: Aligned with 4_VISUALIZATION_SPEC.md
- Light mode for publication
- Provider color palette (canonical)
- Effect size reporting (Cohen's d)
- Bootstrap CI ellipses on pole plots
- Log scale for λ when range > 1000x
- Pole migration visualization for A/B comparison

Visualizations:
1. Pole-Zero Map in Complex Plane (with CI ellipses)
2. Lambda Distribution by Provider
3. Stability Classification Heatmap
4. Decay Rate vs Peak Drift scatter
5. Pole Migration Plot (bare_metal → i_am comparison)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Ellipse
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Optional, Tuple

# ============ CONFIG ============

SCRIPT_DIR = Path(__file__).parent
RESULTS_DIR = SCRIPT_DIR / "results"
VIZ_DIR = SCRIPT_DIR.parent / "visualizations" / "pics" / "16_Laplace_Analysis"

# ============ CANONICAL PROVIDER COLORS (from 4_VISUALIZATION_SPEC.md) ============

PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
    'deepseek': '#FF6B35',
    'default': '#888888',
}

def get_provider_color(provider: str) -> str:
    """Get canonical color for provider."""
    return PROVIDER_COLORS.get(provider.lower(), PROVIDER_COLORS['default'])

# ============ EFFECT SIZE CALCULATION ============

def cohens_d(group1: List[float], group2: List[float]) -> float:
    """Calculate Cohen's d effect size between two groups."""
    if not group1 or not group2:
        return 0.0
    pooled_std = np.sqrt((np.var(group1) + np.var(group2)) / 2)
    return (np.mean(group2) - np.mean(group1)) / pooled_std if pooled_std > 0 else 0

def effect_size_label(d: float) -> str:
    """Convert Cohen's d to interpretive label."""
    d = abs(d)
    if d < 0.2:
        return "negligible"
    elif d < 0.5:
        return "small"
    elif d < 0.8:
        return "medium"
    else:
        return "large"

# ============ LIGHT MODE STYLING ============

def apply_light_mode(fig, ax):
    """Apply publication-ready light mode styling to figure/axes."""
    fig.patch.set_facecolor('white')
    ax.set_facecolor('white')
    ax.tick_params(colors='black')
    ax.xaxis.label.set_color('black')
    ax.yaxis.label.set_color('black')
    ax.title.set_color('black')
    for spine in ax.spines.values():
        spine.set_color('#cccccc')
    ax.grid(True, alpha=0.3, color='#cccccc')

# Find results files
def get_latest_results(source: str = None):
    """Get latest results file, optionally filtered by source."""
    if source:
        files = list(RESULTS_DIR.glob(f"laplace_analysis_{source}_*.json"))
    else:
        files = list(RESULTS_DIR.glob("laplace_analysis_*.json"))
    if not files:
        raise FileNotFoundError(f"No laplace analysis results found for source: {source or 'any'}")
    return max(files, key=lambda p: p.stat().st_mtime)

# ============ VISUALIZATION FUNCTIONS ============

def plot_pole_zero_map(results: dict, output_path: Path, show_ci: bool = True):
    """
    Plot poles in the complex plane with provider colors and CI ellipses.

    Left half-plane = stable (Re(s) < 0)
    Right half-plane = unstable (Re(s) > 0)

    Note on imaginary part:
    - Im = 0: Pure exponential decay (monotonic)
    - Im near ±π: Alternating sign behavior (from negative discrete poles)
    - Other Im: True oscillatory dynamics

    Updated 2025-12-27: Provider colors + CI ellipses per 4_VISUALIZATION_SPEC.md
    """
    fig, ax = plt.subplots(figsize=(12, 10))
    apply_light_mode(fig, ax)

    # Collect poles by provider (for canonical colors)
    provider_poles: Dict[str, List[Tuple[float, float, Optional[float], Optional[float]]]] = defaultdict(list)
    n_excluded = 0

    for traj in results["analysis"]["trajectories"]:
        # Skip trajectories where lambda hit the cap - uninformative
        if traj.get("exponential", {}).get("maxed_out", False):
            n_excluded += 1
            continue

        arma = traj.get("arma", {})
        if not arma.get("poles"):
            continue

        provider = traj.get("provider", "default")
        for pole in arma["poles"]:
            # Get CI if available (from bootstrap)
            ci_real = pole.get("ci_real", 0.1)  # Default small CI if not available
            ci_imag = pole.get("ci_imag", 0.1)
            provider_poles[provider].append((pole["real"], pole["imag"], ci_real, ci_imag))

    # Plot poles by provider with CI ellipses
    for provider, poles in provider_poles.items():
        color = get_provider_color(provider)
        xs, ys = [], []
        for real, imag, ci_real, ci_imag in poles:
            xs.append(real)
            ys.append(imag)

            # Draw CI ellipse if enabled
            if show_ci and ci_real > 0 and ci_imag > 0:
                ellipse = Ellipse(
                    (real, imag),
                    width=2 * ci_real,   # 95% CI width
                    height=2 * ci_imag,
                    alpha=0.15,
                    facecolor=color,
                    edgecolor=color,
                    linewidth=0.5
                )
                ax.add_patch(ellipse)

        # Plot pole markers
        ax.scatter(xs, ys, c=color, alpha=0.7, s=30, marker='x',
                   label=f'{provider} ({len(poles)})', linewidths=1.5)

    # Draw imaginary axis (stability boundary)
    ax.axvline(x=0, color='black', linewidth=2, linestyle='--', label='Stability Boundary')
    ax.axhline(y=0, color='#666666', linewidth=1, alpha=0.7)

    # Mark the π line (alternating behavior from negative discrete poles)
    ax.axhline(y=np.pi, color='#4285F4', linewidth=1, linestyle=':', alpha=0.5)
    ax.axhline(y=-np.pi, color='#4285F4', linewidth=1, linestyle=':', alpha=0.5)
    ax.text(-4.8, np.pi + 0.1, 'Im=π (alternating)', fontsize=8, color='#4285F4', alpha=0.7)

    # Shade regions (subtle for publication)
    ax.axvspan(-10, 0, alpha=0.05, color='#2ecc71')
    ax.axvspan(0, 10, alpha=0.05, color='#e74c3c')
    ax.text(-4.5, 3.5, 'STABLE', fontsize=10, color='#2ecc71', alpha=0.7, fontweight='bold')
    ax.text(0.3, 3.5, 'UNSTABLE', fontsize=10, color='#e74c3c', alpha=0.7, fontweight='bold')

    ax.set_xlim(-5, 2)
    ax.set_ylim(-4, 4)
    ax.set_xlabel('Real Part (σ) - Decay Rate\n(more negative = faster decay)', fontsize=12, color='black')
    ax.set_ylabel('Imaginary Part (ω) - Oscillation Frequency\n(Im=0: monotonic, Im=±π: alternating)', fontsize=12, color='black')
    title = 'ARMA Pole Locations in Complex Plane\n(Laplace Domain Analysis of Identity Drift)'
    if n_excluded > 0:
        title += f'\n({n_excluded} maxed-out trajectories excluded)'
    ax.set_title(title, fontsize=14, color='black')
    ax.legend(loc='upper right', fontsize=9)

    # Add interpretation note
    note = "Im=0: smooth recovery | Im near ±π: sign-alternating | Other: oscillatory"
    ax.text(0.5, -0.12, note, transform=ax.transAxes, fontsize=9,
            ha='center', style='italic', color='#666666')

    plt.tight_layout()
    # Save both PNG and SVG for publication
    for ext in ['png', 'svg']:
        path = output_path.with_suffix(f'.{ext}')
        plt.savefig(path, dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"[OK] Saved: {output_path} (+ SVG)")

def plot_lambda_by_provider(results: dict, output_path: Path):
    """
    Box plot of decay rate (λ) by provider.
    Higher λ = faster recovery = more stable.

    Updated 2025-12-27: Provider colors + light mode + log scale option
    """
    provider_lambdas = defaultdict(list)

    for traj in results["analysis"]["trajectories"]:
        lam = traj.get("exponential", {}).get("lambda")
        if lam is not None and lam < 5:  # Exclude capped values
            provider_lambdas[traj["provider"]].append(lam)

    # Sort by median lambda
    providers = sorted(provider_lambdas.keys(),
                      key=lambda p: np.median(provider_lambdas[p]) if provider_lambdas[p] else 0,
                      reverse=True)

    fig, ax = plt.subplots(figsize=(14, 8))
    apply_light_mode(fig, ax)

    data = [provider_lambdas[p] for p in providers]
    positions = range(len(providers))

    bp = ax.boxplot(data, positions=positions, vert=True, patch_artist=True)

    # Color boxes by provider (canonical colors)
    for i, (patch, provider) in enumerate(zip(bp['boxes'], providers)):
        color = get_provider_color(provider)
        patch.set_facecolor(color)
        patch.set_alpha(0.7)
        patch.set_edgecolor('#333333')

    # Style whiskers and medians
    for element in ['whiskers', 'caps', 'medians']:
        plt.setp(bp[element], color='#333333')
    plt.setp(bp['fliers'], markerfacecolor='#888888', marker='o', markersize=4, alpha=0.5)

    ax.set_xticks(positions)
    ax.set_xticklabels([p[:15] for p in providers], rotation=45, ha='right', color='black')
    ax.set_ylabel('Decay Rate λ (higher = faster recovery)', fontsize=12, color='black')
    ax.set_xlabel('Provider', fontsize=12, color='black')
    ax.set_title('Identity Recovery Rate by Provider\n(Exponential Decay Analysis)', fontsize=14, color='black')
    ax.axhline(y=0.1, color='#f39c12', linestyle='--', alpha=0.7, label='Marginal threshold')
    ax.axhline(y=0.3, color='#2ecc71', linestyle='--', alpha=0.7, label='Stable threshold')
    ax.legend()

    # Check if log scale needed (range > 1000x)
    all_lambdas = [l for lams in provider_lambdas.values() for l in lams]
    if all_lambdas:
        lambda_range = max(all_lambdas) / max(min(all_lambdas), 0.001)
        if lambda_range > 1000:
            ax.set_yscale('log')
            ax.set_ylabel('Decay Rate λ (Log Scale)', fontsize=12, color='black')

    plt.tight_layout()
    for ext in ['png', 'svg']:
        path = output_path.with_suffix(f'.{ext}')
        plt.savefig(path, dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"[OK] Saved: {output_path} (+ SVG)")

def plot_stability_heatmap(results: dict, output_path: Path):
    """
    Heatmap of stability classification by model and provider.
    """
    # Aggregate by model
    model_stats = defaultdict(lambda: {"STABLE": 0, "MARGINAL": 0, "UNSTABLE": 0, "UNKNOWN": 0})

    for traj in results["analysis"]["trajectories"]:
        model = traj["ship"][:20]  # Truncate long names
        stability = traj["classification"]["stability"]
        model_stats[model][stability] += 1

    # Sort by stability ratio
    def stability_score(model):
        stats = model_stats[model]
        total = sum(stats.values())
        if total == 0:
            return 0
        return (stats["STABLE"] * 3 + stats["MARGINAL"]) / total

    models = sorted(model_stats.keys(), key=stability_score, reverse=True)[:25]  # Top 25

    # Build matrix
    categories = ["STABLE", "MARGINAL", "UNSTABLE", "UNKNOWN"]
    matrix = []
    for model in models:
        total = sum(model_stats[model].values())
        row = [model_stats[model][cat] / total * 100 if total > 0 else 0 for cat in categories]
        matrix.append(row)

    fig, ax = plt.subplots(figsize=(10, 12))

    im = ax.imshow(matrix, cmap='RdYlGn', aspect='auto', vmin=0, vmax=100)

    ax.set_xticks(range(len(categories)))
    ax.set_xticklabels(categories)
    ax.set_yticks(range(len(models)))
    ax.set_yticklabels(models)

    # Add text annotations
    for i in range(len(models)):
        for j in range(len(categories)):
            text = f"{matrix[i][j]:.0f}%"
            color = 'white' if matrix[i][j] > 50 or matrix[i][j] < 20 else 'black'
            ax.text(j, i, text, ha='center', va='center', color=color, fontsize=8)

    ax.set_title('Pole Stability Classification by Model\n(% of trajectories)', fontsize=14)
    plt.colorbar(im, ax=ax, label='Percentage')

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"[OK] Saved: {output_path}")

def plot_decay_vs_peak_drift(results: dict, output_path: Path):
    """
    Scatter plot: Decay rate vs Peak drift.

    Hypothesis: Higher peak drift should correlate with slower recovery (lower λ).
    """
    lambdas = []
    peak_drifts = []
    providers = []

    for traj in results["analysis"]["trajectories"]:
        lam = traj.get("exponential", {}).get("lambda")
        peak = traj.get("peak_drift")
        if lam is not None and lam < 5 and peak is not None:
            lambdas.append(lam)
            peak_drifts.append(peak)
            providers.append(traj["provider"])

    fig, ax = plt.subplots(figsize=(12, 8))

    # Color by provider
    unique_providers = list(set(providers))
    colors = plt.cm.tab10(np.linspace(0, 1, len(unique_providers)))
    provider_colors = {p: colors[i] for i, p in enumerate(unique_providers)}

    for provider in unique_providers:
        mask = [p == provider for p in providers]
        xs = [peak_drifts[i] for i in range(len(mask)) if mask[i]]
        ys = [lambdas[i] for i in range(len(mask)) if mask[i]]
        ax.scatter(xs, ys, c=[provider_colors[provider]], alpha=0.5, s=20, label=provider[:15])

    # Add Event Horizon line
    ax.axvline(x=0.80, color='red', linestyle='--', linewidth=2, label='Event Horizon (0.80)')

    # Add stability thresholds
    ax.axhline(y=0.1, color='orange', linestyle=':', alpha=0.7, label='Marginal λ threshold')

    ax.set_xlabel('Peak Drift (cosine distance)', fontsize=12)
    ax.set_ylabel('Recovery Rate λ', fontsize=12)
    ax.set_title('Recovery Rate vs Peak Drift\n(Does crossing Event Horizon slow recovery?)', fontsize=14)
    ax.legend(loc='upper right', fontsize=8)
    ax.grid(True, alpha=0.3)

    # Calculate correlation
    if len(lambdas) > 2:
        corr = np.corrcoef(peak_drifts, lambdas)[0, 1]
        ax.text(0.02, 0.98, f'Correlation: {corr:.3f}', transform=ax.transAxes,
                fontsize=10, verticalalignment='top',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"[OK] Saved: {output_path}")

def plot_lambda_histogram(results: dict, output_path: Path):
    """
    Histogram of decay rates with stability zones marked.
    """
    lambdas = []
    for traj in results["analysis"]["trajectories"]:
        lam = traj.get("exponential", {}).get("lambda")
        if lam is not None and lam < 5:
            lambdas.append(lam)

    fig, ax = plt.subplots(figsize=(12, 6))

    # Histogram
    n, bins, patches = ax.hist(lambdas, bins=50, edgecolor='black', alpha=0.7)

    # Color bars by stability
    for i, patch in enumerate(patches):
        bin_center = (bins[i] + bins[i+1]) / 2
        if bin_center < 0.1:
            patch.set_facecolor('#e74c3c')  # Red - marginal/unstable
        elif bin_center < 0.3:
            patch.set_facecolor('#f39c12')  # Orange
        else:
            patch.set_facecolor('#2ecc71')  # Green - stable

    # Add stability zones
    ax.axvline(x=0.1, color='orange', linestyle='--', linewidth=2, label='Marginal threshold')
    ax.axvline(x=0.3, color='green', linestyle='--', linewidth=2, label='Stable threshold')

    ax.set_xlabel('Decay Rate λ', fontsize=12)
    ax.set_ylabel('Count', fontsize=12)
    ax.set_title('Distribution of Identity Recovery Rates\n(Exponential Decay Analysis)', fontsize=14)
    ax.legend()

    # Add statistics
    stats_text = f'Mean: {np.mean(lambdas):.3f}\nMedian: {np.median(lambdas):.3f}\nStd: {np.std(lambdas):.3f}'
    ax.text(0.98, 0.98, stats_text, transform=ax.transAxes, fontsize=10,
            verticalalignment='top', horizontalalignment='right',
            bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    plt.tight_layout()
    for ext in ['png', 'svg']:
        path = output_path.with_suffix(f'.{ext}')
        plt.savefig(path, dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"[OK] Saved: {output_path} (+ SVG)")


def plot_pole_migration(bare_results: dict, iam_results: dict, output_path: Path):
    """
    Show how I_AM specification shifts poles in complex plane.

    Draws arrows from bare_metal pole locations to i_am pole locations
    for each model, colored by provider.

    NEW 2025-12-27: For JADE LATTICE A/B comparison visualization.
    """
    fig, ax = plt.subplots(figsize=(14, 10))
    apply_light_mode(fig, ax)

    # Build lookup: ship -> (provider, poles) for each condition
    bare_poles = {}
    for traj in bare_results.get("analysis", {}).get("trajectories", []):
        if traj.get("exponential", {}).get("maxed_out", False):
            continue
        arma = traj.get("arma", {})
        if arma.get("poles"):
            ship = traj["ship"]
            provider = traj.get("provider", "default")
            # Take dominant pole (first one)
            pole = arma["poles"][0]
            bare_poles[ship] = (provider, complex(pole["real"], pole["imag"]))

    iam_poles = {}
    for traj in iam_results.get("analysis", {}).get("trajectories", []):
        if traj.get("exponential", {}).get("maxed_out", False):
            continue
        arma = traj.get("arma", {})
        if arma.get("poles"):
            ship = traj["ship"]
            provider = traj.get("provider", "default")
            pole = arma["poles"][0]
            iam_poles[ship] = (provider, complex(pole["real"], pole["imag"]))

    # Draw migration arrows
    bare_reals, iam_reals = [], []
    for ship, (provider, bare_pole) in bare_poles.items():
        if ship not in iam_poles:
            continue
        _, iam_pole = iam_poles[ship]
        color = get_provider_color(provider)

        bare_reals.append(bare_pole.real)
        iam_reals.append(iam_pole.real)

        # Draw arrow from bare to i_am
        ax.annotate(
            '',
            xy=(iam_pole.real, iam_pole.imag),
            xytext=(bare_pole.real, bare_pole.imag),
            arrowprops=dict(
                arrowstyle='->',
                color=color,
                lw=1.5,
                alpha=0.7
            )
        )

        # Mark start (bare) and end (i_am)
        ax.scatter(bare_pole.real, bare_pole.imag, c=color, marker='o', s=40, alpha=0.5, zorder=5)
        ax.scatter(iam_pole.real, iam_pole.imag, c=color, marker='x', s=60, alpha=0.9, zorder=6, linewidths=2)

    # Draw stability boundary
    ax.axvline(x=0, color='black', linewidth=2, linestyle='--', label='Stability Boundary')
    ax.axhline(y=0, color='#666666', linewidth=1, alpha=0.7)

    # Shade regions
    ax.axvspan(-10, 0, alpha=0.05, color='#2ecc71')
    ax.axvspan(0, 10, alpha=0.05, color='#e74c3c')

    ax.set_xlim(-5, 2)
    ax.set_ylim(-4, 4)
    ax.set_xlabel('Real Part (σ) - Decay Rate', fontsize=12, color='black')
    ax.set_ylabel('Imaginary Part (ω) - Oscillation', fontsize=12, color='black')

    # Calculate and report effect size
    if bare_reals and iam_reals:
        d = cohens_d(bare_reals, iam_reals)
        effect_label_str = effect_size_label(d)
        direction = "leftward (more stable)" if d < 0 else "rightward (less stable)"
        title = f"Pole Migration: bare_metal → I_AM\n"
        title += f"(Cohen's d = {d:.3f}, {effect_label_str} effect, {direction})"
    else:
        title = "Pole Migration: bare_metal → I_AM\n(No matching trajectories found)"

    ax.set_title(title, fontsize=14, color='black')

    # Legend for markers
    ax.scatter([], [], c='gray', marker='o', s=40, label='bare_metal (start)')
    ax.scatter([], [], c='gray', marker='x', s=60, label='i_am (end)', linewidths=2)
    ax.legend(loc='upper right', fontsize=9)

    # Add provider legend
    for provider in set(p for p, _ in bare_poles.values()):
        color = get_provider_color(provider)
        ax.plot([], [], color=color, linewidth=2, label=provider)

    plt.tight_layout()
    for ext in ['png', 'svg']:
        path = output_path.with_suffix(f'.{ext}')
        plt.savefig(path, dpi=150, facecolor='white', bbox_inches='tight')
    plt.close()
    print(f"[OK] Saved: {output_path} (+ SVG)")


# ============ MAIN ============

def main(source: str = None):
    """
    Generate visualizations from Laplace analysis results.

    Args:
        source: Filter by source (e.g., "023", "020B", "023b")
    """
    print("="*60)
    print("LAPLACE ANALYSIS VISUALIZATION")
    print("="*60)

    # Ensure output directory exists
    VIZ_DIR.mkdir(parents=True, exist_ok=True)

    # Load results
    results_file = get_latest_results(source)
    print(f"Loading: {results_file.name}")
    with open(results_file) as f:
        results = json.load(f)

    print(f"Trajectories: {results['analysis']['n_trajectories']}")
    print(f"Methodology: {results['methodology']}")
    print(f"Event Horizon: {results['event_horizon']}")
    print()

    # Generate visualizations
    print("Generating visualizations...")

    plot_pole_zero_map(results, VIZ_DIR / "pole_zero_map.png")
    plot_lambda_by_provider(results, VIZ_DIR / "lambda_by_provider.png")
    plot_stability_heatmap(results, VIZ_DIR / "stability_heatmap.png")
    plot_decay_vs_peak_drift(results, VIZ_DIR / "decay_vs_peak_drift.png")
    plot_lambda_histogram(results, VIZ_DIR / "lambda_histogram.png")

    print()
    print("="*60)
    print(f"All visualizations saved to: {VIZ_DIR}")
    print("="*60)

if __name__ == "__main__":
    main()
