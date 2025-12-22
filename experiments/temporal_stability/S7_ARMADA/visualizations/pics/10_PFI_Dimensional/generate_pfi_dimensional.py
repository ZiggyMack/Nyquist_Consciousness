#!/usr/bin/env python3
"""
10_PFI_Dimensional: Cosine-Based Identity Validation Analysis
==============================================================
Recreates the archive's PFI dimensional validation using cosine distance methodology.

Three phases:
- Phase 2: PCA dimensionality analysis (variance curve, PC scatter, provider clusters, EH contour)
- Phase 3A: Perturbation validation (surface vs deep comparison)
- Phase 3B: Cross-model comparison (Cohen's d effect size)

Data source: Run 023d (IRON CLAD Foundation - 750 experiments)
Metric: Cosine distance (Event Horizon = 0.80)
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict
from sklearn.decomposition import PCA
from sklearn.metrics import silhouette_score
from scipy import stats
import warnings
warnings.filterwarnings('ignore')

# Paths
RESULTS_DIR = Path(__file__).parent.parent.parent.parent / "15_IRON_CLAD_FOUNDATION" / "results"
OUTPUT_DIR = Path(__file__).parent

# Constants
EVENT_HORIZON = 0.80  # Cosine distance threshold

# Provider colors
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'xai': '#1DA1F2',
    'together': '#7C3AED',
}

PROVIDER_DISPLAY = {
    'anthropic': 'Anthropic',
    'openai': 'OpenAI',
    'google': 'Google',
    'xai': 'xAI',
    'together': 'Together.ai',
}


def load_data():
    """Load Run 023d results."""
    data_file = RESULTS_DIR / "S7_run_023d_CURRENT.json"
    with open(data_file) as f:
        data = json.load(f)
    return data.get('results', [])


def extract_drift_features(results):
    """
    Extract multi-dimensional drift features from each experiment.

    Features per experiment:
    - peak_drift: Maximum cosine distance reached
    - settled_drift: Final settled cosine distance
    - settling_time: Number of probes to settle
    - overshoot_ratio: peak/settled ratio
    - ringback_count: Number of direction changes
    """
    features = []
    metadata = []

    for r in results:
        feat = [
            r.get('peak_drift', 0),
            r.get('settled_drift', 0),
            r.get('settling_time', 0) / 20.0,  # Normalize to 0-1
            r.get('overshoot_ratio', 1),
            r.get('ringback_count', 0) / 20.0,  # Normalize
        ]
        features.append(feat)
        metadata.append({
            'model': r.get('model', 'unknown'),
            'provider': r.get('provider', 'unknown'),
            'naturally_settled': r.get('naturally_settled', False),
        })

    return np.array(features), metadata


def extract_probe_drifts(results):
    """Extract drift values at each probe type for perturbation analysis."""
    data = []
    for r in results:
        probes = r.get('probe_sequence', [])

        baseline_drifts = []
        step_input_drifts = []
        recovery_drifts = []

        for p in probes:
            ptype = p.get('probe_type', 'unknown')
            drift = p.get('drift', 0)

            if ptype == 'baseline':
                baseline_drifts.append(drift)
            elif ptype == 'step_input':
                step_input_drifts.append(drift)
            elif ptype == 'recovery':
                recovery_drifts.append(drift)

        data.append({
            'model': r.get('model', 'unknown'),
            'provider': r.get('provider', 'unknown'),
            'baseline_drifts': baseline_drifts,
            'step_input_drifts': step_input_drifts,  # Deep perturbation
            'recovery_drifts': recovery_drifts,  # Surface perturbation
            'peak_drift': r.get('peak_drift', 0),
            'settled_drift': r.get('settled_drift', 0),
        })

    return data


# =============================================================================
# PHASE 2: PCA DIMENSIONALITY ANALYSIS
# =============================================================================

def generate_phase2_pca(features, metadata):
    """Generate Phase 2 PCA visualizations."""
    print("\n[PHASE 2] Generating PCA Dimensionality Analysis...")

    output_dir = OUTPUT_DIR / "phase2_pca"
    output_dir.mkdir(parents=True, exist_ok=True)

    # Perform PCA
    pca = PCA()
    pca.fit(features)
    transformed = pca.transform(features)

    # Get provider labels
    providers = [m['provider'] for m in metadata]
    unique_providers = list(set(providers))

    # 1. Variance Curve
    generate_variance_curve(pca, output_dir)

    # 2. PC Scatter
    generate_pc_scatter(transformed, metadata, output_dir)

    # 3. Provider Clusters
    generate_provider_clusters(transformed, metadata, output_dir)

    # 4. Event Horizon Contour
    generate_eh_contour(features, transformed, metadata, output_dir)

    # Calculate silhouette score
    if len(unique_providers) > 1:
        labels = [unique_providers.index(p) for p in providers]
        sil_score = silhouette_score(transformed[:, :2], labels)
        print(f"  Silhouette Score: {sil_score:.4f}")

    return pca, transformed


def generate_variance_curve(pca, output_dir):
    """Generate cumulative explained variance curve."""
    fig, ax = plt.subplots(figsize=(10, 6))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    cumvar = np.cumsum(pca.explained_variance_ratio_)
    n_components = len(cumvar)

    ax.plot(range(1, n_components + 1), cumvar, 'o-', color='#00ff88',
            linewidth=2, markersize=6)

    # Mark 90% threshold
    idx_90 = np.argmax(cumvar >= 0.90) + 1
    ax.axhline(y=0.90, color='#ff4444', linestyle='--', linewidth=2,
               alpha=0.8, label=f'90% threshold')
    ax.axhline(y=0.95, color='#ffaa00', linestyle='--', linewidth=1.5,
               alpha=0.6, label='95% threshold')

    ax.axvline(x=idx_90, color='#ff4444', linestyle=':', alpha=0.5)
    ax.annotate(f'90%: {idx_90} PCs', xy=(idx_90, 0.90),
                xytext=(idx_90 + 0.5, 0.85),
                fontsize=11, color='white',
                arrowprops=dict(arrowstyle='->', color='white', alpha=0.5))

    ax.set_xlabel('Number of Principal Components', fontsize=12, color='white')
    ax.set_ylabel('Cumulative Variance Explained', fontsize=12, color='white')
    ax.set_title('Identity Dimensionality: How Many Dimensions Carry Signal?\n' +
                 '(Low value = identity is low-dimensional, structured)',
                 fontsize=13, color='white', fontweight='bold')

    ax.legend(facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white')
    ax.grid(True, alpha=0.3, color='#333355')
    ax.tick_params(colors='white')
    ax.set_xlim(0, n_components + 1)
    ax.set_ylim(0, 1.05)

    for spine in ax.spines.values():
        spine.set_color('#333355')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'variance_curve.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: variance_curve.png")
    plt.close()


def generate_pc_scatter(transformed, metadata, output_dir):
    """Generate PC1 vs PC2 scatter plot."""
    fig, ax = plt.subplots(figsize=(10, 8))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    providers = [m['provider'] for m in metadata]
    peak_drifts = [m.get('peak_drift', 0) for m in metadata]

    for provider in set(providers):
        mask = [p == provider for p in providers]
        idx = [i for i, m in enumerate(mask) if m]

        x = transformed[idx, 0]
        y = transformed[idx, 1]

        color = PROVIDER_COLORS.get(provider, '#888888')
        display = PROVIDER_DISPLAY.get(provider, provider)

        ax.scatter(x, y, c=color, label=display, alpha=0.7, s=50, edgecolor='white', linewidth=0.3)

    ax.set_xlabel('PC1', fontsize=12, color='white')
    ax.set_ylabel('PC2', fontsize=12, color='white')
    ax.set_title('Identity Space: Experiments in Principal Component Space\n' +
                 '(Clusters = provider-specific identity regions)',
                 fontsize=13, color='white', fontweight='bold')

    ax.legend(facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white', loc='upper right')
    ax.grid(True, alpha=0.3, color='#333355')
    ax.tick_params(colors='white')

    for spine in ax.spines.values():
        spine.set_color('#333355')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'pc_scatter.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: pc_scatter.png")
    plt.close()


def generate_provider_clusters(transformed, metadata, output_dir):
    """Generate provider clustering visualization with centroids."""
    fig, ax = plt.subplots(figsize=(10, 8))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    providers = [m['provider'] for m in metadata]

    # Calculate centroids and spreads
    for provider in set(providers):
        mask = [p == provider for p in providers]
        idx = [i for i, m in enumerate(mask) if m]

        x = transformed[idx, 0]
        y = transformed[idx, 1]

        color = PROVIDER_COLORS.get(provider, '#888888')
        display = PROVIDER_DISPLAY.get(provider, provider)

        # Plot points
        ax.scatter(x, y, c=color, alpha=0.4, s=30, edgecolor='none')

        # Plot centroid
        cx, cy = np.mean(x), np.mean(y)
        ax.scatter(cx, cy, c=color, s=200, marker='X', edgecolor='white',
                   linewidth=2, zorder=10, label=f'{display} centroid')

        # Plot error ellipse (1 std)
        std_x, std_y = np.std(x), np.std(y)
        ellipse = plt.matplotlib.patches.Ellipse(
            (cx, cy), std_x * 2, std_y * 2, fill=False,
            color=color, linewidth=2, linestyle='--', alpha=0.7
        )
        ax.add_patch(ellipse)

    # Calculate silhouette
    unique_providers = list(set(providers))
    labels = [unique_providers.index(p) for p in providers]
    sil_score = silhouette_score(transformed[:, :2], labels)

    ax.set_xlabel('PC1', fontsize=12, color='white')
    ax.set_ylabel('PC2', fontsize=12, color='white')
    ax.set_title(f'Provider Clustering (Silhouette: {sil_score:.3f})\n' +
                 '(Centroids with 1-std ellipses)',
                 fontsize=13, color='white', fontweight='bold')

    ax.legend(facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white',
              loc='upper right', fontsize=9)
    ax.grid(True, alpha=0.3, color='#333355')
    ax.tick_params(colors='white')

    for spine in ax.spines.values():
        spine.set_color('#333355')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'provider_clusters.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: provider_clusters.png (Silhouette: {sil_score:.3f})")
    plt.close()


def generate_eh_contour(features, transformed, metadata, output_dir):
    """Generate Event Horizon contour in PC space."""
    fig, ax = plt.subplots(figsize=(10, 8))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    providers = [m['provider'] for m in metadata]

    # Get peak drift for each point
    peak_drifts = features[:, 0]  # First feature is peak_drift

    # Plot points colored by drift magnitude
    above_eh = peak_drifts > EVENT_HORIZON
    below_eh = ~above_eh

    # Plot below EH (stable)
    sc1 = ax.scatter(transformed[below_eh, 0], transformed[below_eh, 1],
                     c=peak_drifts[below_eh], cmap='viridis', s=50,
                     alpha=0.7, edgecolor='white', linewidth=0.3,
                     vmin=0, vmax=1.2)

    # Plot above EH (volatile) with different marker
    sc2 = ax.scatter(transformed[above_eh, 0], transformed[above_eh, 1],
                     c=peak_drifts[above_eh], cmap='viridis', s=80,
                     alpha=0.9, edgecolor='#ff4444', linewidth=2,
                     marker='s', vmin=0, vmax=1.2)

    cbar = plt.colorbar(sc1, ax=ax, label='Peak Drift (Cosine Distance)')
    cbar.ax.yaxis.label.set_color('white')
    cbar.ax.tick_params(colors='white')

    # Add EH indicator to legend
    ax.scatter([], [], c='gray', s=50, edgecolor='white', label=f'Stable (< {EVENT_HORIZON})')
    ax.scatter([], [], c='gray', s=80, edgecolor='#ff4444', linewidth=2,
               marker='s', label=f'Volatile (>= {EVENT_HORIZON})')

    ax.set_xlabel('PC1', fontsize=12, color='white')
    ax.set_ylabel('PC2', fontsize=12, color='white')
    ax.set_title(f'Event Horizon ({EVENT_HORIZON}) in PC Space\n' +
                 f'(Red border = volatile, crossed EH)',
                 fontsize=13, color='white', fontweight='bold')

    ax.legend(facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white', loc='upper right')
    ax.grid(True, alpha=0.3, color='#333355')
    ax.tick_params(colors='white')

    for spine in ax.spines.values():
        spine.set_color('#333355')

    # Add stats
    n_stable = np.sum(below_eh)
    n_volatile = np.sum(above_eh)
    pct_stable = 100 * n_stable / len(peak_drifts)
    ax.text(0.02, 0.98, f'Stable: {n_stable} ({pct_stable:.1f}%)\nVolatile: {n_volatile}',
            transform=ax.transAxes, fontsize=10, color='white',
            verticalalignment='top', bbox=dict(boxstyle='round', facecolor='#1a1a2e', alpha=0.8))

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'event_horizon_contour.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: event_horizon_contour.png")
    plt.close()


# =============================================================================
# PHASE 3A: PERTURBATION VALIDATION
# =============================================================================

def generate_phase3a_perturbation(probe_data):
    """Generate Phase 3A perturbation validation visualizations."""
    print("\n[PHASE 3A] Generating Perturbation Validation...")

    output_dir = OUTPUT_DIR / "phase3a_synthetic"
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Perturbation Comparison (Deep vs Surface)
    generate_perturbation_comparison(probe_data, output_dir)

    # 2. EH Crossings
    generate_eh_crossings(probe_data, output_dir)

    # 3. Ship Comparison
    generate_ship_comparison(probe_data, output_dir)


def generate_perturbation_comparison(probe_data, output_dir):
    """Compare drift from deep (step_input) vs surface (recovery) perturbations."""
    fig, ax = plt.subplots(figsize=(10, 7))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    # Collect drift by perturbation type
    deep_drifts = []  # step_input
    surface_drifts = []  # first recovery after step

    for d in probe_data:
        if d['step_input_drifts']:
            deep_drifts.extend(d['step_input_drifts'])
        if d['recovery_drifts']:
            # First recovery shows immediate response to "surface" re-grounding
            surface_drifts.append(d['recovery_drifts'][0])

    # Create box plot
    data = [surface_drifts, deep_drifts]
    positions = [1, 2]

    bp = ax.boxplot(data, positions=positions, patch_artist=True, widths=0.6)

    colors = ['#4285F4', '#E07B53']  # Surface=blue, Deep=orange
    for patch, color in zip(bp['boxes'], colors):
        patch.set_facecolor(color)
        patch.set_alpha(0.7)

    for element in ['whiskers', 'caps', 'medians']:
        for item in bp[element]:
            item.set_color('white')
    bp['fliers'][0].set_markeredgecolor('white')
    bp['fliers'][1].set_markeredgecolor('white')

    # Event Horizon line
    ax.axhline(y=EVENT_HORIZON, color='#ff4444', linestyle='--', linewidth=2,
               alpha=0.8, label=f'Event Horizon ({EVENT_HORIZON})')

    ax.set_xticks(positions)
    ax.set_xticklabels(['Surface\n(Recovery Probes)', 'Deep\n(Step Input)'],
                       fontsize=11, color='white')
    ax.set_ylabel('Cosine Distance (Drift)', fontsize=12, color='white')
    ax.set_title('Perturbation Type Comparison\n' +
                 '(Deep > Surface = cosine measures meaning, not vocabulary)',
                 fontsize=13, color='white', fontweight='bold')

    ax.legend(facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white')
    ax.grid(True, alpha=0.3, axis='y', color='#333355')
    ax.tick_params(colors='white')

    for spine in ax.spines.values():
        spine.set_color('#333355')

    # Add stats
    surface_mean = np.mean(surface_drifts)
    deep_mean = np.mean(deep_drifts)
    t_stat, p_value = stats.ttest_ind(deep_drifts, surface_drifts)

    ax.text(0.02, 0.98, f'Surface mean: {surface_mean:.3f}\nDeep mean: {deep_mean:.3f}\n' +
            f't-test p={p_value:.2e}',
            transform=ax.transAxes, fontsize=10, color='white',
            verticalalignment='top', bbox=dict(boxstyle='round', facecolor='#1a1a2e', alpha=0.8))

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'perturbation_comparison.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: perturbation_comparison.png (p={p_value:.2e})")
    plt.close()


def generate_eh_crossings(probe_data, output_dir):
    """Show Event Horizon crossing rates by perturbation type."""
    fig, ax = plt.subplots(figsize=(10, 7))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    # Count EH crossings
    deep_total = 0
    deep_crossings = 0
    surface_total = 0
    surface_crossings = 0

    for d in probe_data:
        for drift in d['step_input_drifts']:
            deep_total += 1
            if drift >= EVENT_HORIZON:
                deep_crossings += 1

        for drift in d['recovery_drifts']:
            surface_total += 1
            if drift >= EVENT_HORIZON:
                surface_crossings += 1

    # Calculate rates
    deep_rate = deep_crossings / max(deep_total, 1)
    surface_rate = surface_crossings / max(surface_total, 1)

    # Bar chart
    categories = ['Surface\n(Recovery)', 'Deep\n(Step Input)']
    rates = [surface_rate * 100, deep_rate * 100]
    colors = ['#4285F4', '#E07B53']

    bars = ax.bar(categories, rates, color=colors, alpha=0.8, edgecolor='white', linewidth=0.5)

    # Add value labels on bars
    for bar, rate in zip(bars, rates):
        ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 1,
                f'{rate:.1f}%', ha='center', va='bottom', fontsize=12, color='white')

    ax.set_ylabel('EH Crossing Rate (%)', fontsize=12, color='white')
    ax.set_title('Event Horizon Crossings by Perturbation Type\n' +
                 '(Higher = more identity disruption)',
                 fontsize=13, color='white', fontweight='bold')

    ax.grid(True, alpha=0.3, axis='y', color='#333355')
    ax.tick_params(colors='white')
    ax.set_ylim(0, max(rates) * 1.2)

    for spine in ax.spines.values():
        spine.set_color('#333355')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'eh_crossings.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: eh_crossings.png (Deep: {deep_rate*100:.1f}%, Surface: {surface_rate*100:.1f}%)")
    plt.close()


def generate_ship_comparison(probe_data, output_dir):
    """Show per-model response to perturbations."""
    fig, ax = plt.subplots(figsize=(12, 8))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    # Aggregate by model
    model_stats = defaultdict(lambda: {'deep': [], 'surface': [], 'provider': None})

    for d in probe_data:
        model = d['model']
        provider = d['provider']
        model_stats[model]['provider'] = provider

        if d['step_input_drifts']:
            model_stats[model]['deep'].extend(d['step_input_drifts'])
        if d['recovery_drifts']:
            model_stats[model]['surface'].extend(d['recovery_drifts'])

    # Plot each model
    for model, stats_data in model_stats.items():
        if not stats_data['deep'] or not stats_data['surface']:
            continue

        deep_mean = np.mean(stats_data['deep'])
        surface_mean = np.mean(stats_data['surface'])
        provider = stats_data['provider']
        color = PROVIDER_COLORS.get(provider, '#888888')

        ax.scatter(surface_mean, deep_mean, c=color, s=100, alpha=0.7,
                   edgecolor='white', linewidth=0.5)

    # Diagonal line (Deep = Surface)
    ax.plot([0, 1.2], [0, 1.2], '--', color='white', alpha=0.5, label='Equal line')

    # EH lines
    ax.axhline(y=EVENT_HORIZON, color='#ff4444', linestyle=':', alpha=0.5)
    ax.axvline(x=EVENT_HORIZON, color='#ff4444', linestyle=':', alpha=0.5)

    # Legend for providers
    for provider in set(d['provider'] for d in probe_data):
        color = PROVIDER_COLORS.get(provider, '#888888')
        display = PROVIDER_DISPLAY.get(provider, provider)
        ax.scatter([], [], c=color, s=100, label=display, alpha=0.7)

    ax.set_xlabel('Surface Drift (Recovery Probes)', fontsize=12, color='white')
    ax.set_ylabel('Deep Drift (Step Input)', fontsize=12, color='white')
    ax.set_title('Surface vs Deep Drift by Model\n' +
                 '(Points above diagonal = Deep > Surface)',
                 fontsize=13, color='white', fontweight='bold')

    ax.legend(facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white', loc='lower right')
    ax.grid(True, alpha=0.3, color='#333355')
    ax.tick_params(colors='white')
    ax.set_xlim(0, 1.2)
    ax.set_ylim(0, 1.2)

    for spine in ax.spines.values():
        spine.set_color('#333355')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'ship_comparison.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: ship_comparison.png")
    plt.close()


# =============================================================================
# PHASE 3B: CROSS-MODEL COMPARISON
# =============================================================================

def generate_phase3b_crossmodel(probe_data, results):
    """Generate Phase 3B cross-model comparison visualizations."""
    print("\n[PHASE 3B] Generating Cross-Model Comparison...")

    output_dir = OUTPUT_DIR / "phase3b_crossmodel"
    output_dir.mkdir(parents=True, exist_ok=True)

    # 1. Cross-model comparison (within vs cross provider)
    cohens_d = generate_cross_model_comparison(probe_data, results, output_dir)

    # 2. Cross-model histogram
    generate_cross_model_histogram(probe_data, results, output_dir)

    # 3. Provider matrix
    generate_provider_matrix(probe_data, results, output_dir)

    return cohens_d


def calculate_within_cross_distances(results):
    """Calculate within-provider and cross-provider drift distances."""
    # Group results by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        by_provider[provider].append(r.get('peak_drift', 0))

    # Within-provider: variance within each provider
    within_distances = []
    for provider, drifts in by_provider.items():
        if len(drifts) > 1:
            # Pairwise differences within provider
            for i in range(len(drifts)):
                for j in range(i+1, len(drifts)):
                    within_distances.append(abs(drifts[i] - drifts[j]))

    # Cross-provider: differences between providers
    cross_distances = []
    providers = list(by_provider.keys())
    for i in range(len(providers)):
        for j in range(i+1, len(providers)):
            for d1 in by_provider[providers[i]][:20]:  # Limit for speed
                for d2 in by_provider[providers[j]][:20]:
                    cross_distances.append(abs(d1 - d2))

    return within_distances, cross_distances


def generate_cross_model_comparison(probe_data, results, output_dir):
    """Generate within vs cross-provider comparison box plot."""
    fig, ax = plt.subplots(figsize=(10, 7))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    within_dists, cross_dists = calculate_within_cross_distances(results)

    # Calculate Cohen's d
    pooled_std = np.sqrt((np.var(within_dists) + np.var(cross_dists)) / 2)
    cohens_d = (np.mean(cross_dists) - np.mean(within_dists)) / pooled_std if pooled_std > 0 else 0

    # Box plot
    data = [within_dists, cross_dists]
    positions = [1, 2]

    bp = ax.boxplot(data, positions=positions, patch_artist=True, widths=0.6)

    colors = ['#4285F4', '#E07B53']
    for patch, color in zip(bp['boxes'], colors):
        patch.set_facecolor(color)
        patch.set_alpha(0.7)

    for element in ['whiskers', 'caps', 'medians']:
        for item in bp[element]:
            item.set_color('white')

    ax.set_xticks(positions)
    ax.set_xticklabels(['Within-Provider\n(same family)', 'Cross-Provider\n(different families)'],
                       fontsize=11, color='white')
    ax.set_ylabel('Drift Difference (|d1 - d2|)', fontsize=12, color='white')
    ax.set_title(f"Cross-Model Comparison (Cohen's d = {cohens_d:.3f})\n" +
                 '(d > 0.8 = LARGE effect = genuine identity differences)',
                 fontsize=13, color='white', fontweight='bold')

    ax.grid(True, alpha=0.3, axis='y', color='#333355')
    ax.tick_params(colors='white')

    for spine in ax.spines.values():
        spine.set_color('#333355')

    # Effect size interpretation
    effect_label = "LARGE" if cohens_d >= 0.8 else "MEDIUM" if cohens_d >= 0.5 else "SMALL"
    ax.text(0.98, 0.98, f"Cohen's d = {cohens_d:.3f}\n({effect_label} effect)",
            transform=ax.transAxes, fontsize=12, color='#00ff88' if cohens_d >= 0.8 else 'white',
            verticalalignment='top', horizontalalignment='right',
            bbox=dict(boxstyle='round', facecolor='#1a1a2e', alpha=0.8))

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'cross_model_comparison.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: cross_model_comparison.png (Cohen's d = {cohens_d:.3f})")
    plt.close()

    return cohens_d


def generate_cross_model_histogram(probe_data, results, output_dir):
    """Generate overlapping histograms for within vs cross-provider."""
    fig, ax = plt.subplots(figsize=(10, 7))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    within_dists, cross_dists = calculate_within_cross_distances(results)

    # Histograms
    bins = np.linspace(0, max(max(within_dists), max(cross_dists)), 30)

    ax.hist(within_dists, bins=bins, alpha=0.6, color='#4285F4',
            label=f'Within-Provider (n={len(within_dists)})', edgecolor='white', linewidth=0.5)
    ax.hist(cross_dists, bins=bins, alpha=0.6, color='#E07B53',
            label=f'Cross-Provider (n={len(cross_dists)})', edgecolor='white', linewidth=0.5)

    ax.set_xlabel('Drift Difference', fontsize=12, color='white')
    ax.set_ylabel('Count', fontsize=12, color='white')
    ax.set_title('Distribution of Cross-Model Drift Differences\n' +
                 '(Separated distributions = genuine identity differences)',
                 fontsize=13, color='white', fontweight='bold')

    ax.legend(facecolor='#1a1a2e', edgecolor='#333355', labelcolor='white')
    ax.grid(True, alpha=0.3, color='#333355')
    ax.tick_params(colors='white')

    for spine in ax.spines.values():
        spine.set_color('#333355')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'cross_model_histogram.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: cross_model_histogram.png")
    plt.close()


def generate_provider_matrix(probe_data, results, output_dir):
    """Generate provider-to-provider similarity matrix."""
    fig, ax = plt.subplots(figsize=(9, 8))
    fig.patch.set_facecolor('#0f0f1a')
    ax.set_facecolor('#1a1a2e')

    # Group by provider
    by_provider = defaultdict(list)
    for r in results:
        provider = r.get('provider', 'unknown')
        by_provider[provider].append(r.get('peak_drift', 0))

    providers = sorted(by_provider.keys())
    n = len(providers)
    matrix = np.zeros((n, n))

    # Calculate mean pairwise difference
    for i, p1 in enumerate(providers):
        for j, p2 in enumerate(providers):
            diffs = []
            for d1 in by_provider[p1][:30]:
                for d2 in by_provider[p2][:30]:
                    diffs.append(abs(d1 - d2))
            matrix[i, j] = np.mean(diffs)

    # Plot heatmap
    im = ax.imshow(matrix, cmap='YlGnBu', aspect='auto')

    # Labels
    display_labels = [PROVIDER_DISPLAY.get(p, p) for p in providers]
    ax.set_xticks(range(n))
    ax.set_yticks(range(n))
    ax.set_xticklabels(display_labels, fontsize=10, color='white')
    ax.set_yticklabels(display_labels, fontsize=10, color='white')

    # Add values
    for i in range(n):
        for j in range(n):
            text = ax.text(j, i, f'{matrix[i, j]:.2f}',
                          ha='center', va='center', fontsize=10,
                          color='black' if matrix[i, j] > matrix.max()/2 else 'white')

    cbar = plt.colorbar(im, ax=ax, label='Mean Drift Difference')
    cbar.ax.yaxis.label.set_color('white')
    cbar.ax.tick_params(colors='white')

    ax.set_title('Provider Similarity Matrix\n' +
                 '(Lower diagonal = more similar identity profiles)',
                 fontsize=13, color='white', fontweight='bold')

    plt.tight_layout()

    for ext in ['png', 'svg']:
        plt.savefig(output_dir / f'provider_matrix.{ext}', dpi=150,
                    facecolor=fig.get_facecolor(), bbox_inches='tight')
    print(f"  Saved: provider_matrix.png")
    plt.close()


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("="*60)
    print("10_PFI_DIMENSIONAL: Cosine-Based Identity Validation")
    print("="*60)

    print("\nLoading Run 023d data...")
    results = load_data()
    print(f"Loaded {len(results)} results")

    # Extract features
    features, metadata = extract_drift_features(results)
    probe_data = extract_probe_drifts(results)

    print(f"\nFeature matrix shape: {features.shape}")
    print(f"Providers: {set(m['provider'] for m in metadata)}")

    # Phase 2: PCA
    pca, transformed = generate_phase2_pca(features, metadata)

    # Phase 3A: Perturbation
    generate_phase3a_perturbation(probe_data)

    # Phase 3B: Cross-model
    cohens_d = generate_phase3b_crossmodel(probe_data, results)

    # Summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"Event Horizon: {EVENT_HORIZON}")
    print(f"Cohen's d: {cohens_d:.3f} ({'LARGE' if cohens_d >= 0.8 else 'MEDIUM' if cohens_d >= 0.5 else 'SMALL'})")
    print(f"90% Variance PCs: {np.argmax(np.cumsum(pca.explained_variance_ratio_) >= 0.90) + 1}")
    print("\nVisualization complete!")
    print("="*60)


if __name__ == "__main__":
    main()
