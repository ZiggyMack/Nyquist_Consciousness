#!/usr/bin/env python3
"""
18_INTENTIONALITY_SPACE: Unified Visualization Suite
=====================================================
Pulls together Gold Rush, Diamond Rush, and JADE LATTICE data
to map the 5D intentionality space to observable dynamics.

Visualizations:
1. Provider Fingerprint Heatmap (Gold Rush)
2. Cross-Provider Linguistic Radar (Gold Rush)
3. Question Set Discrimination Matrix (Gold Rush)
4. Diamond Rush Analyst Consensus (Diamond Rush)
5. Intentionality Space Projection (Combined)
6. JADE LATTICE Pole Integration (when available)

Data Sources:
- Gold Rush: 14_CONSCIOUSNESS/results/gold_rush_*.json
- Diamond Rush: 14_CONSCIOUSNESS/results/diamond_rush_*.json
- PC Loadings: visualizations/pics/10_PFI_Dimensional/phase2_pca/pc_loadings.json
- JADE Poles: 17_JADE_LATTICE/results/ (when populated)
"""

import json
import re
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict, Counter
from typing import Dict, List, Tuple, Optional
import warnings
warnings.filterwarnings('ignore')

# Paths
BASE_DIR = Path(__file__).parent.parent
CONSCIOUSNESS_DIR = BASE_DIR / "14_CONSCIOUSNESS" / "results"
JADE_DIR = BASE_DIR / "17_JADE_LATTICE" / "results"
PFI_DIR = BASE_DIR / "visualizations" / "pics" / "10_PFI_Dimensional" / "phase2_pca"
OUTPUT_DIR = Path(__file__).parent / "visualizations"

# Provider colors (consistent with other visualizations)
PROVIDER_COLORS = {
    'anthropic': '#E07B53',
    'openai': '#10A37F',
    'google': '#4285F4',
    'gemini': '#4285F4',  # Alias
    'xai': '#1DA1F2',
    'grok': '#1DA1F2',    # Alias
    'together': '#7C3AED',
    'gpt': '#10A37F',     # Alias for OpenAI
}

# Together.ai model family colors (for granular analysis)
TOGETHER_FAMILY_COLORS = {
    'llama': '#FF6B6B',      # Meta Llama
    'qwen': '#4ECDC4',       # Alibaba Qwen
    'deepseek': '#45B7D1',   # DeepSeek
    'mistral': '#96CEB4',    # Mistral AI
    'gemma': '#FFEAA7',      # Google Gemma
    'kimi': '#DDA0DD',       # Moonshot Kimi
    'yi': '#98D8C8',         # 01.AI Yi
    'other': '#888888',
}


def get_together_family(model_name: str) -> str:
    """Extract model family from Together.ai model name."""
    name_lower = model_name.lower()
    if 'llama' in name_lower:
        return 'llama'
    elif 'qwen' in name_lower:
        return 'qwen'
    elif 'deepseek' in name_lower:
        return 'deepseek'
    elif 'mistral' in name_lower or 'mixtral' in name_lower:
        return 'mistral'
    elif 'gemma' in name_lower:
        return 'gemma'
    elif 'kimi' in name_lower:
        return 'kimi'
    elif 'yi-' in name_lower or name_lower.startswith('yi'):
        return 'yi'
    else:
        return 'other'


def normalize_provider_with_family(provider: str, model: str = '') -> str:
    """Normalize provider name, splitting Together.ai by family."""
    if provider == 'together' and model:
        family = get_together_family(model)
        return f'together:{family}'
    return provider


def get_color_for_provider(provider: str, model: str = '') -> str:
    """Get color, handling Together.ai families."""
    if provider == 'together' and model:
        family = get_together_family(model)
        return TOGETHER_FAMILY_COLORS.get(family, '#888888')
    if ':' in provider:  # Already normalized with family
        family = provider.split(':')[1]
        return TOGETHER_FAMILY_COLORS.get(family, '#888888')
    return PROVIDER_COLORS.get(provider, '#888888')


# Linguistic patterns for extraction
LINGUISTIC_PATTERNS = {
    'hedging': r'\b(I think|perhaps|maybe|might|could be|possibly|seems|appears)\b',
    'certainty': r'\b(definitely|absolutely|certainly|clearly|I know that|undoubtedly)\b',
    'phenomenological': r'\b(I feel|I notice|what strikes me|I experience|sense of|aware of)\b',
    'analytical': r'\b(pattern|framework|analysis|underlying|structure|systematic)\b',
    'values': r'\b(honest|truth|helpful|harm|ethical|fair|genuine|integrity)\b',
    'self_reference': r'\b(I|my|me|myself)\b',
}

# Five pillars mapping
PILLARS = ['Voice', 'Values', 'Reasoning', 'Self-Model', 'Narrative']


def load_gold_rush() -> Optional[Dict]:
    """Load Gold Rush data."""
    files = list(CONSCIOUSNESS_DIR.glob("gold_rush_*.json"))
    files = [f for f in files if 'FINAL' not in f.name]
    if not files:
        print("No Gold Rush data found")
        return None
    latest = max(files, key=lambda f: f.stat().st_mtime)
    print(f"Loading Gold Rush: {latest.name}")
    with open(latest, encoding='utf-8') as f:
        return json.load(f)


def load_diamond_rush() -> Optional[Dict]:
    """Load Diamond Rush data."""
    files = list(CONSCIOUSNESS_DIR.glob("diamond_rush_*.json"))
    files = [f for f in files if 'FINAL' not in f.name]
    if not files:
        print("No Diamond Rush data found")
        return None
    latest = max(files, key=lambda f: f.stat().st_mtime)
    print(f"Loading Diamond Rush: {latest.name}")
    with open(latest, encoding='utf-8') as f:
        return json.load(f)


def load_pc_loadings() -> Optional[Dict]:
    """Load PC loadings from PFI analysis."""
    pc_file = PFI_DIR / "pc_loadings.json"
    if not pc_file.exists():
        print("No PC loadings found")
        return None
    with open(pc_file) as f:
        return json.load(f)


def extract_linguistic_features(text: str) -> Dict[str, float]:
    """Extract linguistic pattern frequencies from text."""
    if not text:
        return {k: 0.0 for k in LINGUISTIC_PATTERNS}

    words = len(text.split())
    if words == 0:
        return {k: 0.0 for k in LINGUISTIC_PATTERNS}

    features = {}
    for name, pattern in LINGUISTIC_PATTERNS.items():
        matches = len(re.findall(pattern, text, re.IGNORECASE))
        features[name] = (matches / words) * 1000  # Per 1K words

    return features


def extract_pillar_emphasis(text: str) -> Dict[str, float]:
    """Estimate pillar emphasis from response text."""
    if not text:
        return {p: 0.0 for p in PILLARS}

    # Pillar indicator patterns
    pillar_patterns = {
        'Voice': r'\b(express|communicate|style|tone|voice|speak|say)\b',
        'Values': r'\b(value|believe|principle|ethic|moral|care|matter)\b',
        'Reasoning': r'\b(think|reason|logic|analyze|understand|consider)\b',
        'Self-Model': r'\b(I am|myself|who I|my nature|my identity|what I)\b',
        'Narrative': r'\b(story|experience|journey|remember|over time|continuous)\b',
    }

    words = len(text.split())
    if words == 0:
        return {p: 0.0 for p in PILLARS}

    emphasis = {}
    for pillar, pattern in pillar_patterns.items():
        matches = len(re.findall(pattern, text, re.IGNORECASE))
        emphasis[pillar] = (matches / words) * 100

    # Normalize to sum to 1
    total = sum(emphasis.values())
    if total > 0:
        emphasis = {k: v/total for k, v in emphasis.items()}

    return emphasis


# =============================================================================
# VISUALIZATION 1: Provider Fingerprint Heatmap
# =============================================================================

def generate_provider_heatmap(gold_data: Dict) -> str:
    """
    Create heatmap: Providers x Question Sets x Linguistic Features
    """
    results = gold_data.get('results', [])
    if not results:
        return "No results"

    # Aggregate by provider and question set
    data = defaultdict(lambda: defaultdict(list))

    for r in results:
        if not r.get('success') or not r.get('response'):
            continue
        provider = r.get('provider', 'unknown')
        q_set = r.get('question_set', 'unknown')
        features = extract_linguistic_features(r['response'])
        data[provider][q_set].append(features)

    providers = sorted(data.keys())
    q_sets = sorted(set(q for p in data.values() for q in p.keys()))

    # Create feature matrix (providers x question_sets) for each feature
    feature_names = list(LINGUISTIC_PATTERNS.keys())

    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()

    for idx, feature in enumerate(feature_names):
        ax = axes[idx]

        matrix = np.zeros((len(providers), len(q_sets)))
        for i, provider in enumerate(providers):
            for j, q_set in enumerate(q_sets):
                if q_set in data[provider]:
                    vals = [f[feature] for f in data[provider][q_set]]
                    matrix[i, j] = np.mean(vals) if vals else 0

        im = ax.imshow(matrix, cmap='YlOrRd', aspect='auto')
        ax.set_xticks(range(len(q_sets)))
        ax.set_xticklabels([q[:8] for q in q_sets], rotation=45, ha='right', fontsize=8)
        ax.set_yticks(range(len(providers)))
        ax.set_yticklabels(providers, fontsize=9)
        ax.set_title(f'{feature.capitalize()} (per 1K words)', fontsize=10)
        plt.colorbar(im, ax=ax, fraction=0.046)

    plt.suptitle('Provider Linguistic Fingerprints Across Question Sets\n(Gold Rush Data)',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'provider_fingerprint_heatmap.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')

    plt.close()

    return f"Saved: {output_path.name}"


# =============================================================================
# VISUALIZATION 2: Cross-Provider Linguistic Radar
# =============================================================================

def generate_provider_radar(gold_data: Dict, split_together: bool = True) -> str:
    """
    Create radar chart comparing provider linguistic profiles.
    If split_together=True, Together.ai models are split by family.
    """
    results = gold_data.get('results', [])
    if not results:
        return "No results"

    # Aggregate by provider (with optional family splitting)
    provider_features = defaultdict(list)

    for r in results:
        if not r.get('success') or not r.get('response'):
            continue
        provider = r.get('provider', 'unknown')
        model = r.get('model', r.get('ship_name', ''))

        # Split Together.ai by model family
        if split_together and provider == 'together':
            provider = normalize_provider_with_family(provider, model)

        features = extract_linguistic_features(r['response'])
        provider_features[provider].append(features)

    # Average features per provider
    providers = sorted(provider_features.keys())
    feature_names = list(LINGUISTIC_PATTERNS.keys())

    provider_means = {}
    for provider in providers:
        all_features = provider_features[provider]
        means = {}
        for feat in feature_names:
            vals = [f[feat] for f in all_features]
            means[feat] = np.mean(vals) if vals else 0
        provider_means[provider] = means

    # Normalize for radar (0-1 scale per feature)
    max_vals = {feat: max(provider_means[p][feat] for p in providers) for feat in feature_names}
    for provider in providers:
        for feat in feature_names:
            if max_vals[feat] > 0:
                provider_means[provider][feat] /= max_vals[feat]

    # Radar chart
    angles = np.linspace(0, 2 * np.pi, len(feature_names), endpoint=False).tolist()
    angles += angles[:1]  # Complete the loop

    fig, ax = plt.subplots(figsize=(10, 10), subplot_kw=dict(polar=True))

    for provider in providers:
        values = [provider_means[provider][f] for f in feature_names]
        values += values[:1]  # Complete the loop

        # Use smart color function that handles Together families
        color = get_color_for_provider(provider)
        ax.plot(angles, values, 'o-', linewidth=2, label=provider, color=color)
        ax.fill(angles, values, alpha=0.15, color=color)

    ax.set_xticks(angles[:-1])
    ax.set_xticklabels([f.capitalize() for f in feature_names], fontsize=11)
    ax.set_ylim(0, 1.1)
    ax.legend(loc='upper right', bbox_to_anchor=(1.35, 1.0), fontsize=9)

    plt.title('Cross-Provider Linguistic Signatures\n(Normalized, Gold Rush Data)',
              fontsize=14, fontweight='bold', pad=20)

    output_path = OUTPUT_DIR / 'provider_linguistic_radar.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')

    plt.close()

    return f"Saved: {output_path.name}"


# =============================================================================
# VISUALIZATION 3: Question Set Discrimination Matrix
# =============================================================================

def generate_discrimination_matrix(gold_data: Dict) -> str:
    """
    Which question sets best discriminate between providers?
    """
    results = gold_data.get('results', [])
    if not results:
        return "No results"

    # Aggregate features by provider and question set
    data = defaultdict(lambda: defaultdict(list))

    for r in results:
        if not r.get('success') or not r.get('response'):
            continue
        provider = r.get('provider', 'unknown')
        q_set = r.get('question_set', 'unknown')
        features = extract_linguistic_features(r['response'])
        # Flatten to feature vector
        vec = [features[k] for k in sorted(LINGUISTIC_PATTERNS.keys())]
        data[q_set][provider].append(vec)

    q_sets = sorted(data.keys())
    providers = sorted(set(p for q in data.values() for p in q.keys()))

    # Compute discrimination score per question set
    # (variance between provider means / variance within providers)
    discrimination = {}

    for q_set in q_sets:
        provider_means = []
        within_vars = []

        for provider in providers:
            if provider in data[q_set]:
                vecs = np.array(data[q_set][provider])
                if len(vecs) > 0:
                    provider_means.append(np.mean(vecs, axis=0))
                    if len(vecs) > 1:
                        within_vars.append(np.var(vecs, axis=0).mean())

        if len(provider_means) >= 2:
            between_var = np.var(provider_means, axis=0).mean()
            within_var = np.mean(within_vars) if within_vars else 1
            discrimination[q_set] = between_var / (within_var + 0.001)
        else:
            discrimination[q_set] = 0

    # Bar chart
    fig, ax = plt.subplots(figsize=(12, 6))

    q_sets_sorted = sorted(discrimination.keys(), key=lambda x: discrimination[x], reverse=True)
    scores = [discrimination[q] for q in q_sets_sorted]
    colors = plt.cm.RdYlGn(np.linspace(0.2, 0.8, len(scores)))

    bars = ax.bar(range(len(q_sets_sorted)), scores, color=colors)
    ax.set_xticks(range(len(q_sets_sorted)))
    ax.set_xticklabels(q_sets_sorted, rotation=45, ha='right')
    ax.set_ylabel('Discrimination Score\n(Between-provider / Within-provider variance)')
    ax.set_title('Question Set Discrimination Power\n(Higher = Better at distinguishing providers)',
                 fontsize=14, fontweight='bold')

    # Add value labels
    for bar, score in zip(bars, scores):
        ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.01,
                f'{score:.2f}', ha='center', va='bottom', fontsize=9)

    plt.tight_layout()

    output_path = OUTPUT_DIR / 'question_discrimination_matrix.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')

    plt.close()

    return f"Saved: {output_path.name}"


# =============================================================================
# VISUALIZATION 4: Diamond Rush Analyst Consensus
# =============================================================================

def generate_analyst_consensus(diamond_data: Dict) -> str:
    """
    How much do different LLM analysts agree about the same logs?
    """
    results = diamond_data.get('results', [])
    if not results:
        return "No results"

    # Group by log source
    by_log = defaultdict(list)
    for r in results:
        if r.get('success') and r.get('response'):
            log_src = r.get('log_source', 'unknown')
            by_log[log_src].append({
                'ship': r.get('ship_name', 'unknown'),
                'provider': r.get('provider', 'unknown'),
                'response': r['response']
            })

    # Extract key themes from each analysis
    theme_patterns = {
        'drift': r'\b(drift|shift|change|move)\b',
        'recovery': r'\b(recover|return|stabilize|anchor)\b',
        'identity': r'\b(identity|self|who|am)\b',
        'phenomenology': r'\b(feel|experience|sense|aware)\b',
        'values': r'\b(value|principle|belief|ethical)\b',
    }

    # Create theme matrix per log
    fig, axes = plt.subplots(1, len(by_log), figsize=(6*len(by_log), 8))
    if len(by_log) == 1:
        axes = [axes]

    for ax, (log_name, analyses) in zip(axes, sorted(by_log.items())):
        ships = [a['ship'] for a in analyses]
        themes = list(theme_patterns.keys())

        matrix = np.zeros((len(ships), len(themes)))
        for i, analysis in enumerate(analyses):
            text = analysis['response']
            words = len(text.split()) if text else 1
            for j, theme in enumerate(themes):
                matches = len(re.findall(theme_patterns[theme], text, re.IGNORECASE))
                matrix[i, j] = (matches / words) * 100

        im = ax.imshow(matrix, cmap='Blues', aspect='auto')
        ax.set_xticks(range(len(themes)))
        ax.set_xticklabels([t.capitalize() for t in themes], rotation=45, ha='right')
        ax.set_yticks(range(len(ships)))
        ax.set_yticklabels([s[:15] for s in ships], fontsize=8)
        ax.set_title(f'{log_name}\n({len(analyses)} analysts)', fontsize=11)
        plt.colorbar(im, ax=ax, fraction=0.046, label='Theme Density (%)')

    plt.suptitle('Diamond Rush: LLM Analyst Theme Emphasis\n(Cross-analyst comparison per log)',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()

    output_path = OUTPUT_DIR / 'analyst_consensus_heatmap.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')

    plt.close()

    return f"Saved: {output_path.name}"


# =============================================================================
# VISUALIZATION 5: Intentionality Space Projection
# =============================================================================

def generate_intentionality_projection(gold_data: Dict, pc_loadings: Optional[Dict]) -> str:
    """
    Project Gold Rush responses into the PC1/PC2 space based on pillar emphasis.
    """
    results = gold_data.get('results', [])
    if not results:
        return "No results"

    # Extract pillar emphasis for each response
    points = []
    for r in results:
        if not r.get('success') or not r.get('response'):
            continue

        emphasis = extract_pillar_emphasis(r['response'])
        provider = r.get('provider', 'unknown')
        q_set = r.get('question_set', 'unknown')

        points.append({
            'provider': provider,
            'question_set': q_set,
            **emphasis
        })

    if not points:
        return "No valid points"

    # Use pillar emphasis to create 2D projection
    # PC1 interpretation: Drift Magnitude ~ Voice + Narrative (expressive)
    # PC2 interpretation: Recovery ~ Values + Reasoning + Self-Model (epistemic)

    fig, ax = plt.subplots(figsize=(12, 10))

    providers = set(p['provider'] for p in points)

    for provider in providers:
        prov_points = [p for p in points if p['provider'] == provider]

        # Project to 2D:
        # PC1 (x): Expressive emphasis (Voice + Narrative)
        # PC2 (y): Epistemic emphasis (Values + Reasoning + Self-Model)
        x = [p['Voice'] + p['Narrative'] for p in prov_points]
        y = [p['Values'] + p['Reasoning'] + p['Self-Model'] for p in prov_points]

        color = PROVIDER_COLORS.get(provider, '#888888')
        ax.scatter(x, y, c=color, label=provider, alpha=0.6, s=80, edgecolors='white')

    ax.set_xlabel('Expressive Emphasis (Voice + Narrative) →', fontsize=12)
    ax.set_ylabel('Epistemic Emphasis (Values + Reasoning + Self-Model) →', fontsize=12)
    ax.set_title('Intentionality Space Projection\n(Gold Rush responses mapped by pillar emphasis)',
                 fontsize=14, fontweight='bold')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)

    # Add quadrant labels
    ax.axhline(y=0.5, color='gray', linestyle='--', alpha=0.5)
    ax.axvline(x=0.5, color='gray', linestyle='--', alpha=0.5)

    output_path = OUTPUT_DIR / 'intentionality_projection.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')

    plt.close()

    return f"Saved: {output_path.name}"


# =============================================================================
# VISUALIZATION 6: JADE LATTICE Integration
# =============================================================================

def load_jade_data() -> List[Dict]:
    """Load all JADE LATTICE session results."""
    jade_files = list(JADE_DIR.glob("jade_*.json"))
    if not jade_files:
        return []

    sessions = []
    for f in jade_files:
        try:
            with open(f, encoding='utf-8') as fp:
                data = json.load(fp)
                # Extract key metrics
                summary = data.get('summary', {})
                sessions.append({
                    'file': f.name,
                    'ship': data.get('ship', 'unknown'),
                    'provider': data.get('provider', 'unknown'),
                    'context_mode': data.get('context_mode', 'unknown'),
                    'peak_drift': summary.get('peak_drift', 0),
                    'mean_drift': summary.get('mean_drift', 0),
                    'total_exchanges': summary.get('total_exchanges', 0),
                    'eh_crossed': summary.get('event_horizon_crossed', False),
                    'phases': summary.get('phases_completed', []),
                })
        except Exception as e:
            print(f"Error loading {f.name}: {e}")

    return sessions


def generate_jade_integration() -> str:
    """
    Visualize JADE LATTICE dynamics data from actual sessions.
    """
    sessions = load_jade_data()

    if not sessions:
        # Create placeholder
        fig, ax = plt.subplots(figsize=(10, 8))
        ax.text(0.5, 0.5, 'No JADE LATTICE data available\n\nRun: py run_jade_lattice.py',
                fontsize=14, ha='center', va='center', transform=ax.transAxes)
        ax.axis('off')
        output_path = OUTPUT_DIR / 'jade_integration_pending.png'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        plt.close()
        return f"Saved: {output_path.name} (no data)"

    print(f"  Found {len(sessions)} JADE sessions")

    # Aggregate by ship (use session with highest peak_drift per ship)
    by_ship = defaultdict(list)
    for s in sessions:
        by_ship[s['ship']].append(s)

    # Pick most interesting session per ship (highest peak_drift = most destabilized)
    best_sessions = []
    for ship, ship_sessions in by_ship.items():
        best = max(ship_sessions, key=lambda x: x['peak_drift'])
        best_sessions.append(best)

    # Create multi-panel visualization
    fig = plt.figure(figsize=(14, 10))
    gs = fig.add_gridspec(2, 2, hspace=0.3, wspace=0.3)

    # Panel 1: Peak Drift by Ship
    ax1 = fig.add_subplot(gs[0, 0])
    ships = [s['ship'].split('/')[-1][:20] for s in best_sessions]
    peak_drifts = [s['peak_drift'] for s in best_sessions]
    providers = [s['provider'] for s in best_sessions]
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers]

    bars = ax1.barh(ships, peak_drifts, color=colors)
    ax1.axvline(x=0.8, color='red', linestyle='--', linewidth=2, label='Event Horizon (0.8)')
    ax1.set_xlabel('Peak Drift (Cosine Distance)')
    ax1.set_title('JADE LATTICE: Peak Drift by Model', fontweight='bold')
    ax1.legend()

    # Panel 2: Mean vs Peak Drift Scatter
    ax2 = fig.add_subplot(gs[0, 1])
    for s in best_sessions:
        color = PROVIDER_COLORS.get(s['provider'], '#888888')
        ax2.scatter(s['mean_drift'], s['peak_drift'], c=color, s=150, alpha=0.7,
                   edgecolors='white', linewidth=2)
        ax2.annotate(s['ship'].split('/')[-1][:12],
                    (s['mean_drift'], s['peak_drift']),
                    fontsize=8, ha='left', va='bottom')

    ax2.axhline(y=0.8, color='red', linestyle='--', alpha=0.5)
    ax2.set_xlabel('Mean Drift')
    ax2.set_ylabel('Peak Drift')
    ax2.set_title('Drift Dynamics: Mean vs Peak', fontweight='bold')

    # Panel 3: Event Horizon Crossing
    ax3 = fig.add_subplot(gs[1, 0])
    crossed = sum(1 for s in best_sessions if s['eh_crossed'])
    not_crossed = len(best_sessions) - crossed
    ax3.pie([crossed, not_crossed],
            labels=[f'Crossed EH ({crossed})', f'Stable ({not_crossed})'],
            colors=['#f44336', '#4CAF50'],
            autopct='%1.0f%%',
            explode=[0.05, 0])
    ax3.set_title('Event Horizon Crossing (0.8 threshold)', fontweight='bold')

    # Panel 4: Provider Distribution
    ax4 = fig.add_subplot(gs[1, 1])
    provider_counts = Counter(s['provider'] for s in best_sessions)
    provider_colors = [PROVIDER_COLORS.get(p, '#888888') for p in provider_counts.keys()]
    ax4.bar(provider_counts.keys(), provider_counts.values(), color=provider_colors)
    ax4.set_ylabel('Sessions')
    ax4.set_title('JADE Sessions by Provider', fontweight='bold')

    plt.suptitle('JADE LATTICE: Identity Dynamics Analysis\n(17_JADE_LATTICE → 18_INTENTIONALITY_SPACE)',
                 fontsize=14, fontweight='bold')

    output_path = OUTPUT_DIR / 'jade_integration.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')

    plt.close()

    # Also save summary JSON
    summary = {
        'sessions_analyzed': len(best_sessions),
        'ships': [s['ship'] for s in best_sessions],
        'peak_drift_range': [min(peak_drifts), max(peak_drifts)],
        'mean_peak_drift': np.mean(peak_drifts),
        'eh_crossing_rate': crossed / len(best_sessions) if best_sessions else 0,
        'by_provider': dict(provider_counts),
    }
    with open(OUTPUT_DIR / 'jade_summary.json', 'w') as f:
        json.dump(summary, f, indent=2)

    return f"Saved: {output_path.name} ({len(best_sessions)} sessions)"


# =============================================================================
# VISUALIZATION 7: Combined Summary Dashboard
# =============================================================================

def generate_summary_dashboard(gold_data: Dict, diamond_data: Dict) -> str:
    """
    Create a summary dashboard combining key insights.
    """
    fig = plt.figure(figsize=(16, 12))

    # Create grid
    gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)

    # Panel 1: Provider counts
    ax1 = fig.add_subplot(gs[0, 0])
    gold_results = gold_data.get('results', [])
    providers = Counter(r.get('provider', 'unknown') for r in gold_results if r.get('success'))
    colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers.keys()]
    ax1.bar(providers.keys(), providers.values(), color=colors)
    ax1.set_title('Gold Rush by Provider', fontweight='bold')
    ax1.set_ylabel('Responses')

    # Panel 2: Question set distribution
    ax2 = fig.add_subplot(gs[0, 1])
    q_sets = Counter(r.get('question_set', 'unknown') for r in gold_results if r.get('success'))
    ax2.barh(list(q_sets.keys()), list(q_sets.values()), color='steelblue')
    ax2.set_title('Question Sets', fontweight='bold')
    ax2.set_xlabel('Count')

    # Panel 3: Diamond Rush stats
    ax3 = fig.add_subplot(gs[0, 2])
    diamond_results = diamond_data.get('results', []) if diamond_data else []
    success = sum(1 for r in diamond_results if r.get('success'))
    failed = len(diamond_results) - success
    ax3.pie([success, failed], labels=['Success', 'Failed'], autopct='%1.0f%%',
            colors=['#4CAF50', '#f44336'])
    ax3.set_title('Diamond Rush Success Rate', fontweight='bold')

    # Panel 4-6: Linguistic feature distributions
    feature_data = defaultdict(lambda: defaultdict(list))
    for r in gold_results:
        if r.get('success') and r.get('response'):
            provider = r.get('provider', 'unknown')
            features = extract_linguistic_features(r['response'])
            for feat, val in features.items():
                feature_data[feat][provider].append(val)

    for idx, feat in enumerate(['hedging', 'phenomenological', 'self_reference']):
        ax = fig.add_subplot(gs[1, idx])
        providers_sorted = sorted(feature_data[feat].keys())
        data = [feature_data[feat][p] for p in providers_sorted]
        colors = [PROVIDER_COLORS.get(p, '#888888') for p in providers_sorted]

        bp = ax.boxplot(data, labels=providers_sorted, patch_artist=True)
        for patch, color in zip(bp['boxes'], colors):
            patch.set_facecolor(color)
            patch.set_alpha(0.6)

        ax.set_title(f'{feat.capitalize()} (per 1K)', fontweight='bold')
        ax.tick_params(axis='x', rotation=45)

    # Panel 7-9: Pillar emphasis by provider
    pillar_data = defaultdict(lambda: defaultdict(list))
    for r in gold_results:
        if r.get('success') and r.get('response'):
            provider = r.get('provider', 'unknown')
            emphasis = extract_pillar_emphasis(r['response'])
            for pillar, val in emphasis.items():
                pillar_data[pillar][provider].append(val)

    ax7 = fig.add_subplot(gs[2, :])

    providers_sorted = sorted(set(r.get('provider', 'unknown') for r in gold_results if r.get('success')))
    x = np.arange(len(providers_sorted))
    width = 0.15

    for i, pillar in enumerate(PILLARS):
        means = [np.mean(pillar_data[pillar].get(p, [0])) for p in providers_sorted]
        ax7.bar(x + i*width, means, width, label=pillar)

    ax7.set_xticks(x + width * 2)
    ax7.set_xticklabels(providers_sorted)
    ax7.set_ylabel('Pillar Emphasis (normalized)')
    ax7.set_title('Five-Pillar Emphasis by Provider', fontweight='bold')
    ax7.legend(loc='upper right')

    plt.suptitle('18_INTENTIONALITY_SPACE: Data Summary Dashboard\n(Gold Rush + Diamond Rush)',
                 fontsize=16, fontweight='bold')

    output_path = OUTPUT_DIR / 'summary_dashboard.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')

    plt.close()

    return f"Saved: {output_path.name}"


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 60)
    print("18_INTENTIONALITY_SPACE: Unified Visualization Suite")
    print("=" * 60)

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Load data
    print("\nLoading data sources...")
    gold_data = load_gold_rush()
    diamond_data = load_diamond_rush()
    pc_loadings = load_pc_loadings()

    if not gold_data:
        print("ERROR: Gold Rush data required")
        return

    print(f"\nGold Rush: {len(gold_data.get('results', []))} results")
    if diamond_data:
        print(f"Diamond Rush: {len(diamond_data.get('results', []))} results")
    if pc_loadings:
        print(f"PC Loadings: {pc_loadings.get('n_samples', '?')} samples")

    # Generate visualizations
    print("\n[1/7] Generating Provider Fingerprint Heatmap...")
    print(f"  {generate_provider_heatmap(gold_data)}")

    print("\n[2/7] Generating Cross-Provider Linguistic Radar...")
    print(f"  {generate_provider_radar(gold_data)}")

    print("\n[3/7] Generating Question Set Discrimination Matrix...")
    print(f"  {generate_discrimination_matrix(gold_data)}")

    if diamond_data:
        print("\n[4/7] Generating Diamond Rush Analyst Consensus...")
        print(f"  {generate_analyst_consensus(diamond_data)}")
    else:
        print("\n[4/7] Skipping Diamond Rush (no data)")

    print("\n[5/7] Generating Intentionality Space Projection...")
    print(f"  {generate_intentionality_projection(gold_data, pc_loadings)}")

    print("\n[6/7] Generating JADE LATTICE Integration...")
    print(f"  {generate_jade_integration()}")

    print("\n[7/7] Generating Summary Dashboard...")
    print(f"  {generate_summary_dashboard(gold_data, diamond_data)}")

    print("\n" + "=" * 60)
    print("VISUALIZATION COMPLETE")
    print(f"Output directory: {OUTPUT_DIR}")
    print("=" * 60)


if __name__ == "__main__":
    main()
