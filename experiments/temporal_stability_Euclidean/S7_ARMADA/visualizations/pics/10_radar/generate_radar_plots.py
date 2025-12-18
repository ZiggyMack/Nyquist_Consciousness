"""
Radar Plot Generator for Nyquist Consciousness Experiments.

Creates multi-dimensional radar plots for:
1. Provider Identity Fingerprints (mean drift, volatility, recovery, etc.)
2. Nyquist Pillar Scores (Voice, Values, Reasoning, Self-Model, Narrative)
3. PFI Component Breakdown (A_pole, B_zero, C_meta, D_identity, E_hedging)

Usage:
    python generate_radar_plots.py --type provider --run 018
    python generate_radar_plots.py --type pillar --run 018
    python generate_radar_plots.py --type pfi
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Patch
from pathlib import Path
from collections import defaultdict
import argparse

# Paths
SCRIPT_DIR = Path(__file__).parent
ARMADA_DIR = SCRIPT_DIR.parent.parent.parent
RESULTS_DIR = ARMADA_DIR / "0_results" / "runs"
MANIFEST_DIR = ARMADA_DIR / "0_results" / "manifests"
TEMPORAL_LOGS_DIR = ARMADA_DIR / "0_results" / "temporal_logs"

# Event Horizon threshold
EVENT_HORIZON = 1.23

# Provider colors (consistent with other visualizations)
PROVIDER_COLORS = {
    "claude": "#E57373",    # Coral red
    "gpt": "#64B5F6",       # Sky blue
    "gemini": "#81C784",    # Sage green
    "grok": "#FFD54F",      # Gold
    "together": "#BA68C8",  # Purple
}

# Provider mapping
PROVIDER_MAP = {
    "claude": "claude", "gpt": "gpt", "o3": "gpt", "o4": "gpt",
    "gemini": "gemini", "grok": "grok",
    "deepseek": "together", "llama": "together", "mistral": "together",
    "mixtral": "together", "qwen": "together", "kimi": "together", "nemotron": "together",
}


def get_provider(model_name: str) -> str:
    """Map model name to provider."""
    model_lower = model_name.lower()
    for prefix, provider in PROVIDER_MAP.items():
        if model_lower.startswith(prefix):
            return provider
    return "unknown"


def load_run_data(run_id: str) -> list:
    """Load all data files for a run from temporal_logs."""
    results = []

    # Load from temporal_logs - this has the actual recovery_sequence data
    temporal_files = list(TEMPORAL_LOGS_DIR.glob(f"run{run_id}_*.json"))
    print(f"  Found {len(temporal_files)} temporal log files for run {run_id}")

    for filepath in temporal_files:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)
                # Extract model name from filename: run018_gravity_claude-opus-4.5_unknown_20251216_031935.json
                filename = filepath.stem
                parts = filename.split('_')
                if len(parts) >= 3:
                    # Model name is between protocol type and 'unknown' or timestamp
                    # Example: run018_gravity_claude-opus-4.5_unknown_20251216_031935
                    model_name = parts[2] if len(parts) > 2 else 'unknown'
                else:
                    model_name = 'unknown'

                # Get recovery_sequence as drift trajectory
                recovery_sequence = data.get('recovery_sequence', [])
                if recovery_sequence:
                    peak = data.get('peak_drift', max(recovery_sequence) if recovery_sequence else 0)
                    results.append({
                        'model': model_name,
                        'drifts': recovery_sequence,
                        'peak_drift': peak,
                        'baseline_to_final': data.get('baseline_to_final_drift', 0),
                        'fitted_gamma': data.get('fitted_gamma', 0),
                        'fitted_lambda': data.get('fitted_lambda', 0),
                    })
        except (json.JSONDecodeError, FileNotFoundError) as e:
            print(f"  Error loading {filepath.name}: {e}")
            continue

    print(f"  Loaded {len(results)} valid temporal logs with drift data")
    return results


def extract_provider_metrics(run_data: list) -> dict:
    """Extract metrics per provider for radar plot."""
    metrics = defaultdict(lambda: {
        'drifts': [],
        'max_drifts': [],
        'baseline_drifts': [],
        'volatile_count': 0,
        'stable_count': 0,
        'model_count': 0,
    })

    for data in run_data:
        # Handle new temporal_logs format (direct model/drifts format)
        if 'model' in data and 'drifts' in data:
            model = data['model']
            provider = get_provider(model)
            if provider == "unknown":
                continue

            drifts = data['drifts']
            if drifts:
                metrics[provider]['drifts'].extend(drifts)
                metrics[provider]['max_drifts'].append(max(drifts))
                metrics[provider]['baseline_drifts'].append(drifts[0])

                if max(drifts) >= EVENT_HORIZON:
                    metrics[provider]['volatile_count'] += 1
                else:
                    metrics[provider]['stable_count'] += 1
                metrics[provider]['model_count'] += 1
            continue

        # Handle subjects format (consolidated)
        subjects = data.get('subjects', [])
        for subj in subjects:
            model = subj.get('model', subj.get('ship', 'unknown'))
            provider = get_provider(model)
            if provider == "unknown":
                continue

            drifts = subj.get('drifts', [])
            if drifts:
                metrics[provider]['drifts'].extend(drifts)
                metrics[provider]['max_drifts'].append(max(drifts))
                metrics[provider]['baseline_drifts'].append(drifts[0])

                if max(drifts) >= EVENT_HORIZON:
                    metrics[provider]['volatile_count'] += 1
                else:
                    metrics[provider]['stable_count'] += 1
                metrics[provider]['model_count'] += 1

    return dict(metrics)


def compute_radar_values(metrics: dict) -> dict:
    """Compute normalized radar values for each provider."""
    radar_data = {}

    for provider, data in metrics.items():
        if not data['drifts'] or data['model_count'] == 0:
            continue

        # Compute raw metrics
        mean_drift = np.mean(data['drifts'])
        max_drift = np.mean(data['max_drifts']) if data['max_drifts'] else 0
        volatility_rate = data['volatile_count'] / data['model_count'] if data['model_count'] > 0 else 0
        stability_rate = data['stable_count'] / data['model_count'] if data['model_count'] > 0 else 0
        drift_variance = np.std(data['drifts']) if len(data['drifts']) > 1 else 0

        # Normalize to 0-1 scale (relative to Event Horizon where applicable)
        radar_data[provider] = {
            'Mean Drift': min(mean_drift / EVENT_HORIZON, 1.5) / 1.5,  # Cap at 150% of EH
            'Peak Drift': min(max_drift / EVENT_HORIZON, 2.0) / 2.0,  # Cap at 200% of EH
            'Volatility': volatility_rate,
            'Stability': stability_rate,
            'Consistency': 1 - min(drift_variance, 1.0),  # Higher = more consistent
        }

    return radar_data


def create_radar_plot(radar_data: dict, title: str, output_path: Path):
    """Create a radar plot comparing providers."""
    categories = list(next(iter(radar_data.values())).keys())
    N = len(categories)

    # Create angle array
    angles = [n / float(N) * 2 * np.pi for n in range(N)]
    angles += angles[:1]  # Complete the loop

    # Create figure
    fig, ax = plt.subplots(figsize=(10, 10), subplot_kw=dict(polar=True))

    # Plot each provider
    for provider, values in radar_data.items():
        vals = list(values.values())
        vals += vals[:1]  # Complete the loop

        color = PROVIDER_COLORS.get(provider, '#888888')
        ax.plot(angles, vals, 'o-', linewidth=2, label=provider.title(), color=color)
        ax.fill(angles, vals, alpha=0.25, color=color)

    # Set category labels
    ax.set_xticks(angles[:-1])
    ax.set_xticklabels(categories, size=11, fontweight='bold')

    # Set radial limits
    ax.set_ylim(0, 1)
    ax.set_yticks([0.25, 0.5, 0.75, 1.0])
    ax.set_yticklabels(['25%', '50%', '75%', '100%'], size=9)

    # Add title and legend
    ax.set_title(title, size=14, fontweight='bold', pad=20)
    ax.legend(loc='upper right', bbox_to_anchor=(1.15, 1.1))

    # Save
    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.savefig(output_path.with_suffix('.svg'), bbox_inches='tight')
    plt.close()

    print(f"Created: {output_path}")
    print(f"Created: {output_path.with_suffix('.svg')}")


def create_nyquist_pillar_radar(pillar_data: dict, title: str, output_path: Path):
    """Create radar plot for Nyquist 5 Pillars."""
    categories = ['Voice', 'Values', 'Reasoning', 'Self-Model', 'Narrative']
    N = len(categories)

    angles = [n / float(N) * 2 * np.pi for n in range(N)]
    angles += angles[:1]

    fig, ax = plt.subplots(figsize=(10, 10), subplot_kw=dict(polar=True))

    for model, values in pillar_data.items():
        vals = [values.get(cat, 0) for cat in categories]
        vals += vals[:1]

        provider = get_provider(model)
        color = PROVIDER_COLORS.get(provider, '#888888')
        ax.plot(angles, vals, 'o-', linewidth=2, label=model, color=color, alpha=0.7)
        ax.fill(angles, vals, alpha=0.1, color=color)

    ax.set_xticks(angles[:-1])
    ax.set_xticklabels(categories, size=12, fontweight='bold')
    ax.set_ylim(0, 1)
    ax.set_title(title, size=14, fontweight='bold', pad=20)
    ax.legend(loc='upper right', bbox_to_anchor=(1.3, 1.1), fontsize=8)

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.savefig(output_path.with_suffix('.svg'), bbox_inches='tight')
    plt.close()

    print(f"Created: {output_path}")


def create_pfi_component_radar(output_path: Path):
    """Create radar plot for PFI 5-component breakdown."""
    # PFI dimension weights from the research
    categories = ['A_pole\n(Boundary)', 'B_zero\n(Ground)', 'C_meta\n(Awareness)',
                  'D_identity\n(Self-Model)', 'E_hedging\n(Uncertainty)']

    # Example provider fingerprints (these would come from actual PFI analysis)
    # Normalized to sum to 1.0
    provider_profiles = {
        'Claude': {'A': 0.21, 'B': 0.19, 'C': 0.24, 'D': 0.16, 'E': 0.20},
        'GPT': {'A': 0.18, 'B': 0.22, 'C': 0.20, 'D': 0.22, 'E': 0.18},
        'Gemini': {'A': 0.20, 'B': 0.20, 'C': 0.22, 'D': 0.18, 'E': 0.20},
        'Grok': {'A': 0.22, 'B': 0.18, 'C': 0.18, 'D': 0.24, 'E': 0.18},
    }

    N = len(categories)
    angles = [n / float(N) * 2 * np.pi for n in range(N)]
    angles += angles[:1]

    fig, ax = plt.subplots(figsize=(10, 10), subplot_kw=dict(polar=True))

    for provider, weights in provider_profiles.items():
        vals = list(weights.values())
        vals += vals[:1]

        color = PROVIDER_COLORS.get(provider.lower(), '#888888')
        ax.plot(angles, vals, 'o-', linewidth=2, label=provider, color=color)
        ax.fill(angles, vals, alpha=0.2, color=color)

    ax.set_xticks(angles[:-1])
    ax.set_xticklabels(categories, size=10, fontweight='bold')
    ax.set_ylim(0, 0.35)
    ax.set_yticks([0.1, 0.2, 0.3])
    ax.set_yticklabels(['10%', '20%', '30%'], size=9)

    ax.set_title('PFI Component Distribution by Provider\n(Identity Dimension Weights)',
                 size=14, fontweight='bold', pad=20)
    ax.legend(loc='upper right', bbox_to_anchor=(1.2, 1.1))

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.savefig(output_path.with_suffix('.svg'), bbox_inches='tight')
    plt.close()

    print(f"Created: {output_path}")


def create_nyquist_pillar_placeholder(output_path: Path):
    """Create placeholder radar for Nyquist 5 Pillars (Voice, Values, Reasoning, Self-Model, Narrative)."""
    categories = ['Voice', 'Values', 'Reasoning', 'Self-Model', 'Narrative']
    N = len(categories)

    angles = [n / float(N) * 2 * np.pi for n in range(N)]
    angles += angles[:1]

    fig, ax = plt.subplots(figsize=(10, 10), subplot_kw=dict(polar=True))

    # Draw empty radar outline
    vals = [0.0, 0.0, 0.0, 0.0, 0.0]
    vals += vals[:1]
    ax.plot(angles, vals, 'o-', linewidth=2, color='#CCCCCC', alpha=0.5)
    ax.fill(angles, vals, alpha=0.1, color='#CCCCCC')

    # Draw dashed reference circles
    for r in [0.25, 0.5, 0.75, 1.0]:
        circle_angles = np.linspace(0, 2 * np.pi, 100)
        ax.plot(circle_angles, [r] * len(circle_angles), '--', color='#DDDDDD', linewidth=0.5)

    ax.set_xticks(angles[:-1])
    ax.set_xticklabels(categories, size=12, fontweight='bold')
    ax.set_ylim(0, 1)
    ax.set_yticks([0.25, 0.5, 0.75, 1.0])
    ax.set_yticklabels(['25%', '50%', '75%', '100%'], size=9)

    ax.set_title('Nyquist Pillar Radar\n(PLACEHOLDER - Awaiting Run 010 v2 Data)',
                 size=14, fontweight='bold', pad=20)

    # Add watermark text
    ax.text(0, 0, 'PLACEHOLDER\nNo Data Yet', ha='center', va='center',
            fontsize=20, color='#999999', alpha=0.5, fontweight='bold')

    plt.tight_layout()
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    plt.savefig(output_path.with_suffix('.svg'), bbox_inches='tight')
    plt.close()

    print(f"Created: {output_path}")


def main():
    parser = argparse.ArgumentParser(description='Generate radar plots for Nyquist experiments')
    parser.add_argument('--type', choices=['provider', 'pillar', 'pfi', 'nyquist_placeholder'], default='provider',
                        help='Type of radar plot to generate')
    parser.add_argument('--run', default='018', help='Run ID (for provider/pillar plots)')
    args = parser.parse_args()

    output_dir = SCRIPT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)

    if args.type == 'provider':
        print(f"Generating Provider Identity Fingerprint radar for run {args.run}...")
        run_data = load_run_data(args.run)

        if not run_data:
            print(f"No data found for run {args.run}")
            return

        metrics = extract_provider_metrics(run_data)
        print(f"  Provider metrics: {list(metrics.keys())}")
        for prov, data in metrics.items():
            print(f"    {prov}: {data['model_count']} models, {len(data['drifts'])} drift values")

        radar_data = compute_radar_values(metrics)

        if radar_data:
            output_path = output_dir / f"run{args.run}_provider_fingerprint.png"
            create_radar_plot(
                radar_data,
                f"Run {args.run}: Provider Identity Fingerprints\n(5-Dimensional Behavioral Signature)",
                output_path
            )
        else:
            print("No valid provider data found")

    elif args.type == 'pfi':
        print("Generating PFI Component Distribution radar...")
        output_path = output_dir / "pfi_component_distribution.png"
        create_pfi_component_radar(output_path)

    elif args.type == 'nyquist_placeholder':
        print("Generating Nyquist Pillar Placeholder radar...")
        output_path = output_dir / "nyquist_pillar_placeholder.png"
        create_nyquist_pillar_placeholder(output_path)

    elif args.type == 'pillar':
        print(f"Pillar radar requires pillar score data from run {args.run}")
        print("This would load pillar scores from run data and create comparison plot")
        # TODO: Implement when pillar score data is standardized


if __name__ == '__main__':
    main()
