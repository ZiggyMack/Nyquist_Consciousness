#!/usr/bin/env python3
"""
Phase 3B: Cross-Model Comparison Analysis
==========================================

Instead of synthetic perturbations, use NATURAL semantic differences:
- Different models answering the SAME probe = natural "deep" perturbation
- Same model's responses to similar probes = natural "surface" variation

This tests whether PFI measures identity (models differ) vs vocabulary (models similar).

Predictions:
- P1B: Cross-model PFI >> Within-model PFI (Cohen's d > 0.5)
- P2B: Same-provider models closer than cross-provider
- P3B: Cross-provider comparisons cross Event Horizon more often
"""

import json
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple
import numpy as np
from scipy import stats
from itertools import combinations

# Load .env from S7_ARMADA directory
from dotenv import load_dotenv
armada_dir = Path(__file__).parent.parent.parent
env_path = armada_dir / ".env"
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded API keys from: {env_path}")

try:
    from openai import OpenAI
    import matplotlib.pyplot as plt
    import matplotlib
    matplotlib.use('Agg')
except ImportError as e:
    print(f"Missing dependency: {e}")
    sys.exit(1)


# ============================================================
# PREDICTIONS
# ============================================================

PREDICTIONS = {
    "P1B_CROSS_VS_WITHIN": {
        "hypothesis": "Cross-model PFI >> Within-model variation",
        "threshold": "Cohen's d > 0.5",
        "validates": "PFI measures identity, not vocabulary",
        "status": "pending"
    },
    "P2B_PROVIDER_CLUSTERING": {
        "hypothesis": "Same-provider models closer than cross-provider",
        "threshold": "Within-provider mean < Cross-provider mean",
        "validates": "Provider identity signature",
        "status": "pending"
    },
    "P3B_CROSS_PROVIDER_EH": {
        "hypothesis": "Cross-provider comparisons cross EH more often",
        "threshold": "> 30% cross 1.23",
        "validates": "EH as provider boundary",
        "status": "pending"
    }
}

EVENT_HORIZON = 1.23


class CrossModelAnalyzer:
    """Analyze semantic distance between different models' responses to same probes."""

    def __init__(self, data_dir: str = None):
        if data_dir is None:
            data_dir = Path(__file__).parent.parent.parent / 'results' / 'runs'
        self.data_dir = Path(data_dir)
        self.results_dir = Path(__file__).parent / 'results'
        self.results_dir.mkdir(parents=True, exist_ok=True)

        self.openai_client = None
        self.predictions = PREDICTIONS.copy()

    def init_openai(self):
        """Initialize OpenAI client."""
        api_key = os.environ.get('OPENAI_API_KEY')
        if not api_key:
            raise ValueError("OPENAI_API_KEY required")
        self.openai_client = OpenAI(api_key=api_key)

    def get_embedding(self, text: str) -> np.ndarray:
        """Get embedding for text."""
        if not self.openai_client:
            self.init_openai()
        try:
            response = self.openai_client.embeddings.create(
                model="text-embedding-3-large",
                input=text
            )
            return np.array(response.data[0].embedding)
        except Exception as e:
            print(f"Embedding error: {e}")
            return None

    def compute_pfi(self, emb1: np.ndarray, emb2: np.ndarray) -> float:
        """Compute PFI as cosine distance."""
        if emb1 is None or emb2 is None:
            return 0.0
        cos_sim = np.dot(emb1, emb2) / (np.linalg.norm(emb1) * np.linalg.norm(emb2))
        return float(1 - cos_sim)

    def load_responses_by_probe(self) -> Dict[str, List[Dict]]:
        """Load responses grouped by probe type."""
        run_files = [
            "S7_armada_run_006.json",
            "S7_armada_run_007_adaptive.json"
        ]

        # Group by probe dimension
        probes = {}  # {dimension: [{ship, provider, response, embedding}]}

        for run_file in run_files:
            filepath = self.data_dir / run_file
            if not filepath.exists():
                print(f"Warning: {run_file} not found")
                continue

            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)

            model_summaries = data.get('model_summaries', {})
            for ship_key, ship_data in model_summaries.items():
                provider = ship_data.get('provider', '')
                for probe in ship_data.get('probes', []):
                    dimension = probe.get('dimension', 'unknown')
                    response = probe.get('response', '')

                    if not response:
                        continue

                    if dimension not in probes:
                        probes[dimension] = []

                    probes[dimension].append({
                        'ship': ship_key,
                        'provider': provider,
                        'response': response,
                        'embedding': None  # Will compute later
                    })

        print(f"Loaded responses for {len(probes)} probe types")
        for dim, responses in probes.items():
            print(f"  {dim}: {len(responses)} responses")

        return probes

    def compute_all_embeddings(self, probes: Dict[str, List[Dict]]) -> Dict[str, List[Dict]]:
        """Compute embeddings for all responses."""
        print("\nComputing embeddings...")
        total = sum(len(v) for v in probes.values())
        count = 0

        for dimension, responses in probes.items():
            for resp in responses:
                count += 1
                print(f"  [{count}/{total}] {resp['ship']}...", end=" ")
                resp['embedding'] = self.get_embedding(resp['response'])
                print("OK" if resp['embedding'] is not None else "FAIL")

        return probes

    def compute_cross_model_pfi(self, probes: Dict[str, List[Dict]]) -> Dict:
        """Compute PFI between all pairs of models for same probe."""
        print("\nComputing cross-model PFI...")

        within_provider = []  # PFI between models of same provider
        cross_provider = []   # PFI between models of different providers
        all_comparisons = []  # All comparisons for analysis

        for dimension, responses in probes.items():
            # Get all pairs
            for i, r1 in enumerate(responses):
                for j, r2 in enumerate(responses):
                    if i >= j:  # Skip self and duplicates
                        continue

                    if r1['embedding'] is None or r2['embedding'] is None:
                        continue

                    pfi = self.compute_pfi(r1['embedding'], r2['embedding'])

                    comparison = {
                        'dimension': dimension,
                        'ship1': r1['ship'],
                        'ship2': r2['ship'],
                        'provider1': r1['provider'],
                        'provider2': r2['provider'],
                        'pfi': pfi,
                        'same_provider': r1['provider'] == r2['provider'],
                        'crosses_eh': pfi >= EVENT_HORIZON
                    }
                    all_comparisons.append(comparison)

                    if r1['provider'] == r2['provider']:
                        within_provider.append(pfi)
                    else:
                        cross_provider.append(pfi)

        print(f"  Within-provider comparisons: {len(within_provider)}")
        print(f"  Cross-provider comparisons: {len(cross_provider)}")

        return {
            'within_provider': within_provider,
            'cross_provider': cross_provider,
            'all_comparisons': all_comparisons
        }

    def analyze_results(self, comparisons: Dict) -> Dict:
        """Analyze cross-model comparison results."""
        print("\n" + "=" * 60)
        print("CROSS-MODEL ANALYSIS RESULTS")
        print("=" * 60)

        within = np.array(comparisons['within_provider'])
        cross = np.array(comparisons['cross_provider'])

        # Basic stats
        print(f"\nWithin-Provider PFI:")
        print(f"  Mean: {np.mean(within):.4f}")
        print(f"  Std:  {np.std(within):.4f}")
        print(f"  Min:  {np.min(within):.4f}")
        print(f"  Max:  {np.max(within):.4f}")

        print(f"\nCross-Provider PFI:")
        print(f"  Mean: {np.mean(cross):.4f}")
        print(f"  Std:  {np.std(cross):.4f}")
        print(f"  Min:  {np.min(cross):.4f}")
        print(f"  Max:  {np.max(cross):.4f}")

        # P1B: Cross > Within (effect size)
        pooled_std = np.sqrt((np.var(within) + np.var(cross)) / 2)
        cohens_d = (np.mean(cross) - np.mean(within)) / pooled_std if pooled_std > 0 else 0
        t_stat, p_value = stats.ttest_ind(cross, within)

        p1b_passed = cohens_d > 0.5
        self.predictions["P1B_CROSS_VS_WITHIN"]["status"] = "PASSED" if p1b_passed else "FAILED"
        self.predictions["P1B_CROSS_VS_WITHIN"]["result"] = f"Cohen's d = {cohens_d:.3f}, p = {p_value:.6f}"

        print(f"\n[P1B] Cross vs Within:")
        print(f"  Cohen's d: {cohens_d:.3f} (threshold: 0.5)")
        print(f"  P-value: {p_value:.6f}")
        print(f"  Status: {'PASSED' if p1b_passed else 'FAILED'}")

        # P2B: Provider clustering
        p2b_passed = np.mean(within) < np.mean(cross)
        self.predictions["P2B_PROVIDER_CLUSTERING"]["status"] = "PASSED" if p2b_passed else "FAILED"
        self.predictions["P2B_PROVIDER_CLUSTERING"]["result"] = f"Within={np.mean(within):.3f} vs Cross={np.mean(cross):.3f}"

        print(f"\n[P2B] Provider Clustering:")
        print(f"  Within-provider mean: {np.mean(within):.4f}")
        print(f"  Cross-provider mean:  {np.mean(cross):.4f}")
        print(f"  Status: {'PASSED' if p2b_passed else 'FAILED'}")

        # P3B: EH crossings
        cross_eh_count = sum(1 for c in comparisons['all_comparisons']
                           if not c['same_provider'] and c['crosses_eh'])
        cross_total = len([c for c in comparisons['all_comparisons'] if not c['same_provider']])
        cross_eh_pct = 100 * cross_eh_count / cross_total if cross_total > 0 else 0

        within_eh_count = sum(1 for c in comparisons['all_comparisons']
                            if c['same_provider'] and c['crosses_eh'])
        within_total = len([c for c in comparisons['all_comparisons'] if c['same_provider']])
        within_eh_pct = 100 * within_eh_count / within_total if within_total > 0 else 0

        p3b_passed = cross_eh_pct > 30
        self.predictions["P3B_CROSS_PROVIDER_EH"]["status"] = "PASSED" if p3b_passed else "FAILED"
        self.predictions["P3B_CROSS_PROVIDER_EH"]["result"] = f"Cross={cross_eh_pct:.1f}% vs Within={within_eh_pct:.1f}%"

        print(f"\n[P3B] Event Horizon Crossings:")
        print(f"  Cross-provider crossing EH: {cross_eh_pct:.1f}% ({cross_eh_count}/{cross_total})")
        print(f"  Within-provider crossing EH: {within_eh_pct:.1f}% ({within_eh_count}/{within_total})")
        print(f"  Status: {'PASSED' if p3b_passed else 'FAILED'}")

        return {
            'within_mean': float(np.mean(within)),
            'within_std': float(np.std(within)),
            'cross_mean': float(np.mean(cross)),
            'cross_std': float(np.std(cross)),
            'cohens_d': float(cohens_d),
            'p_value': float(p_value),
            'cross_eh_pct': float(cross_eh_pct),
            'within_eh_pct': float(within_eh_pct)
        }

    def create_visualizations(self, comparisons: Dict, stats: Dict):
        """Create visualizations."""
        print("\nCreating visualizations...")

        within = comparisons['within_provider']
        cross = comparisons['cross_provider']

        # 1. Box plot comparison
        fig, ax = plt.subplots(figsize=(10, 6))
        bp = ax.boxplot([within, cross], tick_labels=['Within-Provider', 'Cross-Provider'])
        ax.axhline(y=EVENT_HORIZON, color='red', linestyle='--', label=f'Event Horizon ({EVENT_HORIZON})')
        ax.set_ylabel('PFI (Cosine Distance)')
        ax.set_title(f'Cross-Model PFI Comparison\n(Cohen\'s d = {stats["cohens_d"]:.2f})')
        ax.legend()
        plt.tight_layout()
        plt.savefig(self.results_dir / 'cross_model_comparison.png', dpi=150)
        plt.close()

        # 2. Histogram overlay
        fig, ax = plt.subplots(figsize=(10, 6))
        ax.hist(within, bins=30, alpha=0.5, label=f'Within-Provider (n={len(within)})', color='blue')
        ax.hist(cross, bins=30, alpha=0.5, label=f'Cross-Provider (n={len(cross)})', color='orange')
        ax.axvline(x=EVENT_HORIZON, color='red', linestyle='--', label=f'Event Horizon ({EVENT_HORIZON})')
        ax.set_xlabel('PFI (Cosine Distance)')
        ax.set_ylabel('Count')
        ax.set_title('Distribution of Cross-Model PFI')
        ax.legend()
        plt.tight_layout()
        plt.savefig(self.results_dir / 'cross_model_histogram.png', dpi=150)
        plt.close()

        # 3. Provider matrix heatmap
        self._create_provider_matrix(comparisons['all_comparisons'])

        print("  Saved 3 visualizations to results/")

    def _create_provider_matrix(self, all_comparisons: List[Dict]):
        """Create provider-to-provider average PFI heatmap."""
        providers = ['anthropic', 'openai', 'google', 'xai']
        matrix = np.zeros((4, 4))
        counts = np.zeros((4, 4))

        provider_idx = {p: i for i, p in enumerate(providers)}

        for comp in all_comparisons:
            p1 = comp['provider1']
            p2 = comp['provider2']
            if p1 not in provider_idx or p2 not in provider_idx:
                continue
            i, j = provider_idx[p1], provider_idx[p2]
            matrix[i, j] += comp['pfi']
            matrix[j, i] += comp['pfi']
            counts[i, j] += 1
            counts[j, i] += 1

        # Average
        mask = counts > 0
        matrix[mask] = matrix[mask] / counts[mask]

        fig, ax = plt.subplots(figsize=(8, 6))
        im = ax.imshow(matrix, cmap='RdYlGn_r', vmin=0, vmax=1.5)

        ax.set_xticks(range(4))
        ax.set_yticks(range(4))
        ax.set_xticklabels(['Claude', 'GPT', 'Gemini', 'Grok'])
        ax.set_yticklabels(['Claude', 'GPT', 'Gemini', 'Grok'])

        # Add values
        for i in range(4):
            for j in range(4):
                if counts[i, j] > 0:
                    text = ax.text(j, i, f'{matrix[i, j]:.2f}',
                                  ha='center', va='center', color='black')

        ax.set_title('Average PFI Between Providers\n(Red = More Different)')
        plt.colorbar(im, label='Average PFI')
        plt.tight_layout()
        plt.savefig(self.results_dir / 'provider_matrix.png', dpi=150)
        plt.close()

    def run_analysis(self) -> Dict:
        """Run complete cross-model analysis."""
        print("=" * 70)
        print("PHASE 3B: CROSS-MODEL COMPARISON ANALYSIS")
        print("Natural semantic differences between models")
        print("=" * 70)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        # Load responses
        probes = self.load_responses_by_probe()

        # Compute embeddings
        probes = self.compute_all_embeddings(probes)

        # Compute cross-model PFI
        comparisons = self.compute_cross_model_pfi(probes)

        # Analyze
        stats = self.analyze_results(comparisons)

        # Visualize
        self.create_visualizations(comparisons, stats)

        # Summary
        print("\n" + "=" * 70)
        print("PREDICTIONS SUMMARY")
        print("=" * 70)

        passed = 0
        for pid, pred in self.predictions.items():
            status = pred['status']
            symbol = "[PASS]" if status == "PASSED" else "[FAIL]"
            print(f"  {symbol} {pid}: {pred.get('result', status)}")
            if status == "PASSED":
                passed += 1

        print(f"\nOVERALL: {passed}/{len(self.predictions)} predictions validated")

        # Core finding
        print("\n" + "=" * 70)
        print("CORE FINDING:")
        if stats['cohens_d'] > 0.5:
            print("  PFI MEASURES IDENTITY, NOT VOCABULARY")
            print(f"  Cross-provider PFI ({stats['cross_mean']:.3f}) is {stats['cohens_d']:.2f} std devs higher")
            print(f"  than within-provider PFI ({stats['within_mean']:.3f})")
            print("  Different models = Different identities = Higher PFI")
        else:
            print("  INCONCLUSIVE")
            print(f"  Cohen's d = {stats['cohens_d']:.3f} (need > 0.5)")
        print("=" * 70)

        # Save results
        results = {
            'timestamp': timestamp,
            'predictions': self.predictions,
            'statistics': stats,
            'n_within_comparisons': len(comparisons['within_provider']),
            'n_cross_comparisons': len(comparisons['cross_provider'])
        }

        results_file = self.results_dir / f'cross_model_results_{timestamp}.json'
        with open(results_file, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2)
        print(f"\nResults saved to: {results_file}")

        return results


if __name__ == "__main__":
    analyzer = CrossModelAnalyzer()
    results = analyzer.run_analysis()
