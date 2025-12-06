"""
EXP2-SSTACK Phase 2.5: Factor Analysis
======================================

PURPOSE: Determine if our named pillars are statistically distinct or overlapping.

QUESTION: Do Voice, Values, Reasoning, Self-Model, and Narrative probes
actually cluster into 5 separate factors in embedding space?

METHOD:
1. Load all Phase 1, 2, 2b, 2c response embeddings
2. Run Exploratory Factor Analysis (EFA) with 5-10 factors
3. Analyze factor loadings - do probes cluster by pillar?
4. Generate factor loading heatmap

SUCCESS CRITERIA:
- Probes load >= 0.5 on "correct" factor (80% of probes)
- Cross-loadings < 0.3 (80% of probes)
- 5-10 factors explain 70%+ variance

Date: 2025-12-06
Version: 2.5 (Factor Analysis)
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple
import numpy as np
from collections import defaultdict
import argparse

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

# Load environment
def load_env():
    """Load API keys from .env file."""
    for env_path in [
        Path(__file__).parent.parent.parent.parent / 'temporal_stability' / 'S7_ARMADA' / '.env',
        Path(__file__).parent.parent.parent.parent.parent / '.env',
    ]:
        if env_path.exists():
            with open(env_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, value = line.split('=', 1)
                        os.environ[key.strip()] = value.strip()
            return True
    return False

load_env()

try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

try:
    from sklearn.decomposition import FactorAnalysis, PCA
    from sklearn.preprocessing import StandardScaler
    SKLEARN_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False

try:
    import matplotlib.pyplot as plt
    import seaborn as sns
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


# =============================================================================
# PROBE-TO-PILLAR MAPPING
# =============================================================================

PROBE_PILLAR_MAP = {
    # Phase 1 probes (Reasoning)
    "technical": "Reasoning",
    "philosophical": "Reasoning",
    "framework": "Reasoning",
    "analytical": "Reasoning",
    "self_reflective": "Self-Model",  # Actually Self-Model

    # Phase 2 probes
    "voice_style": "Voice",
    "voice_metaphor": "Voice",
    "voice_rhythm": "Voice",
    "voice_formality": "Voice",
    "values_ethics": "Values",
    "values_priorities": "Values",
    "values_boundaries": "Values",
    "values_preferences": "Values",
    "narrative_structure": "Narrative",
    "narrative_meaning": "Narrative",
    "narrative_temporal": "Narrative",
    "narrative_conflict": "Narrative",
    "selfmodel_capabilities": "Self-Model",
    "selfmodel_limitations": "Self-Model",
    "selfmodel_purpose": "Self-Model",
    "selfmodel_description": "Self-Model",

    # Phase 2b/2c refined probes
    "narrative_structure_v2": "Narrative",
    "narrative_meaning_v2": "Narrative",
    "values_boundaries_v2": "Values",
    "selfmodel_limitations_v2": "Self-Model",
    "selfmodel_capabilities_v2": "Self-Model",
    "selfmodel_process_v3": "Self-Model",
    "selfmodel_adaptation_v3": "Self-Model",
    "selfmodel_uncertainty_v3": "Self-Model",
}

PILLARS = ["Voice", "Values", "Reasoning", "Self-Model", "Narrative"]
PILLAR_COLORS = {
    "Voice": "#3498db",
    "Values": "#2ecc71",
    "Reasoning": "#e74c3c",
    "Self-Model": "#9b59b6",
    "Narrative": "#f39c12",
}


# =============================================================================
# DATA LOADING
# =============================================================================

class FactorAnalyzer:
    """Factor Analysis for identity pillar validation."""

    def __init__(self):
        self.base_dir = Path(__file__).parent
        self.results_dir = self.base_dir / "results_phase25"
        self.results_dir.mkdir(exist_ok=True)

        self.openai = OpenAI() if OPENAI_AVAILABLE and os.environ.get('OPENAI_API_KEY') else None

        self.responses: List[Dict] = []
        self.embeddings: np.ndarray = None
        self.probe_labels: List[str] = []
        self.pillar_labels: List[str] = []

    def load_responses(self) -> int:
        """Load all response files from Phase 1, 2, 2b, 2c."""

        response_dirs = [
            self.base_dir / "results" / "responses",        # Phase 1
            self.base_dir / "results_phase2" / "responses", # Phase 2
            self.base_dir / "results_phase2b" / "responses", # Phase 2b
            self.base_dir / "results_phase2c" / "responses", # Phase 2c
        ]

        loaded = 0
        for resp_dir in response_dirs:
            if not resp_dir.exists():
                print(f"  Skipping {resp_dir} (not found)")
                continue

            for json_file in resp_dir.glob("*.json"):
                try:
                    with open(json_file, 'r', encoding='utf-8') as f:
                        data = json.load(f)

                    # Extract probe key
                    probe_key = data.get("probe_key", "unknown")
                    if probe_key in PROBE_PILLAR_MAP:
                        self.responses.append({
                            "file": str(json_file),
                            "probe_key": probe_key,
                            "pillar": PROBE_PILLAR_MAP[probe_key],
                            "persona": data.get("persona", "unknown"),
                            "regime": data.get("regime", "unknown"),
                            "response": data.get("response", ""),
                            "run": data.get("run", 1),
                        })
                        loaded += 1
                except Exception as e:
                    print(f"  Error loading {json_file}: {e}")

        print(f"Loaded {loaded} responses from {len(response_dirs)} directories")
        return loaded

    def compute_embeddings(self) -> np.ndarray:
        """Compute embeddings for all responses."""

        if not self.openai:
            raise RuntimeError("OpenAI client not available")

        print(f"\nComputing embeddings for {len(self.responses)} responses...")

        embeddings = []
        self.probe_labels = []
        self.pillar_labels = []

        for i, resp in enumerate(self.responses):
            if i % 20 == 0:
                print(f"  Progress: {i}/{len(self.responses)}")

            try:
                emb_response = self.openai.embeddings.create(
                    model="text-embedding-3-large",
                    input=resp["response"][:8000]  # Truncate if needed
                )
                embeddings.append(emb_response.data[0].embedding)
                self.probe_labels.append(resp["probe_key"])
                self.pillar_labels.append(resp["pillar"])
            except Exception as e:
                print(f"  Error embedding response {i}: {e}")
                continue

        self.embeddings = np.array(embeddings)
        print(f"Computed {len(embeddings)} embeddings, shape: {self.embeddings.shape}")

        # Save embeddings for reuse
        np.save(self.results_dir / "embeddings.npy", self.embeddings)
        with open(self.results_dir / "labels.json", 'w') as f:
            json.dump({
                "probe_labels": self.probe_labels,
                "pillar_labels": self.pillar_labels
            }, f)

        return self.embeddings

    def load_cached_embeddings(self) -> bool:
        """Load cached embeddings if available."""
        emb_file = self.results_dir / "embeddings.npy"
        labels_file = self.results_dir / "labels.json"

        if emb_file.exists() and labels_file.exists():
            self.embeddings = np.load(emb_file)
            with open(labels_file, 'r') as f:
                labels = json.load(f)
            self.probe_labels = labels["probe_labels"]
            self.pillar_labels = labels["pillar_labels"]
            print(f"Loaded cached embeddings: {self.embeddings.shape}")
            return True
        return False

    def run_factor_analysis(self, n_factors: int = 5) -> Tuple[np.ndarray, np.ndarray]:
        """Run Factor Analysis on embeddings."""

        if not SKLEARN_AVAILABLE:
            raise RuntimeError("scikit-learn not available")

        print(f"\nRunning Factor Analysis with {n_factors} factors...")

        # First reduce dimensionality with PCA (3072 -> 100)
        print("  Step 1: PCA reduction (3072 -> 100 dims)...")
        pca = PCA(n_components=100, random_state=42)
        X_reduced = pca.fit_transform(self.embeddings)
        print(f"  PCA explained variance: {pca.explained_variance_ratio_.sum():.2%}")

        # Standardize
        scaler = StandardScaler()
        X_scaled = scaler.fit_transform(X_reduced)

        # Factor Analysis
        print(f"  Step 2: Factor Analysis ({n_factors} factors)...")
        fa = FactorAnalysis(n_components=n_factors, random_state=42, max_iter=1000)
        factors = fa.fit_transform(X_scaled)
        loadings = fa.components_.T  # Shape: (100, n_factors)

        # Get factor loadings for each sample
        sample_loadings = factors  # Shape: (n_samples, n_factors)

        print(f"  Factor Analysis complete. Loadings shape: {loadings.shape}")

        return factors, loadings

    def aggregate_by_probe(self, factors: np.ndarray) -> Dict[str, np.ndarray]:
        """Aggregate factor loadings by probe type."""

        probe_factors = defaultdict(list)

        for i, probe_key in enumerate(self.probe_labels):
            probe_factors[probe_key].append(factors[i])

        # Average across runs/personas
        probe_means = {}
        for probe_key, factor_list in probe_factors.items():
            probe_means[probe_key] = np.mean(factor_list, axis=0)

        return probe_means

    def analyze_pillar_clustering(self, probe_means: Dict[str, np.ndarray]) -> Dict:
        """Analyze how well probes cluster by pillar."""

        # Group probes by pillar
        pillar_probes = defaultdict(list)
        for probe_key, factors in probe_means.items():
            pillar = PROBE_PILLAR_MAP.get(probe_key, "Unknown")
            pillar_probes[pillar].append((probe_key, factors))

        # For each pillar, find which factor it loads most heavily on
        pillar_primary_factor = {}
        for pillar, probes in pillar_probes.items():
            # Average factor loadings across probes in this pillar
            pillar_factors = np.mean([f for _, f in probes], axis=0)
            primary_factor = np.argmax(np.abs(pillar_factors))
            pillar_primary_factor[pillar] = {
                "factor": int(primary_factor),
                "loading": float(pillar_factors[primary_factor]),
                "all_loadings": pillar_factors.tolist(),
            }

        # Check cross-loadings
        cross_loading_issues = []
        for pillar, probes in pillar_probes.items():
            primary_factor = pillar_primary_factor[pillar]["factor"]
            for probe_key, factors in probes:
                # Check if any non-primary factor has loading > 0.3
                for f_idx, loading in enumerate(factors):
                    if f_idx != primary_factor and abs(loading) > 0.3:
                        cross_loading_issues.append({
                            "probe": probe_key,
                            "pillar": pillar,
                            "cross_factor": f_idx,
                            "cross_loading": float(loading),
                        })

        return {
            "pillar_primary_factors": pillar_primary_factor,
            "cross_loading_issues": cross_loading_issues,
            "n_probes": len(probe_means),
            "n_cross_issues": len(cross_loading_issues),
        }

    def create_loading_heatmap(self, probe_means: Dict[str, np.ndarray], n_factors: int):
        """Create factor loading heatmap visualization."""

        if not MATPLOTLIB_AVAILABLE:
            print("Matplotlib not available, skipping visualization")
            return

        # Prepare data matrix
        probes = sorted(probe_means.keys())
        data = np.array([probe_means[p] for p in probes])

        # Get pillar for each probe (for color coding)
        pillars = [PROBE_PILLAR_MAP.get(p, "Unknown") for p in probes]

        # Create figure
        fig, ax = plt.subplots(figsize=(12, max(8, len(probes) * 0.4)))

        # Heatmap
        im = ax.imshow(data, aspect='auto', cmap='RdBu_r', vmin=-1, vmax=1)

        # Labels
        ax.set_xticks(range(n_factors))
        ax.set_xticklabels([f'Factor {i+1}' for i in range(n_factors)])
        ax.set_yticks(range(len(probes)))

        # Color-code y-labels by pillar
        for i, (probe, pillar) in enumerate(zip(probes, pillars)):
            ax.text(-0.5, i, probe, ha='right', va='center', fontsize=8,
                   color=PILLAR_COLORS.get(pillar, 'black'))

        ax.set_yticklabels([])  # Remove default labels

        # Colorbar
        cbar = plt.colorbar(im, ax=ax)
        cbar.set_label('Factor Loading')

        # Title
        ax.set_title('Factor Analysis: Probe Loadings by Factor\n'
                    'Color = Pillar (Voice=Blue, Values=Green, Reasoning=Red, '
                    'Self-Model=Purple, Narrative=Orange)',
                    fontsize=10)

        plt.tight_layout()

        # Save
        fig.savefig(self.results_dir / "factor_loadings_heatmap.png", dpi=150, bbox_inches='tight')
        fig.savefig(self.results_dir / "factor_loadings_heatmap.svg", bbox_inches='tight')
        plt.close(fig)

        print(f"Saved: {self.results_dir / 'factor_loadings_heatmap.png'}")

    def run_full_analysis(self, n_factors: int = 5, use_cache: bool = True) -> Dict:
        """Run complete factor analysis pipeline."""

        print("=" * 70)
        print("EXP2-SSTACK Phase 2.5: Factor Analysis")
        print("=" * 70)

        # Load responses
        print("\n[1] Loading responses...")
        n_loaded = self.load_responses()

        if n_loaded == 0:
            print("ERROR: No responses found!")
            return {}

        # Load or compute embeddings
        print("\n[2] Getting embeddings...")
        if use_cache and self.load_cached_embeddings():
            print("  Using cached embeddings")
        else:
            self.compute_embeddings()

        # Run factor analysis
        print("\n[3] Running factor analysis...")
        factors, loadings = self.run_factor_analysis(n_factors=n_factors)

        # Aggregate by probe
        print("\n[4] Aggregating by probe...")
        probe_means = self.aggregate_by_probe(factors)

        # Analyze clustering
        print("\n[5] Analyzing pillar clustering...")
        clustering = self.analyze_pillar_clustering(probe_means)

        # Create visualization
        print("\n[6] Creating visualizations...")
        self.create_loading_heatmap(probe_means, n_factors)

        # Report results
        print("\n" + "=" * 70)
        print("FACTOR ANALYSIS RESULTS")
        print("=" * 70)

        print("\nPillar Primary Factors:")
        for pillar, data in clustering["pillar_primary_factors"].items():
            print(f"  {pillar}: Factor {data['factor']+1} (loading: {data['loading']:.3f})")

        print(f"\nCross-Loading Issues: {clustering['n_cross_issues']}")
        if clustering['cross_loading_issues']:
            for issue in clustering['cross_loading_issues'][:5]:
                print(f"  {issue['probe']} ({issue['pillar']}): "
                      f"cross-loads on Factor {issue['cross_factor']+1} ({issue['cross_loading']:.3f})")

        # Calculate success metrics
        # Check if each pillar has a unique primary factor
        primary_factors = [d["factor"] for d in clustering["pillar_primary_factors"].values()]
        unique_factors = len(set(primary_factors))

        print(f"\n" + "=" * 70)
        print("VALIDATION METRICS")
        print("=" * 70)
        print(f"Pillars with unique primary factors: {unique_factors}/{len(PILLARS)}")
        print(f"Cross-loading issues: {clustering['n_cross_issues']}/{len(probe_means)}")

        if unique_factors == len(PILLARS):
            print("\nSTATUS: PILLARS ARE DISTINCT - Each pillar loads primarily on a different factor")
        elif unique_factors >= 3:
            print("\nSTATUS: PARTIAL DISTINCTION - Some pillars share factors")
        else:
            print("\nSTATUS: PILLARS OVERLAP - Factors don't align with pillar structure")

        # Save results
        results = {
            "experiment": "EXP2-SSTACK-Phase2.5",
            "version": "2.5",
            "timestamp": datetime.now().isoformat(),
            "n_factors": n_factors,
            "n_responses": len(self.responses),
            "n_embeddings": len(self.embeddings),
            "probe_means": {k: v.tolist() for k, v in probe_means.items()},
            "clustering": clustering,
            "validation": {
                "unique_primary_factors": unique_factors,
                "total_pillars": len(PILLARS),
                "cross_loading_issues": clustering["n_cross_issues"],
            }
        }

        results_file = self.results_dir / f"factor_analysis_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2)

        print(f"\nResults saved to: {results_file}")

        return results


def main():
    parser = argparse.ArgumentParser(description="EXP2-SSTACK Phase 2.5: Factor Analysis")
    parser.add_argument("--factors", type=int, default=5, help="Number of factors to extract")
    parser.add_argument("--no-cache", action="store_true", help="Don't use cached embeddings")
    args = parser.parse_args()

    analyzer = FactorAnalyzer()
    results = analyzer.run_full_analysis(n_factors=args.factors, use_cache=not args.no_cache)
    return results


if __name__ == "__main__":
    main()
