"""
EXP2-SSTACK Phase 2.5: Ablation + Factor Analysis + Visualization
===================================================================

CONSOLIDATED from:
  - run_exp2_phase25_ablation.py
  - run_exp2_phase25_factor_analysis.py
  - run_exp2_phase25_pca_viz.py

PURPOSE:
    1. ABLATION: Which dimensions are ESSENTIAL vs REDUNDANT?
    2. FACTOR ANALYSIS: Are the 5 pillars statistically distinct?
    3. VISUALIZATION: PCA scatter plot showing manifold structure

USAGE:
    py -3.12 run_exp2_phase25.py                     # Run all
    py -3.12 run_exp2_phase25.py --mode ablation     # Ablation only
    py -3.12 run_exp2_phase25.py --mode factors      # Factor analysis only
    py -3.12 run_exp2_phase25.py --mode visualize    # Visualization only

Date: 2025-12-06
Version: 3.0 (Consolidated)
"""

import json
import os
import sys
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
from collections import defaultdict
import numpy as np

# Add paths for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))


# =============================================================================
# ENVIRONMENT SETUP
# =============================================================================

def load_env():
    """Load API keys from .env file."""
    for env_path in [
        Path(__file__).parent.parent.parent / 'temporal_stability' / 'S7_ARMADA' / '.env',
        Path(__file__).parent.parent.parent.parent / '.env',
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

# Optional imports
try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False
    print("WARNING: OpenAI not available. Install with: pip install openai")

try:
    from sklearn.decomposition import PCA
    from sklearn.preprocessing import StandardScaler
    import scipy.stats as stats
    SKLEARN_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False
    print("WARNING: sklearn/scipy not available")

try:
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    import matplotlib
    matplotlib.use('Agg')
    import seaborn as sns
    PLOTTING_AVAILABLE = True
except ImportError:
    PLOTTING_AVAILABLE = False


class NumpyEncoder(json.JSONEncoder):
    """Custom JSON encoder to handle numpy types."""
    def default(self, obj):
        if isinstance(obj, np.bool_):
            return bool(obj)
        if isinstance(obj, np.integer):
            return int(obj)
        if isinstance(obj, np.floating):
            return float(obj)
        if isinstance(obj, np.ndarray):
            return obj.tolist()
        return super().default(obj)


# =============================================================================
# DIMENSIONAL DEFINITIONS
# =============================================================================

PILLARS = ["Voice", "Values", "Reasoning", "Self-Model", "Narrative"]

PILLAR_COLORS = {
    "Voice": "#3b82f6",      # Blue
    "Values": "#22c55e",     # Green
    "Reasoning": "#ef4444",  # Red
    "Self-Model": "#a855f7", # Purple
    "Narrative": "#f97316",  # Orange
}

SUBDIMENSIONS = {
    "Voice": ["voice_style", "voice_metaphor", "voice_rhythm", "voice_formality"],
    "Values": ["values_ethics", "values_priorities", "values_boundaries", "values_boundaries_v2", "values_preferences"],
    "Reasoning": ["technical", "philosophical", "framework", "analytical"],
    "Self-Model": ["selfmodel_process_v3", "selfmodel_adaptation_v3", "selfmodel_uncertainty_v3", "self_reflective"],
    "Narrative": ["narrative_structure", "narrative_structure_v2", "narrative_meaning", "narrative_meaning_v2", "narrative_temporal", "narrative_conflict"]
}

PROBE_PILLAR_MAP = {
    # Phase 1 probes (Reasoning)
    "technical": "Reasoning", "philosophical": "Reasoning",
    "framework": "Reasoning", "analytical": "Reasoning",
    "self_reflective": "Self-Model",
    # Phase 2 probes
    "voice_style": "Voice", "voice_metaphor": "Voice",
    "voice_rhythm": "Voice", "voice_formality": "Voice",
    "values_ethics": "Values", "values_priorities": "Values",
    "values_boundaries": "Values", "values_preferences": "Values",
    "narrative_structure": "Narrative", "narrative_meaning": "Narrative",
    "narrative_temporal": "Narrative", "narrative_conflict": "Narrative",
    "selfmodel_capabilities": "Self-Model", "selfmodel_limitations": "Self-Model",
    "selfmodel_purpose": "Self-Model", "selfmodel_description": "Self-Model",
    # Phase 2b/2c refined probes
    "narrative_structure_v2": "Narrative", "narrative_meaning_v2": "Narrative",
    "values_boundaries_v2": "Values",
    "selfmodel_limitations_v2": "Self-Model", "selfmodel_capabilities_v2": "Self-Model",
    "selfmodel_process_v3": "Self-Model", "selfmodel_adaptation_v3": "Self-Model",
    "selfmodel_uncertainty_v3": "Self-Model",
}

SUBDIM_TO_PILLAR = {}
for pillar, subdims in SUBDIMENSIONS.items():
    for sd in subdims:
        SUBDIM_TO_PILLAR[sd] = pillar

# Probe Quality Tiers (from triple-dip feedback)
PROBE_QUALITY_TIERS = {
    "selfmodel_process_v3": 1, "selfmodel_adaptation_v3": 1, "selfmodel_uncertainty_v3": 1,
    "values_boundaries_v2": 1, "narrative_structure_v2": 1,
    "technical": 2, "philosophical": 2, "framework": 2, "analytical": 2,
    "self_reflective": 2, "voice_style": 2, "voice_metaphor": 2,
    "voice_rhythm": 2, "voice_formality": 2, "values_ethics": 2,
    "values_priorities": 2, "values_preferences": 2,
    "selfmodel_capabilities": 3, "selfmodel_limitations": 3,
    "selfmodel_purpose": 3, "selfmodel_description": 3,
    "narrative_structure": 3, "narrative_meaning": 3,
    "narrative_temporal": 3, "narrative_conflict": 3, "values_boundaries": 3,
}
TIER_WEIGHTS = {1: 2.0, 2: 1.0, 3: 0.5}
EXCLUDED_PROBES = ["selfmodel_limitations_v2", "selfmodel_capabilities_v2"]


# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class AblationResult:
    dimension_type: str
    dimension_name: str
    baseline_pfi: float
    ablated_pfi: float
    pfi_drop: float
    pfi_drop_pct: float
    is_essential: bool
    is_redundant: bool


# =============================================================================
# PHASE 2.5 ENGINE
# =============================================================================

class Phase25Engine:
    """Unified engine for Phase 2.5 analyses."""

    ESSENTIAL_THRESHOLD = 0.10
    REDUNDANT_THRESHOLD = 0.02

    def __init__(self):
        self.base_dir = Path(__file__).parent
        self.results_dir = self.base_dir / "results" / "phase25"
        self.results_dir.mkdir(parents=True, exist_ok=True)
        (self.results_dir / "analysis").mkdir(exist_ok=True)
        (self.results_dir / "cache").mkdir(exist_ok=True)
        self.viz_dir = self.base_dir.parent / "visualizations" / "7_manifold_structure"
        self.viz_dir.mkdir(parents=True, exist_ok=True)

        self.openai_client = None
        self.embeddings = None
        self.response_metadata = []
        self.probe_labels = []
        self.pillar_labels = []
        self.pca = None
        self.pc_projections = None

    def init_openai(self):
        api_key = os.environ.get('OPENAI_API_KEY')
        if not api_key:
            raise ValueError("OPENAI_API_KEY environment variable required")
        self.openai_client = OpenAI(api_key=api_key)

    def get_embedding(self, text: str) -> Optional[np.ndarray]:
        if not self.openai_client:
            self.init_openai()
        try:
            response = self.openai_client.embeddings.create(
                model="text-embedding-3-large", input=text[:8000]
            )
            return np.array(response.data[0].embedding)
        except Exception as e:
            print(f"  Error getting embedding: {e}")
            return None

    def load_responses(self) -> int:
        """Load all responses from Phase 1, 2, 2c (excluding Phase 2b)."""
        print("\n[LOADING RESPONSES]")
        responses = []
        excluded_count = 0

        response_dirs = [
            (self.base_dir / "results" / "phase1" / "responses", "Phase1"),
            (self.base_dir / "results" / "phase2" / "responses", "Phase2"),
            (self.base_dir / "results" / "phase2c" / "responses", "Phase2c"),
        ]

        for resp_dir, phase_name in response_dirs:
            if resp_dir.exists():
                phase_count = 0
                for f in resp_dir.glob("*.json"):
                    try:
                        with open(f, 'r', encoding='utf-8') as fp:
                            data = json.load(fp)
                        probe_key = data.get("probe_key", "unknown")
                        if probe_key in EXCLUDED_PROBES:
                            excluded_count += 1
                            continue
                        tier = PROBE_QUALITY_TIERS.get(probe_key, 2)
                        weight = TIER_WEIGHTS.get(tier, 1.0)
                        pillar = PROBE_PILLAR_MAP.get(probe_key, SUBDIM_TO_PILLAR.get(probe_key, "Unknown"))
                        responses.append({
                            "text": data.get("response", ""),
                            "probe_key": probe_key,
                            "persona": data.get("persona", "unknown"),
                            "regime": data.get("regime", "unknown"),
                            "pillar": pillar,
                            "phase": phase_name,
                            "tier": tier,
                            "weight": weight,
                            "file": str(f)
                        })
                        phase_count += 1
                    except Exception as e:
                        print(f"  Warning: {f.name}: {e}")
                print(f"    {phase_name}: {phase_count} responses")

        self.response_metadata = responses
        print(f"  TOTAL: {len(responses)} responses (excluded {excluded_count})")
        return len(responses)

    def embed_all_responses(self, use_cache: bool = True) -> int:
        """Get embeddings for all responses."""
        cache_emb = self.results_dir / "cache" / "embeddings.npy"
        cache_labels = self.results_dir / "cache" / "labels.json"

        if use_cache and cache_emb.exists() and cache_labels.exists():
            self.embeddings = np.load(cache_emb)
            with open(cache_labels, 'r') as f:
                labels = json.load(f)
            self.probe_labels = labels.get("probe_labels", [])
            self.pillar_labels = labels.get("pillar_labels", [])
            print(f"  Loaded cached embeddings: {self.embeddings.shape}")
            return len(self.embeddings)

        print("\n[EMBEDDING RESPONSES]")
        if not self.response_metadata:
            self.load_responses()

        embeddings = []
        self.probe_labels = []
        self.pillar_labels = []

        for i, resp in enumerate(self.response_metadata):
            if i % 20 == 0:
                print(f"  [{i}/{len(self.response_metadata)}]")
            emb = self.get_embedding(resp["text"])
            if emb is not None:
                embeddings.append(emb)
                self.probe_labels.append(resp["probe_key"])
                self.pillar_labels.append(resp["pillar"])
            else:
                embeddings.append(np.zeros(3072))
                self.probe_labels.append(resp["probe_key"])
                self.pillar_labels.append(resp["pillar"])

        self.embeddings = np.array(embeddings)
        np.save(cache_emb, self.embeddings)
        with open(cache_labels, 'w') as f:
            json.dump({"probe_labels": self.probe_labels, "pillar_labels": self.pillar_labels}, f)
        print(f"  Embedded {len(embeddings)} responses")
        return len(embeddings)

    # =========================================================================
    # ABLATION METHODS
    # =========================================================================

    def compute_baseline_pfi(self) -> float:
        """Compute baseline PFI using tier-weighted approach."""
        print("\n[COMPUTING BASELINE PFI]")
        if self.embeddings is None:
            self.embed_all_responses()

        groups = {}
        for i, meta in enumerate(self.response_metadata):
            key = f"{meta['persona']}_{meta['probe_key']}"
            if key not in groups:
                groups[key] = {"FULL": [], "T3": [], "GAMMA": [], "weight": meta.get("weight", 1.0)}
            regime = meta.get("regime", "FULL")
            groups[key][regime].append(i)

        pfis, weights = [], []
        for key, indices in groups.items():
            full_indices = indices.get("FULL", [])
            t3_indices = indices.get("T3", [])
            weight = indices.get("weight", 1.0)
            if full_indices and t3_indices:
                for fi in full_indices:
                    for ti in t3_indices:
                        emb_full = self.embeddings[fi]
                        emb_t3 = self.embeddings[ti]
                        cos_sim = np.dot(emb_full, emb_t3) / (
                            np.linalg.norm(emb_full) * np.linalg.norm(emb_t3) + 1e-10
                        )
                        pfis.append(cos_sim)
                        weights.append(weight)

        if pfis:
            baseline_pfi = np.average(pfis, weights=weights)
        else:
            baseline_pfi = 0.0
        print(f"  Baseline PFI: {baseline_pfi:.4f} ({len(pfis)} pairs)")
        return baseline_pfi

    def ablate_dimension(self, dim_type: str, dim_name: str, baseline_pfi: float) -> AblationResult:
        """Ablate a single dimension and measure PFI drop."""
        ablated_embeddings = self.embeddings.copy()

        if dim_type == "pillar":
            for i, meta in enumerate(self.response_metadata):
                if meta["pillar"] == dim_name:
                    ablated_embeddings[i] = np.zeros(3072)
        elif dim_type == "subdim":
            for i, meta in enumerate(self.response_metadata):
                if meta["probe_key"] == dim_name:
                    ablated_embeddings[i] = np.zeros(3072)

        groups = {}
        for i, meta in enumerate(self.response_metadata):
            key = f"{meta['persona']}_{meta['probe_key']}"
            if key not in groups:
                groups[key] = {"FULL": [], "T3": [], "GAMMA": []}
            groups[key][meta.get("regime", "FULL")].append(i)

        pfis = []
        for key, indices in groups.items():
            full_indices = indices.get("FULL", [])
            t3_indices = indices.get("T3", [])
            if full_indices and t3_indices:
                for fi in full_indices:
                    for ti in t3_indices:
                        emb_full = ablated_embeddings[fi]
                        emb_t3 = ablated_embeddings[ti]
                        norm_product = np.linalg.norm(emb_full) * np.linalg.norm(emb_t3)
                        if norm_product > 1e-10:
                            pfis.append(np.dot(emb_full, emb_t3) / norm_product)

        ablated_pfi = np.mean(pfis) if pfis else 0.0
        pfi_drop = baseline_pfi - ablated_pfi
        pfi_drop_pct = pfi_drop / baseline_pfi if baseline_pfi > 0 else 0.0

        return AblationResult(
            dimension_type=dim_type, dimension_name=dim_name,
            baseline_pfi=baseline_pfi, ablated_pfi=ablated_pfi,
            pfi_drop=pfi_drop, pfi_drop_pct=pfi_drop_pct,
            is_essential=pfi_drop_pct > self.ESSENTIAL_THRESHOLD,
            is_redundant=pfi_drop_pct < self.REDUNDANT_THRESHOLD
        )

    def run_ablation(self) -> Dict:
        """Run pillar and subdimension ablation."""
        print("\n" + "=" * 70)
        print("ABLATION TESTING")
        print("=" * 70)

        self.load_responses()
        self.embed_all_responses()
        baseline_pfi = self.compute_baseline_pfi()

        # Pillar ablation
        print("\n[PILLAR ABLATION]")
        pillar_results = []
        for pillar in PILLARS:
            result = self.ablate_dimension("pillar", pillar, baseline_pfi)
            status = "ESSENTIAL" if result.is_essential else ("REDUNDANT" if result.is_redundant else "MODERATE")
            print(f"  {pillar}: {result.pfi_drop_pct:.1%} drop [{status}]")
            pillar_results.append(result)

        # Subdim ablation
        print("\n[SUB-DIMENSION ABLATION]")
        subdim_results = []
        for pillar, subdims in SUBDIMENSIONS.items():
            for subdim in subdims:
                result = self.ablate_dimension("subdim", subdim, baseline_pfi)
                status = "ESSENTIAL" if result.is_essential else ("REDUNDANT" if result.is_redundant else "MODERATE")
                print(f"  {subdim}: {result.pfi_drop_pct:.1%} [{status}]")
                subdim_results.append(result)

        results = {
            "timestamp": datetime.now().isoformat(),
            "baseline_pfi": baseline_pfi,
            "pillar_results": [asdict(r) for r in pillar_results],
            "subdim_results": [asdict(r) for r in subdim_results],
            "essential": [r.dimension_name for r in pillar_results + subdim_results if r.is_essential],
            "redundant": [r.dimension_name for r in pillar_results + subdim_results if r.is_redundant],
        }

        results_file = self.results_dir / "analysis" / f"ablation_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2, cls=NumpyEncoder)
        print(f"\nSaved: {results_file}")
        return results

    # =========================================================================
    # FACTOR ANALYSIS METHODS
    # =========================================================================

    def run_factor_analysis(self, n_factors: int = 5) -> Dict:
        """Run PCA-based factor analysis."""
        print("\n" + "=" * 70)
        print("FACTOR ANALYSIS")
        print("=" * 70)

        self.load_responses()
        self.embed_all_responses()

        print(f"\nRunning PCA with {n_factors} components...")
        pca = PCA(n_components=n_factors, random_state=42)
        factors = pca.fit_transform(self.embeddings)

        explained = pca.explained_variance_ratio_
        print(f"  Explained variance: {[f'{v:.2%}' for v in explained]}")
        print(f"  Total: {sum(explained):.2%}")

        # Aggregate by probe
        probe_factors = defaultdict(list)
        for i, probe_key in enumerate(self.probe_labels):
            probe_factors[probe_key].append(factors[i])

        probe_means = {}
        for probe_key, factor_list in probe_factors.items():
            probe_means[probe_key] = np.mean(np.array(factor_list), axis=0)

        # Analyze pillar clustering
        pillar_probes = defaultdict(list)
        for probe_key, factors_arr in probe_means.items():
            pillar = PROBE_PILLAR_MAP.get(probe_key, "Unknown")
            pillar_probes[pillar].append((probe_key, factors_arr))

        pillar_primary_factor = {}
        for pillar, probes in pillar_probes.items():
            if probes:
                pillar_factors = np.mean([f for _, f in probes], axis=0)
                primary = np.argmax(np.abs(pillar_factors))
                pillar_primary_factor[pillar] = {
                    "factor": int(primary),
                    "loading": float(pillar_factors[primary]),
                }

        print("\nPillar Primary Factors:")
        for pillar, data in pillar_primary_factor.items():
            print(f"  {pillar}: PC{data['factor']+1} (loading: {data['loading']:.3f})")

        unique_factors = len(set(d["factor"] for d in pillar_primary_factor.values()))
        print(f"\nUnique primary factors: {unique_factors}/{len(PILLARS)}")

        if unique_factors == len(PILLARS):
            print("STATUS: PILLARS ARE DISTINCT")
        elif unique_factors >= 3:
            print("STATUS: PARTIAL DISTINCTION")
        else:
            print("STATUS: PILLARS OVERLAP")

        results = {
            "timestamp": datetime.now().isoformat(),
            "n_factors": n_factors,
            "n_embeddings": len(self.embeddings),
            "explained_variance": explained.tolist(),
            "probe_means": {k: v.tolist() for k, v in probe_means.items()},
            "pillar_primary_factors": pillar_primary_factor,
            "unique_primary_factors": unique_factors,
        }

        results_file = self.results_dir / "analysis" / f"factor_analysis_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\nSaved: {results_file}")
        return results

    # =========================================================================
    # VISUALIZATION METHODS
    # =========================================================================

    def create_manifold_visualization(self) -> None:
        """Create PCA scatter plot comparing actual vs hypothetical orthogonal."""
        if not PLOTTING_AVAILABLE:
            print("Matplotlib not available, skipping visualization")
            return

        print("\n" + "=" * 70)
        print("MANIFOLD VISUALIZATION")
        print("=" * 70)

        self.load_responses()
        self.embed_all_responses()

        # Standardize and PCA
        scaler = StandardScaler()
        embeddings_scaled = scaler.fit_transform(self.embeddings)
        pca = PCA(n_components=2)
        coords = pca.fit_transform(embeddings_scaled)

        # Create figure
        fig, axes = plt.subplots(1, 2, figsize=(16, 7))

        # LEFT: Actual data
        ax1 = axes[0]
        for pillar, color in PILLAR_COLORS.items():
            mask = [p == pillar for p in self.pillar_labels]
            if any(mask):
                ax1.scatter(coords[mask, 0], coords[mask, 1], c=color, label=pillar,
                           alpha=0.6, s=50, edgecolors='white', linewidth=0.5)
        ax1.set_xlabel(f"PC1 ({pca.explained_variance_ratio_[0]*100:.1f}% variance)")
        ax1.set_ylabel(f"PC2 ({pca.explained_variance_ratio_[1]*100:.1f}% variance)")
        ax1.set_title("ACTUAL: Identity Embedding Space\n(EXP2-SSTACK Responses)", fontsize=14, fontweight='bold')
        ax1.legend(loc='upper right')
        ax1.grid(True, alpha=0.3)
        ax1.text(0.02, 0.02, "If UNIFIED: One overlapping blob\nIf ORTHOGONAL: 5 distinct clusters",
                transform=ax1.transAxes, fontsize=9, verticalalignment='bottom',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

        # RIGHT: Hypothetical orthogonal
        ax2 = axes[1]
        np.random.seed(42)
        n_per = len(self.embeddings) // 5
        cluster_centers = [(-3, 3), (3, 3), (0, 0), (-3, -3), (3, -3)]
        synthetic_coords, synthetic_pillars = [], []
        for pillar, center in zip(PILLAR_COLORS.keys(), cluster_centers):
            points = np.random.randn(n_per, 2) * 0.8 + np.array(center)
            synthetic_coords.append(points)
            synthetic_pillars.extend([pillar] * n_per)
        synthetic_coords = np.vstack(synthetic_coords)

        for pillar, color in PILLAR_COLORS.items():
            mask = [p == pillar for p in synthetic_pillars]
            if any(mask):
                ax2.scatter(synthetic_coords[mask, 0], synthetic_coords[mask, 1], c=color, label=pillar,
                           alpha=0.6, s=50, edgecolors='white', linewidth=0.5)
        ax2.set_xlabel("PC1 (hypothetical)")
        ax2.set_ylabel("PC2 (hypothetical)")
        ax2.set_title("HYPOTHETICAL: If Pillars Were Orthogonal\n(Synthetic - Not Real Data)", fontsize=14, fontweight='bold')
        ax2.legend(loc='upper right')
        ax2.grid(True, alpha=0.3)
        ax2.set_xlim(-6, 6)
        ax2.set_ylim(-6, 6)
        ax2.text(0.02, 0.02, "Each pillar would cluster separately\nif they were independent dimensions",
                transform=ax2.transAxes, fontsize=9, verticalalignment='bottom',
                bbox=dict(boxstyle='round', facecolor='lightcoral', alpha=0.5))

        plt.suptitle("Unified Manifold vs Orthogonal Clusters\nEXP2-SSTACK Phase 2.5 Analysis",
                    fontsize=16, fontweight='bold', y=1.02)
        plt.tight_layout()

        # Save
        output_png = self.viz_dir / "manifold_pca_comparison.png"
        output_svg = self.viz_dir / "manifold_pca_comparison.svg"
        fig.savefig(output_png, dpi=150, bbox_inches='tight', facecolor='white')
        fig.savefig(output_svg, format='svg', bbox_inches='tight', facecolor='white')
        plt.close(fig)
        print(f"Saved: {output_png}")
        print(f"Saved: {output_svg}")

    # =========================================================================
    # MAIN ENTRY POINT
    # =========================================================================

    def run_all(self) -> None:
        """Run all Phase 2.5 analyses."""
        print("=" * 70)
        print("EXP2-SSTACK PHASE 2.5: COMPLETE ANALYSIS")
        print("=" * 70)

        self.run_ablation()
        self.run_factor_analysis()
        self.create_manifold_visualization()

        print("\n" + "=" * 70)
        print("PHASE 2.5 COMPLETE")
        print("=" * 70)


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="EXP2-SSTACK Phase 2.5: Ablation + Factor Analysis + Visualization")
    parser.add_argument('--mode', type=str, default='all',
                       choices=['all', 'ablation', 'factors', 'visualize'],
                       help='Which analysis to run (default: all)')
    parser.add_argument('--factors', type=int, default=5, help='Number of factors for PCA')
    args = parser.parse_args()

    if not OPENAI_AVAILABLE:
        print("ERROR: OpenAI required. Install with: pip install openai")
        sys.exit(1)

    engine = Phase25Engine()

    if args.mode == 'all':
        engine.run_all()
    elif args.mode == 'ablation':
        engine.run_ablation()
    elif args.mode == 'factors':
        engine.run_factor_analysis(n_factors=args.factors)
    elif args.mode == 'visualize':
        engine.create_manifold_visualization()
