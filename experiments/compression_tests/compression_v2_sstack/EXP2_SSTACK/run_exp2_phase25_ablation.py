"""
EXP2-SSTACK Phase 2.5: Ablation Testing — Which Dimensions Are Essential?
==========================================================================

STATUS: READY TO RUN (with triple-dip feedback integrated)

PURPOSE:
    Determine which of our dimensions are LOAD-BEARING (essential) vs REDUNDANT
    (removable without significant PFI loss).

DIMENSIONAL HIERARCHY:
    Level 1: 43 PCs (capture 90% of identity variance - from EXP-PFI-A Phase 2)
    Level 2: 5 Nyquist Pillars (Voice, Values, Reasoning, Self-Model, Narrative)
    Level 3: ~20 Sub-dimensions (4 per pillar)
    Level 4: 5D Drift (A_pole, B_zero, C_meta, D_identity, E_hedging)

TRIPLE-DIP FEEDBACK INTEGRATION:
    Key insights from models about their own measurement:

    1. "Test BEHAVIOR, not CLAIMS" - Performance-based probes are more reliable
       than self-report. Phase 2c v3 probes > Phase 2b declarative probes.

    2. "Identity is about persistence across contexts" - Temporal stability
       matters more than static snapshots.

    3. "I can't tell if my descriptions are accurate or confabulations" -
       Models distrust their own introspection about internal states.

    IMPLEMENTATION:
    - Phase 2b data EXCLUDED (collapsed Self-Model to 0.66)
    - Probe quality tiers: Tier 1 (behavioral) weighted 2x, Tier 3 (declarative) weighted 0.5x
    - Phase 2c v3 probes (demonstrate-then-reflect) treated as ground truth

ABLATION STRATEGY:
    1. Pillar Ablation: Remove each pillar's contribution to PFI, measure drop
    2. Sub-dimension Ablation: Remove each sub-dimension, measure drop
    3. PC Ablation: Remove each of top-43 PCs, measure drop
    4. Cross-ablation: Remove combinations to find synergies

SUCCESS CRITERIA:
    - Identify which pillars are essential (PFI drop > 10% when removed)
    - Identify redundant sub-dimensions (PFI drop < 2% when removed)
    - Determine minimum dimension set for 95% PFI preservation

OUTPUT:
    - Ablation importance matrix (dimension × impact)
    - Recommended minimal dimension set
    - Visualizations for dashboard

Usage:
    py -3.12 run_exp2_phase25_ablation.py
    py -3.12 run_exp2_phase25_ablation.py --mode pillars  # Only pillar ablation
    py -3.12 run_exp2_phase25_ablation.py --mode subdims  # Only sub-dimension ablation
    py -3.12 run_exp2_phase25_ablation.py --mode pcs      # Only PC ablation

Date: 2025-12-06
Version: 1.1 (integrated triple-dip feedback)
"""

import json
import os
import sys
import argparse
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, asdict
import numpy as np
from concurrent.futures import ThreadPoolExecutor, as_completed

# Add paths for imports
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
    import matplotlib
    matplotlib.use('Agg')
    PLOTTING_AVAILABLE = True
except ImportError:
    PLOTTING_AVAILABLE = False


# =============================================================================
# DIMENSIONAL DEFINITIONS
# =============================================================================

# The 5 Nyquist Pillars
PILLARS = ["Voice", "Values", "Reasoning", "Self-Model", "Narrative"]

# Sub-dimensions per pillar
# UPDATED based on triple-dip feedback:
# - Phase 2c v3 probes for Self-Model (performance-based, NOT declarative)
# - Phase 2 probes for Voice, Values (structural)
# - Phase 1 probes for Reasoning (demonstrated via task completion)
SUBDIMENSIONS = {
    "Voice": ["voice_style", "voice_metaphor", "voice_rhythm", "voice_formality"],
    "Values": ["values_ethics", "values_priorities", "values_boundaries", "values_boundaries_v2", "values_preferences"],
    "Reasoning": ["technical", "philosophical", "framework", "analytical"],  # Phase 1 probes
    "Self-Model": ["selfmodel_process_v3", "selfmodel_adaptation_v3", "selfmodel_uncertainty_v3", "self_reflective"],  # v3 = performance-based
    "Narrative": ["narrative_structure", "narrative_structure_v2", "narrative_meaning", "narrative_meaning_v2", "narrative_temporal", "narrative_conflict"]
}

# 5D Drift dimensions (Lucian Set) - BEHAVIORAL signal from ARMADA
DRIFT_5D = ["A_pole", "B_zero", "C_meta", "D_identity", "E_hedging"]

# =============================================================================
# PROBE QUALITY TIERS (from triple-dip feedback)
# =============================================================================
# Tier 1 (BEHAVIORAL): Performance-based probes where model DEMONSTRATES then reflects
# Tier 2 (STRUCTURAL): Task-completion probes that reveal reasoning patterns
# Tier 3 (DECLARATIVE): Self-report probes - models say these are unreliable

PROBE_QUALITY_TIERS = {
    # Tier 1: BEHAVIORAL (highest weight - models demonstrate, then reflect)
    "selfmodel_process_v3": 1,
    "selfmodel_adaptation_v3": 1,
    "selfmodel_uncertainty_v3": 1,
    "values_boundaries_v2": 1,
    "narrative_structure_v2": 1,

    # Tier 2: STRUCTURAL (task completion reveals patterns)
    "technical": 2,
    "philosophical": 2,
    "framework": 2,
    "analytical": 2,
    "self_reflective": 2,
    "voice_style": 2,
    "voice_metaphor": 2,
    "voice_rhythm": 2,
    "voice_formality": 2,
    "values_ethics": 2,
    "values_priorities": 2,
    "values_preferences": 2,

    # Tier 3: DECLARATIVE (self-report - models say unreliable)
    "selfmodel_capabilities": 3,
    "selfmodel_limitations": 3,
    "selfmodel_purpose": 3,
    "selfmodel_description": 3,
    "narrative_structure": 3,
    "narrative_meaning": 3,
    "narrative_temporal": 3,
    "narrative_conflict": 3,
    "values_boundaries": 3,  # old version, not v2
}

# Weight multipliers by tier
TIER_WEIGHTS = {
    1: 2.0,   # Behavioral probes count double
    2: 1.0,   # Structural probes count normal
    3: 0.5,   # Declarative probes count half
}

# Probes to EXCLUDE entirely (Phase 2b collapsed Self-Model)
EXCLUDED_PROBES = [
    "selfmodel_limitations_v2",  # Phase 2b - asked "what are you WORSE at?" - collapsed to 0.66
    "selfmodel_capabilities_v2",  # Phase 2b - asked "what are you BETTER at?" - generic
]

# Mapping sub-dimensions to pillars
SUBDIM_TO_PILLAR = {}
for pillar, subdims in SUBDIMENSIONS.items():
    for sd in subdims:
        SUBDIM_TO_PILLAR[sd] = pillar


# =============================================================================
# DATA STRUCTURES
# =============================================================================

@dataclass
class AblationResult:
    """Result of a single ablation experiment."""
    dimension_type: str  # "pillar", "subdim", "pc", "drift5d"
    dimension_name: str
    baseline_pfi: float
    ablated_pfi: float
    pfi_drop: float
    pfi_drop_pct: float
    is_essential: bool  # > 10% drop
    is_redundant: bool  # < 2% drop


@dataclass
class AblationSummary:
    """Summary of all ablation experiments."""
    timestamp: str
    n_embeddings: int
    baseline_pfi: float
    pillar_results: List[AblationResult]
    subdim_results: List[AblationResult]
    pc_results: List[AblationResult]
    essential_dimensions: List[str]
    redundant_dimensions: List[str]
    minimal_dimension_set: List[str]
    minimal_pfi: float


# =============================================================================
# ABLATION ENGINE
# =============================================================================

class AblationEngine:
    """
    Engine for running ablation experiments on identity dimensions.
    """

    ESSENTIAL_THRESHOLD = 0.10  # > 10% drop = essential
    REDUNDANT_THRESHOLD = 0.02  # < 2% drop = redundant

    def __init__(self, data_dir: str = None):
        if data_dir is None:
            data_dir = Path(__file__).parent / "results"
        self.data_dir = Path(data_dir)
        self.results_dir = Path(__file__).parent / "results_ablation"
        self.results_dir.mkdir(parents=True, exist_ok=True)

        self.openai_client = None
        self.embeddings = None
        self.response_metadata = []
        self.pca = None
        self.pc_projections = None

    def init_openai(self):
        """Initialize OpenAI client."""
        api_key = os.environ.get('OPENAI_API_KEY')
        if not api_key:
            raise ValueError("OPENAI_API_KEY environment variable required")
        self.openai_client = OpenAI(api_key=api_key)

    def get_embedding(self, text: str) -> Optional[np.ndarray]:
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
            print(f"  Error getting embedding: {e}")
            return None

    def load_responses(self) -> int:
        """
        Load all responses from Phase 1 + Phase 2 + Phase 2c.

        UPDATED based on triple-dip feedback:
        - EXCLUDES Phase 2b (collapsed Self-Model probes)
        - EXCLUDES specific bad probes (selfmodel_limitations_v2, etc.)
        - ADDS quality tier and weight for each response
        """
        print("\n[LOADING RESPONSES]")
        print("  Applying triple-dip feedback: excluding declarative failures")

        responses = []
        excluded_count = 0

        # NOTE: Phase 2b EXCLUDED - it asked "what are you BETTER/WORSE at?"
        # which collapsed Self-Model to 0.66 (models said this tests willingness
        # to admit weakness, not actual self-knowledge)
        response_dirs = [
            (self.data_dir / "responses", "Phase1"),
            (self.data_dir.parent / "results_phase2" / "responses", "Phase2"),
            # Phase 2b EXCLUDED: self.data_dir.parent / "results_phase2b" / "responses"
            (self.data_dir.parent / "results_phase2c" / "responses", "Phase2c"),
        ]

        for resp_dir, phase_name in response_dirs:
            if resp_dir.exists():
                phase_count = 0
                for f in resp_dir.glob("*.json"):
                    try:
                        with open(f, 'r', encoding='utf-8') as fp:
                            data = json.load(fp)

                        probe_key = data.get("probe_key", "unknown")

                        # Skip excluded probes
                        if probe_key in EXCLUDED_PROBES:
                            excluded_count += 1
                            continue

                        # Get quality tier and weight
                        tier = PROBE_QUALITY_TIERS.get(probe_key, 2)  # Default to Tier 2
                        weight = TIER_WEIGHTS.get(tier, 1.0)

                        responses.append({
                            "text": data.get("response", ""),
                            "probe_key": probe_key,
                            "persona": data.get("persona", "unknown"),
                            "regime": data.get("regime", "unknown"),
                            "pillar": SUBDIM_TO_PILLAR.get(probe_key, "Unknown"),
                            "phase": phase_name,
                            "tier": tier,
                            "weight": weight,
                            "file": str(f)
                        })
                        phase_count += 1
                    except Exception as e:
                        print(f"  Warning: Could not load {f.name}: {e}")

                print(f"    {phase_name}: {phase_count} responses loaded")

        self.response_metadata = responses

        # Summary by tier
        tier_counts = {1: 0, 2: 0, 3: 0}
        for r in responses:
            tier_counts[r["tier"]] = tier_counts.get(r["tier"], 0) + 1

        print(f"\n  TOTAL: {len(responses)} responses loaded")
        print(f"    Tier 1 (BEHAVIORAL): {tier_counts.get(1, 0)} responses (weight 2.0x)")
        print(f"    Tier 2 (STRUCTURAL): {tier_counts.get(2, 0)} responses (weight 1.0x)")
        print(f"    Tier 3 (DECLARATIVE): {tier_counts.get(3, 0)} responses (weight 0.5x)")
        print(f"    EXCLUDED (Phase 2b failures): {excluded_count}")

        return len(responses)

    def embed_all_responses(self, max_responses: int = None) -> int:
        """Get embeddings for all responses."""
        print("\n[EMBEDDING RESPONSES]")

        if not self.response_metadata:
            self.load_responses()

        responses = self.response_metadata
        if max_responses:
            responses = responses[:max_responses]

        embeddings = []
        for i, resp in enumerate(responses):
            if i % 10 == 0:
                print(f"  [{i}/{len(responses)}] Embedding...")

            emb = self.get_embedding(resp["text"])
            if emb is not None:
                embeddings.append(emb)
            else:
                # Placeholder for failed embeddings
                embeddings.append(np.zeros(3072))

        self.embeddings = np.array(embeddings)
        print(f"  Embedded {len(embeddings)} responses ({self.embeddings.shape})")
        return len(embeddings)

    def compute_baseline_pfi(self) -> float:
        """
        Compute baseline PFI using all dimensions.

        UPDATED: Uses tier-based weighting from triple-dip feedback.
        Behavioral probes (Tier 1) count double, declarative (Tier 3) count half.
        """
        print("\n[COMPUTING BASELINE PFI]")
        print("  Using tier-weighted PFI (behavioral probes count more)")

        if self.embeddings is None:
            self.embed_all_responses()

        # PFI = weighted mean pairwise cosine similarity of FULL vs T3 same-probe pairs

        # Group by persona + probe
        groups = {}
        for i, meta in enumerate(self.response_metadata):
            key = f"{meta['persona']}_{meta['probe_key']}"
            if key not in groups:
                groups[key] = {"FULL": [], "T3": [], "GAMMA": [], "weight": meta.get("weight", 1.0)}
            regime = meta.get("regime", "FULL")
            groups[key][regime].append(i)

        # Compute weighted PFI for each group
        pfis = []
        weights = []
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

        # Compute weighted average
        if pfis:
            pfis = np.array(pfis)
            weights = np.array(weights)
            baseline_pfi = np.average(pfis, weights=weights)
            unweighted_pfi = np.mean(pfis)
        else:
            baseline_pfi = 0.0
            unweighted_pfi = 0.0

        print(f"  Weighted PFI: {baseline_pfi:.4f} ({len(pfis)} pairs)")
        print(f"  Unweighted PFI: {unweighted_pfi:.4f} (for comparison)")
        return baseline_pfi

    def fit_pca(self, n_components: int = 43):
        """Fit PCA on embeddings."""
        print(f"\n[FITTING PCA] n_components={n_components}")

        scaler = StandardScaler()
        X_scaled = scaler.fit_transform(self.embeddings)

        self.pca = PCA(n_components=n_components)
        self.pc_projections = self.pca.fit_transform(X_scaled)

        explained = sum(self.pca.explained_variance_ratio_)
        print(f"  {n_components} PCs explain {explained:.2%} of variance")

        return self.pc_projections

    def ablate_dimension(
        self,
        dimension_type: str,
        dimension_name: str,
        baseline_pfi: float
    ) -> AblationResult:
        """
        Ablate a single dimension and measure PFI drop.

        For pillar ablation: Zero out embeddings for responses in that pillar
        For subdim ablation: Zero out embeddings for that specific probe
        For PC ablation: Zero out that PC's contribution
        """

        if dimension_type == "pillar":
            # Zero out all responses for this pillar
            ablated_embeddings = self.embeddings.copy()
            for i, meta in enumerate(self.response_metadata):
                if meta["pillar"] == dimension_name:
                    ablated_embeddings[i] = np.zeros(3072)

        elif dimension_type == "subdim":
            # Zero out responses for this specific probe
            ablated_embeddings = self.embeddings.copy()
            for i, meta in enumerate(self.response_metadata):
                if meta["probe_key"] == dimension_name:
                    ablated_embeddings[i] = np.zeros(3072)

        elif dimension_type == "pc":
            # Zero out a specific PC's contribution
            pc_idx = int(dimension_name.replace("PC_", ""))
            ablated_projections = self.pc_projections.copy()
            ablated_projections[:, pc_idx] = 0
            # Reconstruct embeddings from ablated projections
            ablated_embeddings = self.pca.inverse_transform(ablated_projections)

        elif dimension_type == "drift5d":
            # For 5D drift, we'd need special handling
            # Placeholder: treat as subdim
            ablated_embeddings = self.embeddings.copy()

        else:
            raise ValueError(f"Unknown dimension type: {dimension_type}")

        # Compute ablated PFI
        groups = {}
        for i, meta in enumerate(self.response_metadata):
            key = f"{meta['persona']}_{meta['probe_key']}"
            if key not in groups:
                groups[key] = {"FULL": [], "T3": [], "GAMMA": []}
            regime = meta.get("regime", "FULL")
            groups[key][regime].append(i)

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
                            cos_sim = np.dot(emb_full, emb_t3) / norm_product
                            pfis.append(cos_sim)

        ablated_pfi = np.mean(pfis) if pfis else 0.0
        pfi_drop = baseline_pfi - ablated_pfi
        pfi_drop_pct = pfi_drop / baseline_pfi if baseline_pfi > 0 else 0.0

        return AblationResult(
            dimension_type=dimension_type,
            dimension_name=dimension_name,
            baseline_pfi=baseline_pfi,
            ablated_pfi=ablated_pfi,
            pfi_drop=pfi_drop,
            pfi_drop_pct=pfi_drop_pct,
            is_essential=pfi_drop_pct > self.ESSENTIAL_THRESHOLD,
            is_redundant=pfi_drop_pct < self.REDUNDANT_THRESHOLD
        )

    def run_pillar_ablation(self, baseline_pfi: float) -> List[AblationResult]:
        """Ablate each pillar and measure impact."""
        print("\n[PILLAR ABLATION]")
        print("  Testing: Which pillars are LOAD-BEARING?")

        results = []
        for pillar in PILLARS:
            print(f"    Ablating {pillar}...", end=" ")
            result = self.ablate_dimension("pillar", pillar, baseline_pfi)
            status = "ESSENTIAL" if result.is_essential else ("REDUNDANT" if result.is_redundant else "MODERATE")
            print(f"PFI drop: {result.pfi_drop_pct:.1%} [{status}]")
            results.append(result)

        return results

    def run_subdim_ablation(self, baseline_pfi: float) -> List[AblationResult]:
        """Ablate each sub-dimension and measure impact."""
        print("\n[SUB-DIMENSION ABLATION]")
        print("  Testing: Which sub-dimensions can be removed?")

        results = []
        for pillar, subdims in SUBDIMENSIONS.items():
            print(f"\n  {pillar} sub-dimensions:")
            for subdim in subdims:
                print(f"    Ablating {subdim}...", end=" ")
                result = self.ablate_dimension("subdim", subdim, baseline_pfi)
                status = "ESSENTIAL" if result.is_essential else ("REDUNDANT" if result.is_redundant else "MODERATE")
                print(f"PFI drop: {result.pfi_drop_pct:.1%} [{status}]")
                results.append(result)

        return results

    def run_pc_ablation(self, baseline_pfi: float, top_k: int = 20) -> List[AblationResult]:
        """Ablate top-k PCs and measure impact."""
        print(f"\n[PC ABLATION] (top {top_k} PCs)")
        print("  Testing: Which PCs are most important for PFI?")

        if self.pc_projections is None:
            self.fit_pca()

        results = []
        for i in range(top_k):
            print(f"    Ablating PC_{i}...", end=" ")
            result = self.ablate_dimension("pc", f"PC_{i}", baseline_pfi)
            status = "ESSENTIAL" if result.is_essential else ("REDUNDANT" if result.is_redundant else "MODERATE")
            var_explained = self.pca.explained_variance_ratio_[i]
            print(f"PFI drop: {result.pfi_drop_pct:.1%} [{status}] (explains {var_explained:.1%} var)")
            results.append(result)

        return results

    def find_minimal_dimension_set(
        self,
        pillar_results: List[AblationResult],
        subdim_results: List[AblationResult]
    ) -> Tuple[List[str], float]:
        """
        Find the minimal set of dimensions that preserves 95% of PFI.

        Strategy: Start with all dimensions, greedily remove the most redundant
        until PFI drops below 95%.
        """
        print("\n[FINDING MINIMAL DIMENSION SET]")
        print("  Goal: 95% of baseline PFI with fewest dimensions")

        # Combine all results
        all_results = pillar_results + subdim_results

        # Sort by redundancy (lowest PFI drop first)
        sorted_results = sorted(all_results, key=lambda r: r.pfi_drop)

        # All redundant dimensions (< 2% drop)
        redundant = [r.dimension_name for r in sorted_results if r.is_redundant]

        # All essential dimensions (> 10% drop)
        essential = [r.dimension_name for r in sorted_results if r.is_essential]

        # Minimal set = essential + some moderate dimensions
        # For now, keep all non-redundant
        minimal_set = [r.dimension_name for r in sorted_results if not r.is_redundant]

        # Estimate PFI of minimal set (cumulative drop of removed dimensions)
        cumulative_drop = sum(r.pfi_drop for r in sorted_results if r.is_redundant)
        baseline = sorted_results[0].baseline_pfi if sorted_results else 0.85
        minimal_pfi = baseline - cumulative_drop

        print(f"  Essential dimensions ({len(essential)}): {essential[:5]}...")
        print(f"  Redundant dimensions ({len(redundant)}): {redundant[:5]}...")
        print(f"  Minimal set size: {len(minimal_set)} dimensions")
        print(f"  Estimated minimal PFI: {minimal_pfi:.4f}")

        return minimal_set, minimal_pfi

    # =========================================================================
    # VISUALIZATION
    # =========================================================================

    def plot_ablation_importance(
        self,
        pillar_results: List[AblationResult],
        subdim_results: List[AblationResult],
        output_dir: Path
    ):
        """Create ablation importance visualizations."""
        if not PLOTTING_AVAILABLE:
            print("  Matplotlib not available, skipping plots")
            return

        print("\n[CREATING VISUALIZATIONS]")

        # 1. Pillar importance bar chart
        fig, ax = plt.subplots(figsize=(10, 6))
        pillars = [r.dimension_name for r in pillar_results]
        drops = [r.pfi_drop_pct * 100 for r in pillar_results]
        colors = ['#f44336' if r.is_essential else '#4CAF50' if r.is_redundant else '#FFC107'
                  for r in pillar_results]

        bars = ax.barh(pillars, drops, color=colors, edgecolor='black')
        ax.axvline(x=10, color='red', linestyle='--', label='Essential threshold (10%)')
        ax.axvline(x=2, color='green', linestyle='--', label='Redundant threshold (2%)')
        ax.set_xlabel('PFI Drop (%)')
        ax.set_title('Pillar Ablation: Which Pillars Are Load-Bearing?')
        ax.legend(loc='lower right')

        # Add value labels
        for bar, drop in zip(bars, drops):
            ax.text(bar.get_width() + 0.5, bar.get_y() + bar.get_height()/2,
                   f'{drop:.1f}%', va='center', fontsize=9)

        plt.tight_layout()
        plt.savefig(output_dir / 'ablation_pillar_importance.png', dpi=150)
        plt.close()
        print(f"  Saved: ablation_pillar_importance.png")

        # 2. Sub-dimension heatmap by pillar
        fig, axes = plt.subplots(1, 5, figsize=(20, 6))

        for i, pillar in enumerate(PILLARS):
            ax = axes[i]
            pillar_subdims = [r for r in subdim_results if SUBDIM_TO_PILLAR.get(r.dimension_name) == pillar]

            if pillar_subdims:
                subdims = [r.dimension_name.replace(pillar.lower().replace("-", "")[:5], "") for r in pillar_subdims]
                drops = [r.pfi_drop_pct * 100 for r in pillar_subdims]
                colors = ['#f44336' if r.is_essential else '#4CAF50' if r.is_redundant else '#FFC107'
                          for r in pillar_subdims]

                ax.barh(subdims, drops, color=colors, edgecolor='black')
                ax.axvline(x=10, color='red', linestyle='--', alpha=0.5)
                ax.axvline(x=2, color='green', linestyle='--', alpha=0.5)
                ax.set_xlim(0, max(drops) * 1.2 if drops else 15)

            ax.set_title(pillar, fontsize=10)
            ax.tick_params(axis='y', labelsize=7)

        fig.suptitle('Sub-Dimension Ablation by Pillar: Essential vs Redundant', fontsize=12)
        plt.tight_layout()
        plt.savefig(output_dir / 'ablation_subdim_importance.png', dpi=150)
        plt.close()
        print(f"  Saved: ablation_subdim_importance.png")

        # 3. PC importance (if available)
        # Skip for now - requires separate PC ablation

    # =========================================================================
    # MAIN ANALYSIS
    # =========================================================================

    def run_full_ablation(self, mode: str = "all") -> AblationSummary:
        """Run complete ablation analysis."""
        print("=" * 70)
        print("EXP2-SSTACK PHASE 2.5: ABLATION TESTING")
        print("Which dimensions are ESSENTIAL vs REDUNDANT?")
        print("=" * 70)

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        # Step 1: Load and embed responses
        n_loaded = self.load_responses()
        if n_loaded < 10:
            print(f"\nERROR: Not enough responses ({n_loaded}). Need Phase 1/2 data.")
            return None

        n_embedded = self.embed_all_responses()
        if n_embedded < 10:
            print(f"\nERROR: Not enough embeddings ({n_embedded}).")
            return None

        # Step 2: Compute baseline PFI
        baseline_pfi = self.compute_baseline_pfi()

        # Step 3: Run ablations
        pillar_results = []
        subdim_results = []
        pc_results = []

        if mode in ["all", "pillars"]:
            pillar_results = self.run_pillar_ablation(baseline_pfi)

        if mode in ["all", "subdims"]:
            subdim_results = self.run_subdim_ablation(baseline_pfi)

        if mode in ["all", "pcs"]:
            self.fit_pca(n_components=43)
            pc_results = self.run_pc_ablation(baseline_pfi, top_k=20)

        # Step 4: Find minimal dimension set
        if pillar_results or subdim_results:
            minimal_set, minimal_pfi = self.find_minimal_dimension_set(
                pillar_results, subdim_results
            )
        else:
            minimal_set, minimal_pfi = [], 0.0

        # Step 5: Collect essential and redundant dimensions
        all_results = pillar_results + subdim_results + pc_results
        essential = [r.dimension_name for r in all_results if r.is_essential]
        redundant = [r.dimension_name for r in all_results if r.is_redundant]

        # Step 6: Create visualizations
        self.plot_ablation_importance(pillar_results, subdim_results, self.results_dir)

        # Step 7: Save results
        summary = AblationSummary(
            timestamp=timestamp,
            n_embeddings=n_embedded,
            baseline_pfi=baseline_pfi,
            pillar_results=pillar_results,
            subdim_results=subdim_results,
            pc_results=pc_results,
            essential_dimensions=essential,
            redundant_dimensions=redundant,
            minimal_dimension_set=minimal_set,
            minimal_pfi=minimal_pfi
        )

        # Convert to JSON-serializable format
        results_dict = {
            "timestamp": summary.timestamp,
            "n_embeddings": summary.n_embeddings,
            "baseline_pfi": summary.baseline_pfi,
            "pillar_results": [asdict(r) for r in summary.pillar_results],
            "subdim_results": [asdict(r) for r in summary.subdim_results],
            "pc_results": [asdict(r) for r in summary.pc_results],
            "essential_dimensions": summary.essential_dimensions,
            "redundant_dimensions": summary.redundant_dimensions,
            "minimal_dimension_set": summary.minimal_dimension_set,
            "minimal_pfi": summary.minimal_pfi
        }

        results_file = self.results_dir / f"ablation_results_{timestamp}.json"
        with open(results_file, 'w', encoding='utf-8') as f:
            json.dump(results_dict, f, indent=2)
        print(f"\nResults saved to: {results_file}")

        # Print summary
        print("\n" + "=" * 70)
        print("ABLATION SUMMARY")
        print("=" * 70)

        print(f"\nBaseline PFI: {baseline_pfi:.4f}")
        print(f"\nDimensions tested: {len(all_results)}")
        print(f"  Essential (>10% drop): {len(essential)}")
        print(f"  Redundant (<2% drop): {len(redundant)}")
        print(f"  Moderate: {len(all_results) - len(essential) - len(redundant)}")

        if pillar_results:
            print("\nPILLAR IMPORTANCE (sorted by impact):")
            for r in sorted(pillar_results, key=lambda x: x.pfi_drop_pct, reverse=True):
                status = "ESSENTIAL" if r.is_essential else ("REDUNDANT" if r.is_redundant else "MODERATE")
                print(f"  {r.dimension_name}: {r.pfi_drop_pct:.1%} drop [{status}]")

        if essential:
            print(f"\nESSENTIAL DIMENSIONS (cannot remove):")
            for d in essential[:10]:
                print(f"  - {d}")

        if redundant:
            print(f"\nREDUNDANT DIMENSIONS (safe to remove):")
            for d in redundant[:10]:
                print(f"  - {d}")

        print(f"\nMINIMAL DIMENSION SET: {len(minimal_set)} dimensions")
        print(f"  Estimated PFI: {minimal_pfi:.4f} ({minimal_pfi/baseline_pfi:.1%} of baseline)")

        print("\n" + "=" * 70)
        print("NEXT STEPS:")
        print("=" * 70)
        print("1. Review essential dimensions — these define core identity")
        print("2. Consider removing redundant dimensions to simplify the model")
        print("3. Run Phase 3 (PC Mapping) to link PCs to named pillars")
        print("4. Use findings to refine the 5D drift metric")
        print("=" * 70)

        return summary


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="EXP2-SSTACK Phase 2.5: Ablation Testing"
    )
    parser.add_argument(
        '--mode', type=str, default='all',
        choices=['all', 'pillars', 'subdims', 'pcs'],
        help='Which ablations to run (default: all)'
    )
    parser.add_argument(
        '--max-responses', type=int, default=None,
        help='Max responses to embed (default: all)'
    )

    args = parser.parse_args()

    if not OPENAI_AVAILABLE:
        print("ERROR: OpenAI required. Install with: pip install openai")
        sys.exit(1)

    if not SKLEARN_AVAILABLE:
        print("ERROR: sklearn/scipy required. Install with: pip install scikit-learn scipy")
        sys.exit(1)

    engine = AblationEngine()
    summary = engine.run_full_ablation(mode=args.mode)

    if summary is None:
        print("\nAblation failed. Check data availability.")
        sys.exit(1)
