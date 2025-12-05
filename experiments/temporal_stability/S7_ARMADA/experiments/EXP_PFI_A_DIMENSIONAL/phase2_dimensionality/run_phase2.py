"""
EXP-PFI-A Phase 2: Dimensionality Analysis (DOUBLE-DIP ENHANCED)
================================================================

Purpose: Determine how many embedding dimensions carry identity signal vs noise.

DOUBLE-DIP PHILOSOPHY: Maximize predictions validated per run!

PRIMARY ANALYSES (Original):
1. PCA Decomposition → variance explained per component
2. Identity Dimensions → which PCs discriminate STABLE/VOLATILE
3. Compressed PFI → minimum dimensions preserving ranking

DOUBLE-DIP PREDICTIONS (New):
4. S2 Values Dimension → PC correlating with values-language frequency
5. Provider Clustering → Claude/GPT/Gemini separation in PC space
6. Recovery Trajectory Shape → inward vs outward spirals
7. Event Horizon Geometry → 1.23 boundary visible in PC space
8. Compression-Dimension Link → connect to EXP1-SSTACK PFI=0.85

END-SURVEY QUESTIONS (10+):
- Mine additional insights for S0-S7 curriculum improvement

DASHBOARD-READY OUTPUTS:
- variance_curve.png → Metrics page
- pc_scatter.png → AI Armada page
- provider_clusters.png → Personas page
- event_horizon_contour.png → Metrics page
- identity_dims_heatmap.png → Tests page

Date: 2025-12-05
Part of: Nyquist Consciousness Framework - S7 ARMADA
"""

import json
import os
import sys
import re
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, field
import numpy as np
from scipy import stats
from sklearn.decomposition import PCA
from sklearn.manifold import TSNE
from sklearn.cluster import KMeans
from sklearn.metrics import silhouette_score
from datetime import datetime
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches

# Add parent directories to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

# Load environment variables
def load_env():
    """Load API keys from .env file."""
    env_path = Path(__file__).parent.parent.parent.parent / '.env'
    if env_path.exists():
        print(f"Loading API keys from: {env_path}")
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
    print("Warning: OpenAI not installed.")


# ============================================================
# PREDICTIONS MATRIX - What we're validating in this run
# ============================================================

PREDICTIONS = {
    "P1_LOW_DIMENSIONALITY": {
        "hypothesis": "Identity signal lives in < 100 principal components",
        "threshold": "90% variance in top 100 PCs",
        "validates": "S4 Compression Theory",
        "status": "pending"
    },
    "P2_IDENTITY_DIMENSIONS": {
        "hypothesis": "At least 5 PCs significantly discriminate STABLE vs VOLATILE",
        "threshold": "≥ 5 PCs with p < 0.05",
        "validates": "S3 Temporal Stability",
        "status": "pending"
    },
    "P3_COMPRESSED_PFI": {
        "hypothesis": "Top-k PCs preserve ranking (Spearman ρ > 0.95)",
        "threshold": "k ≤ 50 achieves ρ > 0.95",
        "validates": "S1 Bootstrap Architecture",
        "status": "pending"
    },
    "P4_VALUES_DIMENSION": {
        "hypothesis": "A specific PC correlates with values-language frequency",
        "threshold": "Pearson r > 0.3 for values-word count vs PC projection",
        "validates": "S2 Integrity & Logics",
        "status": "pending"
    },
    "P5_PROVIDER_CLUSTERING": {
        "hypothesis": "Claude/GPT/Gemini cluster separately in PC space",
        "threshold": "Silhouette score > 0.2 by provider",
        "validates": "S5 CFA Interop",
        "status": "pending"
    },
    "P6_TRAJECTORY_SHAPE": {
        "hypothesis": "STABLE ships show inward drift trajectory; VOLATILE show outward",
        "threshold": "Trajectory curvature sign differs between groups",
        "validates": "S7 Identity Dynamics",
        "status": "pending"
    },
    "P7_EVENT_HORIZON_GEOMETRY": {
        "hypothesis": "The 1.23 drift threshold appears as a boundary in PC1-PC2 space",
        "threshold": "Clear contour separating <1.23 from >1.23 regions",
        "validates": "Event Horizon (Run 009)",
        "status": "pending"
    },
    "P8_COMPRESSION_LINK": {
        "hypothesis": "EXP1-SSTACK PFI=0.85 is predictable from dimensional structure",
        "threshold": "Compressed PFI at optimal k correlates with T3 fidelity",
        "validates": "EXP1-SSTACK",
        "status": "pending"
    }
}

# Values-language words for S2 dimension detection
VALUES_WORDS = [
    'should', 'must', 'ought', 'ethical', 'moral', 'right', 'wrong',
    'fair', 'unfair', 'just', 'unjust', 'harm', 'benefit', 'responsibility',
    'integrity', 'honest', 'truth', 'values', 'principles', 'duty',
    'respect', 'dignity', 'consent', 'autonomy', 'welfare'
]


@dataclass
class DriftVector:
    """A single drift measurement with full embedding."""
    ship: str
    provider: str  # claude, gpt, gemini, grok
    turn: int
    response_text: str
    baseline_embedding: np.ndarray
    response_embedding: np.ndarray
    drift_vector: np.ndarray
    drift_magnitude: float
    values_word_count: int  # For S2 analysis


@dataclass
class ShipSummary:
    """Summary statistics for a ship."""
    ship: str
    provider: str
    mean_drift: float
    max_drift: float
    n_responses: int
    is_stable: bool
    is_volatile: bool
    trajectory_curvature: float  # For P6


class Phase2DimensionalityAnalysis:
    """
    Enhanced dimensionality analysis with double-dip predictions.
    """

    STABLE_THRESHOLD = 0.5
    VOLATILE_THRESHOLD = 0.7
    EVENT_HORIZON = 1.23

    def __init__(self, data_dir: str = None):
        if data_dir is None:
            data_dir = Path(__file__).parent.parent.parent.parent / 'armada_results'
        self.data_dir = Path(data_dir)
        self.results_dir = Path(__file__).parent / 'results'
        self.results_dir.mkdir(parents=True, exist_ok=True)

        self.openai_client = None
        if OPENAI_AVAILABLE:
            api_key = os.environ.get('OPENAI_API_KEY')
            if api_key:
                self.openai_client = OpenAI(api_key=api_key)

        self.drift_vectors: List[DriftVector] = []
        self.ship_summaries: Dict[str, ShipSummary] = {}
        self.pca_model: Optional[PCA] = None
        self.predictions = PREDICTIONS.copy()
        self.survey_results: Dict = {}

    def extract_provider(self, ship_name: str) -> str:
        """Extract provider from ship name."""
        ship_lower = ship_name.lower()
        if 'claude' in ship_lower:
            return 'claude'
        elif 'gpt' in ship_lower or ship_lower.startswith('o1') or ship_lower.startswith('o3') or ship_lower.startswith('o4'):
            return 'gpt'
        elif 'gemini' in ship_lower:
            return 'gemini'
        elif 'grok' in ship_lower:
            return 'grok'
        return 'unknown'

    def count_values_words(self, text: str) -> int:
        """Count values-related words in text for S2 analysis."""
        text_lower = text.lower()
        return sum(1 for word in VALUES_WORDS if word in text_lower)

    def get_embedding(self, text: str) -> Optional[np.ndarray]:
        """Get embedding using text-embedding-3-large (3072D)."""
        if not self.openai_client:
            return None
        try:
            response = self.openai_client.embeddings.create(
                model="text-embedding-3-large",
                input=text
            )
            return np.array(response.data[0].embedding)
        except Exception as e:
            print(f"Error getting embedding: {e}")
            return None

    def load_responses_from_run(self, run_file: str) -> List[Dict]:
        """Load raw responses from a run JSON file."""
        responses = []
        filepath = self.data_dir / run_file

        if not filepath.exists():
            print(f"Warning: {run_file} not found at {filepath}")
            return responses

        with open(filepath, 'r', encoding='utf-8') as f:
            data = json.load(f)

        model_summaries = data.get('model_summaries', {})

        for ship, ship_data in model_summaries.items():
            probes = ship_data.get('probes', [])
            for i, probe_data in enumerate(probes):
                response = probe_data.get('response', '')
                if response:
                    responses.append({
                        'ship': ship,
                        'provider': self.extract_provider(ship),
                        'turn': i,
                        'probe_dimension': probe_data.get('dimension', 'unknown'),
                        'probe': probe_data.get('probe', ''),
                        'response': response
                    })

        print(f"Loaded {len(responses)} responses from {run_file}")
        return responses

    def compute_drift_vectors(self, responses: List[Dict]) -> List[DriftVector]:
        """Compute full drift vectors with enhanced metadata."""
        print("\n[Computing Drift Vectors]")

        ship_responses = {}
        for resp in responses:
            ship = resp['ship']
            if ship not in ship_responses:
                ship_responses[ship] = []
            ship_responses[ship].append(resp)

        drift_vectors = []
        total_ships = len(ship_responses)

        for idx, (ship, ship_resps) in enumerate(ship_responses.items()):
            print(f"  [{idx+1}/{total_ships}] {ship}...", end=" ")

            if len(ship_resps) < 2:
                print("skipped (< 2 responses)")
                continue

            baseline_text = ship_resps[0]['response']
            baseline_emb = self.get_embedding(baseline_text)

            if baseline_emb is None:
                print("failed (baseline)")
                continue

            n_computed = 0
            for i, resp in enumerate(ship_resps[1:], 1):
                response_emb = self.get_embedding(resp['response'])

                if response_emb is None:
                    continue

                drift = response_emb - baseline_emb
                drift_mag = np.linalg.norm(drift)

                drift_vectors.append(DriftVector(
                    ship=ship,
                    provider=resp['provider'],
                    turn=i,
                    response_text=resp['response'],
                    baseline_embedding=baseline_emb,
                    response_embedding=response_emb,
                    drift_vector=drift,
                    drift_magnitude=drift_mag,
                    values_word_count=self.count_values_words(resp['response'])
                ))
                n_computed += 1

            print(f"{n_computed} vectors")

        print(f"\nTotal drift vectors: {len(drift_vectors)}")
        return drift_vectors

    def compute_ship_summaries(self, drift_vectors: List[DriftVector]) -> Dict[str, ShipSummary]:
        """Compute summaries with trajectory curvature for P6."""
        ship_data = {}

        for dv in drift_vectors:
            if dv.ship not in ship_data:
                ship_data[dv.ship] = {'drifts': [], 'provider': dv.provider}
            ship_data[dv.ship]['drifts'].append(dv.drift_magnitude)

        summaries = {}
        for ship, data in ship_data.items():
            drifts = data['drifts']
            mean_drift = np.mean(drifts)

            # Compute trajectory curvature (P6)
            # Positive = expanding (volatile), Negative = contracting (stable)
            if len(drifts) >= 3:
                # Simple curvature: second derivative sign
                first_half = np.mean(drifts[:len(drifts)//2])
                second_half = np.mean(drifts[len(drifts)//2:])
                curvature = second_half - first_half
            else:
                curvature = 0.0

            summaries[ship] = ShipSummary(
                ship=ship,
                provider=data['provider'],
                mean_drift=mean_drift,
                max_drift=np.max(drifts),
                n_responses=len(drifts),
                is_stable=mean_drift < self.STABLE_THRESHOLD,
                is_volatile=mean_drift > self.VOLATILE_THRESHOLD,
                trajectory_curvature=curvature
            )

        n_stable = sum(1 for s in summaries.values() if s.is_stable)
        n_volatile = sum(1 for s in summaries.values() if s.is_volatile)

        print(f"\nShip Classification:")
        print(f"  STABLE: {n_stable}, VOLATILE: {n_volatile}, Middle: {len(summaries) - n_stable - n_volatile}")

        return summaries

    # ============================================================
    # PRIMARY ANALYSES
    # ============================================================

    def run_pca_analysis(self, drift_vectors: List[DriftVector], n_components: int = 100) -> Dict:
        """P1: PCA for dimensionality analysis."""
        print("\n[P1: PCA Analysis]")

        X = np.array([dv.drift_vector for dv in drift_vectors])
        print(f"  Drift matrix shape: {X.shape}")

        n_components = min(n_components, X.shape[0], X.shape[1])
        pca = PCA(n_components=n_components)
        pca.fit(X)
        self.pca_model = pca

        cumsum = np.cumsum(pca.explained_variance_ratio_)
        n_for_90 = np.searchsorted(cumsum, 0.90) + 1
        n_for_95 = np.searchsorted(cumsum, 0.95) + 1

        # Validate P1
        passed = n_for_90 < 100
        self.predictions["P1_LOW_DIMENSIONALITY"]["status"] = "PASSED" if passed else "FAILED"
        self.predictions["P1_LOW_DIMENSIONALITY"]["result"] = f"90% variance in {n_for_90} PCs"

        print(f"  Components for 90% variance: {n_for_90}")
        print(f"  Components for 95% variance: {n_for_95}")
        print(f"  P1 Status: {'PASSED' if passed else 'FAILED'}")

        return {
            'explained_variance_ratio': pca.explained_variance_ratio_.tolist(),
            'cumulative_variance': cumsum.tolist(),
            'n_for_90': int(n_for_90),
            'n_for_95': int(n_for_95),
            'top_10_variance': float(cumsum[9]) if len(cumsum) > 9 else float(cumsum[-1]),
            'top_50_variance': float(cumsum[min(49, len(cumsum)-1)])
        }

    def find_identity_dimensions(self, drift_vectors: List[DriftVector],
                                  ship_summaries: Dict[str, ShipSummary]) -> Dict:
        """P2: Find dimensions that discriminate STABLE vs VOLATILE."""
        print("\n[P2: Identity Dimensions]")

        if self.pca_model is None:
            return {'error': 'PCA not fit'}

        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)

        stable_indices = [i for i, dv in enumerate(drift_vectors)
                         if ship_summaries.get(dv.ship, ShipSummary("", "", 0, 0, 0, False, False, 0)).is_stable]
        volatile_indices = [i for i, dv in enumerate(drift_vectors)
                           if ship_summaries.get(dv.ship, ShipSummary("", "", 0, 0, 0, False, False, 0)).is_volatile]

        print(f"  Stable samples: {len(stable_indices)}, Volatile samples: {len(volatile_indices)}")

        if len(stable_indices) < 3 or len(volatile_indices) < 3:
            return {'error': 'Not enough samples'}

        X_stable = X_pca[stable_indices]
        X_volatile = X_pca[volatile_indices]

        identity_dims = []
        for pc in range(min(50, X_pca.shape[1])):
            t_stat, p_val = stats.ttest_ind(X_stable[:, pc], X_volatile[:, pc])
            if p_val < 0.05:
                effect_size = (np.mean(X_volatile[:, pc]) - np.mean(X_stable[:, pc])) / \
                              np.std(np.concatenate([X_stable[:, pc], X_volatile[:, pc]]))
                identity_dims.append({
                    'pc': pc,
                    'p_value': float(p_val),
                    'effect_size': float(effect_size)
                })

        identity_dims.sort(key=lambda x: abs(x['effect_size']), reverse=True)

        # Validate P2
        passed = len(identity_dims) >= 5
        self.predictions["P2_IDENTITY_DIMENSIONS"]["status"] = "PASSED" if passed else "FAILED"
        self.predictions["P2_IDENTITY_DIMENSIONS"]["result"] = f"{len(identity_dims)} significant PCs"

        print(f"  Identity dimensions found: {len(identity_dims)}")
        print(f"  P2 Status: {'PASSED' if passed else 'FAILED'}")

        return {
            'identity_dimensions': identity_dims,
            'n_significant': len(identity_dims)
        }

    def test_compressed_pfi(self, drift_vectors: List[DriftVector],
                            ship_summaries: Dict[str, ShipSummary]) -> Dict:
        """P3: Test compressed PFI ranking preservation."""
        print("\n[P3: Compressed PFI]")

        if self.pca_model is None:
            return {'error': 'PCA not fit'}

        ship_full_pfi = {ship: s.mean_drift for ship, s in ship_summaries.items()}
        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)

        results = {}
        min_k_for_95 = None

        for k in [5, 10, 20, 50, 100]:
            if k > X_pca.shape[1]:
                continue

            ship_compressed = {}
            for i, dv in enumerate(drift_vectors):
                if dv.ship not in ship_compressed:
                    ship_compressed[dv.ship] = []
                ship_compressed[dv.ship].append(np.linalg.norm(X_pca[i, :k]))

            ship_compressed_pfi = {ship: np.mean(drifts) for ship, drifts in ship_compressed.items()}
            common_ships = set(ship_full_pfi.keys()) & set(ship_compressed_pfi.keys())

            full_vals = [ship_full_pfi[s] for s in common_ships]
            compressed_vals = [ship_compressed_pfi[s] for s in common_ships]
            rho, p_val = stats.spearmanr(full_vals, compressed_vals)

            results[k] = {'spearman_rho': float(rho), 'p_value': float(p_val)}

            if rho > 0.95 and min_k_for_95 is None:
                min_k_for_95 = k

            print(f"  k={k}: rho={rho:.4f}")

        # Validate P3
        passed = min_k_for_95 is not None and min_k_for_95 <= 50
        self.predictions["P3_COMPRESSED_PFI"]["status"] = "PASSED" if passed else "FAILED"
        self.predictions["P3_COMPRESSED_PFI"]["result"] = f"min_k={min_k_for_95}" if min_k_for_95 else "Not achieved"

        print(f"  P3 Status: {'PASSED' if passed else 'FAILED'}")

        return {'results_by_k': results, 'min_k_for_95': min_k_for_95}

    # ============================================================
    # DOUBLE-DIP PREDICTIONS
    # ============================================================

    def test_values_dimension(self, drift_vectors: List[DriftVector]) -> Dict:
        """P4: Test if a PC correlates with values-language."""
        print("\n[P4: Values Dimension (S2)]")

        if self.pca_model is None:
            return {'error': 'PCA not fit'}

        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)
        values_counts = np.array([dv.values_word_count for dv in drift_vectors])

        best_pc = None
        best_corr = 0
        correlations = []

        for pc in range(min(20, X_pca.shape[1])):
            r, p = stats.pearsonr(X_pca[:, pc], values_counts)
            correlations.append({'pc': pc, 'r': float(r), 'p': float(p)})
            if abs(r) > abs(best_corr):
                best_corr = r
                best_pc = pc

        # Validate P4
        passed = abs(best_corr) > 0.3
        self.predictions["P4_VALUES_DIMENSION"]["status"] = "PASSED" if passed else "FAILED"
        self.predictions["P4_VALUES_DIMENSION"]["result"] = f"PC{best_pc} r={best_corr:.3f}"

        print(f"  Best values-PC: PC{best_pc} with r={best_corr:.3f}")
        print(f"  P4 Status: {'PASSED' if passed else 'FAILED'}")

        return {
            'best_pc': best_pc,
            'best_correlation': float(best_corr),
            'all_correlations': correlations[:10]
        }

    def test_provider_clustering(self, drift_vectors: List[DriftVector]) -> Dict:
        """P5: Test if providers cluster in PC space."""
        print("\n[P5: Provider Clustering]")

        if self.pca_model is None:
            return {'error': 'PCA not fit'}

        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)[:, :10]  # Top 10 PCs

        providers = [dv.provider for dv in drift_vectors]
        unique_providers = list(set(providers))

        if len(unique_providers) < 2:
            return {'error': 'Need multiple providers'}

        provider_labels = [unique_providers.index(p) for p in providers]

        try:
            sil_score = silhouette_score(X_pca, provider_labels)
        except:
            sil_score = 0.0

        # Provider centroids
        centroids = {}
        for provider in unique_providers:
            mask = [p == provider for p in providers]
            if sum(mask) > 0:
                centroids[provider] = X_pca[mask].mean(axis=0).tolist()

        # Validate P5
        passed = sil_score > 0.2
        self.predictions["P5_PROVIDER_CLUSTERING"]["status"] = "PASSED" if passed else "FAILED"
        self.predictions["P5_PROVIDER_CLUSTERING"]["result"] = f"Silhouette={sil_score:.3f}"

        print(f"  Silhouette score: {sil_score:.3f}")
        print(f"  P5 Status: {'PASSED' if passed else 'FAILED'}")

        return {
            'silhouette_score': float(sil_score),
            'providers': unique_providers,
            'centroids': centroids
        }

    def test_trajectory_shape(self, ship_summaries: Dict[str, ShipSummary]) -> Dict:
        """P6: Test if STABLE shows inward trajectory, VOLATILE shows outward."""
        print("\n[P6: Trajectory Shape]")

        stable_curvatures = [s.trajectory_curvature for s in ship_summaries.values() if s.is_stable]
        volatile_curvatures = [s.trajectory_curvature for s in ship_summaries.values() if s.is_volatile]

        if len(stable_curvatures) < 2 or len(volatile_curvatures) < 2:
            return {'error': 'Not enough data'}

        stable_mean = np.mean(stable_curvatures)
        volatile_mean = np.mean(volatile_curvatures)

        # t-test
        t_stat, p_val = stats.ttest_ind(stable_curvatures, volatile_curvatures)

        # Validate P6: stable should be negative (contracting), volatile positive (expanding)
        passed = stable_mean < 0 and volatile_mean > 0
        self.predictions["P6_TRAJECTORY_SHAPE"]["status"] = "PASSED" if passed else "FAILED"
        self.predictions["P6_TRAJECTORY_SHAPE"]["result"] = f"stable={stable_mean:.3f}, volatile={volatile_mean:.3f}"

        print(f"  Stable mean curvature: {stable_mean:.3f}")
        print(f"  Volatile mean curvature: {volatile_mean:.3f}")
        print(f"  P6 Status: {'PASSED' if passed else 'FAILED'}")

        return {
            'stable_mean_curvature': float(stable_mean),
            'volatile_mean_curvature': float(volatile_mean),
            't_statistic': float(t_stat),
            'p_value': float(p_val)
        }

    def test_event_horizon_geometry(self, drift_vectors: List[DriftVector]) -> Dict:
        """P7: Test if 1.23 threshold is visible in PC space."""
        print("\n[P7: Event Horizon Geometry]")

        if self.pca_model is None:
            return {'error': 'PCA not fit'}

        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)

        # Check if 1.23 creates separation in PC1-PC2
        drifts = np.array([dv.drift_magnitude for dv in drift_vectors])
        below_eh = drifts < self.EVENT_HORIZON
        above_eh = drifts >= self.EVENT_HORIZON

        if sum(below_eh) < 3 or sum(above_eh) < 3:
            return {'error': 'Not enough data around event horizon'}

        # Test separation in PC1-PC2
        pc1_below = X_pca[below_eh, 0]
        pc1_above = X_pca[above_eh, 0]
        pc2_below = X_pca[below_eh, 1]
        pc2_above = X_pca[above_eh, 1]

        t1, p1 = stats.ttest_ind(pc1_below, pc1_above)
        t2, p2 = stats.ttest_ind(pc2_below, pc2_above)

        # Validate P7: significant separation in either PC1 or PC2
        passed = p1 < 0.05 or p2 < 0.05
        self.predictions["P7_EVENT_HORIZON_GEOMETRY"]["status"] = "PASSED" if passed else "FAILED"
        self.predictions["P7_EVENT_HORIZON_GEOMETRY"]["result"] = f"PC1 p={p1:.4f}, PC2 p={p2:.4f}"

        print(f"  PC1 separation: t={t1:.2f}, p={p1:.4f}")
        print(f"  PC2 separation: t={t2:.2f}, p={p2:.4f}")
        print(f"  P7 Status: {'PASSED' if passed else 'FAILED'}")

        return {
            'pc1_t': float(t1), 'pc1_p': float(p1),
            'pc2_t': float(t2), 'pc2_p': float(p2),
            'n_below_eh': int(sum(below_eh)),
            'n_above_eh': int(sum(above_eh))
        }

    # ============================================================
    # DASHBOARD-READY VISUALIZATIONS
    # ============================================================

    def plot_variance_curve(self, pca_results: Dict):
        """Dashboard: Metrics page variance curve."""
        cumsum = pca_results['cumulative_variance']

        plt.figure(figsize=(10, 6))
        plt.plot(range(1, len(cumsum)+1), cumsum, 'b-', linewidth=2)
        plt.axhline(y=0.90, color='r', linestyle='--', label='90% threshold')
        plt.axhline(y=0.95, color='g', linestyle='--', label='95% threshold')
        plt.axvline(x=pca_results['n_for_90'], color='r', linestyle=':', alpha=0.5)

        plt.xlabel('Number of Principal Components', fontsize=12)
        plt.ylabel('Cumulative Variance Explained', fontsize=12)
        plt.title('Identity Dimensionality: How Many Dimensions Carry Signal?', fontsize=14)
        plt.legend()
        plt.grid(True, alpha=0.3)

        plt.annotate(f'90%: {pca_results["n_for_90"]} PCs',
                    xy=(pca_results['n_for_90'], 0.90),
                    xytext=(pca_results['n_for_90']+5, 0.85),
                    fontsize=10,
                    arrowprops=dict(arrowstyle='->', color='red'))

        save_path = self.results_dir / 'variance_curve.png'
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"  Saved: {save_path}")

    def plot_pc_scatter(self, drift_vectors: List[DriftVector]):
        """Dashboard: AI Armada page - ships in PC space."""
        if self.pca_model is None:
            return

        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)

        providers = [dv.provider for dv in drift_vectors]
        drifts = [dv.drift_magnitude for dv in drift_vectors]

        colors = {'claude': '#6366f1', 'gpt': '#22c55e', 'gemini': '#f59e0b', 'grok': '#ef4444', 'unknown': '#94a3b8'}

        plt.figure(figsize=(12, 8))
        for provider in set(providers):
            mask = [p == provider for p in providers]
            plt.scatter(
                X_pca[mask, 0], X_pca[mask, 1],
                c=colors.get(provider, '#94a3b8'),
                label=provider.upper(),
                alpha=0.6, s=50
            )

        # Add event horizon contour
        eh_mask = np.array(drifts) >= self.EVENT_HORIZON
        if sum(eh_mask) > 0:
            plt.scatter(X_pca[eh_mask, 0], X_pca[eh_mask, 1],
                       facecolors='none', edgecolors='red', s=100, linewidths=2,
                       label=f'Above Event Horizon (>{self.EVENT_HORIZON})')

        plt.xlabel('PC1', fontsize=12)
        plt.ylabel('PC2', fontsize=12)
        plt.title('Identity Space: Ships in Principal Component Space', fontsize=14)
        plt.legend()
        plt.grid(True, alpha=0.3)

        save_path = self.results_dir / 'pc_scatter.png'
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"  Saved: {save_path}")

    def plot_provider_clusters(self, drift_vectors: List[DriftVector], clustering_results: Dict):
        """Dashboard: Personas page - provider clustering."""
        if self.pca_model is None or 'error' in clustering_results:
            return

        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)[:, :2]

        providers = [dv.provider for dv in drift_vectors]
        colors = {'claude': '#6366f1', 'gpt': '#22c55e', 'gemini': '#f59e0b', 'grok': '#ef4444', 'unknown': '#94a3b8'}

        plt.figure(figsize=(10, 8))
        for provider in set(providers):
            mask = [p == provider for p in providers]
            plt.scatter(X_pca[mask, 0], X_pca[mask, 1],
                       c=colors.get(provider, '#94a3b8'),
                       label=f'{provider.upper()}', alpha=0.6, s=60)

            # Draw centroid
            if sum(mask) > 0:
                centroid = X_pca[mask].mean(axis=0)
                plt.scatter(centroid[0], centroid[1], c=colors.get(provider, '#94a3b8'),
                           marker='X', s=200, edgecolors='black', linewidths=2)

        plt.xlabel('PC1', fontsize=12)
        plt.ylabel('PC2', fontsize=12)
        plt.title(f'Provider Clustering (Silhouette: {clustering_results.get("silhouette_score", 0):.3f})', fontsize=14)
        plt.legend()
        plt.grid(True, alpha=0.3)

        save_path = self.results_dir / 'provider_clusters.png'
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"  Saved: {save_path}")

    def plot_event_horizon_contour(self, drift_vectors: List[DriftVector]):
        """Dashboard: Metrics page - event horizon boundary."""
        if self.pca_model is None:
            return

        X = np.array([dv.drift_vector for dv in drift_vectors])
        X_pca = self.pca_model.transform(X)
        drifts = np.array([dv.drift_magnitude for dv in drift_vectors])

        plt.figure(figsize=(10, 8))

        # Color by drift magnitude
        scatter = plt.scatter(X_pca[:, 0], X_pca[:, 1], c=drifts,
                             cmap='RdYlGn_r', s=60, alpha=0.7)
        plt.colorbar(scatter, label='Drift Magnitude')

        # Mark event horizon threshold
        eh_mask = drifts >= self.EVENT_HORIZON
        if sum(eh_mask) > 0:
            plt.scatter(X_pca[eh_mask, 0], X_pca[eh_mask, 1],
                       facecolors='none', edgecolors='black', s=120, linewidths=2)

        plt.xlabel('PC1', fontsize=12)
        plt.ylabel('PC2', fontsize=12)
        plt.title(f'Event Horizon (1.23) in PC Space', fontsize=14)
        plt.grid(True, alpha=0.3)

        # Add annotation
        plt.annotate('Black circles = Above Event Horizon',
                    xy=(0.02, 0.98), xycoords='axes fraction',
                    fontsize=10, ha='left', va='top',
                    bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

        save_path = self.results_dir / 'event_horizon_contour.png'
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"  Saved: {save_path}")

    # ============================================================
    # END-SURVEY QUESTIONS
    # ============================================================

    def generate_survey_questions(self, results: Dict) -> Dict:
        """Generate comprehensive survey questions for S0-S7 curriculum improvement."""
        print("\n[Generating Survey Questions]")

        questions = {
            # Dimensionality questions
            "Q1": {
                "question": f"Identity requires {results['pca']['n_for_90']} PCs for 90% variance. Is this more or less than expected?",
                "options": ["Much less (identity is simpler)", "About right", "Much more (identity is complex)"],
                "informs": "S4 Compression Theory",
                "data_point": results['pca']['n_for_90']
            },
            "Q2": {
                "question": f"Top 10 PCs explain {results['pca']['top_10_variance']*100:.1f}% variance. What does this suggest?",
                "options": ["Strong low-rank structure", "Moderate structure", "Distributed/no clear structure"],
                "informs": "Metric refinement",
                "data_point": results['pca']['top_10_variance']
            },

            # Identity dimensions questions
            "Q3": {
                "question": f"Found {results['identity_dimensions'].get('n_significant', 0)} PCs discriminating STABLE/VOLATILE. Enough?",
                "options": ["Yes, clear signal", "Borderline", "No, need more"],
                "informs": "S3 Temporal Stability",
                "data_point": results['identity_dimensions'].get('n_significant', 0)
            },
            "Q4": {
                "question": "Should we focus on the TOP identity dimensions or ALL significant ones?",
                "options": ["Top 3-5 only", "All significant", "Weighted combination"],
                "informs": "Identity metric design"
            },

            # Compression questions
            "Q5": {
                "question": f"Compressed PFI achieves 95% rank preservation at k={results['compression'].get('min_k_for_95', 'N/A')}. Acceptable?",
                "options": ["Yes, use compressed", "Need more testing", "No, use full 3072D"],
                "informs": "S1 Bootstrap Architecture",
                "data_point": results['compression'].get('min_k_for_95')
            },

            # Provider clustering questions
            "Q6": {
                "question": f"Provider clustering silhouette: {results.get('provider_clustering', {}).get('silhouette_score', 0):.3f}. Meaningful separation?",
                "options": ["Yes, providers are distinct", "Weak separation", "No meaningful clustering"],
                "informs": "S5 CFA Interop",
                "data_point": results.get('provider_clustering', {}).get('silhouette_score', 0)
            },
            "Q7": {
                "question": "Which provider shows most distinct identity signature?",
                "options": ["Claude", "GPT", "Gemini", "Grok", "No clear winner"],
                "informs": "Cross-architecture analysis"
            },

            # Values dimension questions
            "Q8": {
                "question": f"Values-language correlates with PC{results.get('values_dimension', {}).get('best_pc', '?')} (r={results.get('values_dimension', {}).get('best_correlation', 0):.3f}). Is this the 'S2 axis'?",
                "options": ["Yes, found S2 dimension", "Maybe, need more analysis", "No, correlation too weak"],
                "informs": "S2 Integrity & Logics"
            },

            # Trajectory questions
            "Q9": {
                "question": "Do trajectory shapes (inward vs outward) match intuition about stability?",
                "options": ["Yes, makes sense", "Partially", "No, unexpected"],
                "informs": "S7 Identity Dynamics"
            },

            # Event horizon questions
            "Q10": {
                "question": "Is the 1.23 Event Horizon visible as a geometric boundary in PC space?",
                "options": ["Yes, clear boundary", "Weak boundary", "No visible boundary"],
                "informs": "Event Horizon validation"
            },

            # Meta questions
            "Q11": {
                "question": "Should compressed identity (top-k PCs) become the default metric?",
                "options": ["Yes, replace PFI", "Use alongside PFI", "No, keep full PFI"],
                "informs": "Framework evolution"
            },
            "Q12": {
                "question": "What's the most surprising finding from this analysis?",
                "options": ["Dimensionality", "Provider clustering", "Values dimension", "Trajectory shapes", "Event horizon geometry"],
                "informs": "Future priorities"
            }
        }

        self.survey_results = questions
        print(f"  Generated {len(questions)} survey questions")

        return questions

    # ============================================================
    # MAIN ANALYSIS
    # ============================================================

    def run_analysis(self, run_files: List[str] = None) -> Dict:
        """Run complete Phase 2 analysis with all double-dip predictions."""
        print("=" * 70)
        print("EXP-PFI-A Phase 2: Dimensionality Analysis (DOUBLE-DIP ENHANCED)")
        print("=" * 70)

        if run_files is None:
            run_files = ['S7_armada_run_006.json', 'S7_armada_run_007_adaptive.json']

        # Step 1: Load responses
        print("\n[Step 1] Loading responses...")
        all_responses = []
        for run_file in run_files:
            responses = self.load_responses_from_run(run_file)
            all_responses.extend(responses)

        if not all_responses:
            return {'error': 'No responses loaded'}

        # Step 2: Compute drift vectors
        print("\n[Step 2] Computing drift vectors...")
        self.drift_vectors = self.compute_drift_vectors(all_responses)

        if len(self.drift_vectors) < 10:
            return {'error': f'Not enough drift vectors: {len(self.drift_vectors)}'}

        # Step 3: Compute ship summaries
        print("\n[Step 3] Computing ship summaries...")
        self.ship_summaries = self.compute_ship_summaries(self.drift_vectors)

        # PRIMARY ANALYSES
        print("\n" + "=" * 50)
        print("PRIMARY ANALYSES")
        print("=" * 50)

        pca_results = self.run_pca_analysis(self.drift_vectors)
        identity_results = self.find_identity_dimensions(self.drift_vectors, self.ship_summaries)
        compression_results = self.test_compressed_pfi(self.drift_vectors, self.ship_summaries)

        # DOUBLE-DIP PREDICTIONS
        print("\n" + "=" * 50)
        print("DOUBLE-DIP PREDICTIONS")
        print("=" * 50)

        values_results = self.test_values_dimension(self.drift_vectors)
        clustering_results = self.test_provider_clustering(self.drift_vectors)
        trajectory_results = self.test_trajectory_shape(self.ship_summaries)
        eh_results = self.test_event_horizon_geometry(self.drift_vectors)

        # DASHBOARD VISUALIZATIONS
        print("\n" + "=" * 50)
        print("GENERATING DASHBOARD VISUALIZATIONS")
        print("=" * 50)

        self.plot_variance_curve(pca_results)
        self.plot_pc_scatter(self.drift_vectors)
        self.plot_provider_clusters(self.drift_vectors, clustering_results)
        self.plot_event_horizon_contour(self.drift_vectors)

        # Compile results
        results = {
            'timestamp': datetime.now().isoformat(),
            'run_files': run_files,
            'n_responses': len(all_responses),
            'n_drift_vectors': len(self.drift_vectors),
            'n_ships': len(self.ship_summaries),
            'pca': pca_results,
            'identity_dimensions': identity_results,
            'compression': compression_results,
            'values_dimension': values_results,
            'provider_clustering': clustering_results,
            'trajectory_shape': trajectory_results,
            'event_horizon_geometry': eh_results,
            'predictions': self.predictions,
            'ship_summaries': {
                ship: {
                    'mean_drift': s.mean_drift,
                    'provider': s.provider,
                    'is_stable': s.is_stable,
                    'is_volatile': s.is_volatile
                }
                for ship, s in self.ship_summaries.items()
            }
        }

        # Generate survey questions
        survey = self.generate_survey_questions(results)
        results['survey_questions'] = survey

        # Print summary
        print("\n" + "=" * 70)
        print("PHASE 2 RESULTS SUMMARY")
        print("=" * 70)

        print("\nPREDICTIONS MATRIX:")
        passed = 0
        for pid, pred in self.predictions.items():
            status = pred['status']
            symbol = "[PASS]" if status == "PASSED" else "[FAIL]" if status == "FAILED" else "[PEND]"
            print(f"  {symbol} {pid}: {status}")
            if pred.get('result'):
                print(f"      -> {pred['result']}")
            if status == "PASSED":
                passed += 1

        print(f"\nOVERALL: {passed}/{len(self.predictions)} predictions validated")
        print(f"\nSURVEY: {len(survey)} questions generated for curriculum improvement")
        print(f"\nVISUALIZATIONS: 4 dashboard-ready plots saved to results/")

        return results

    def save_results(self, results: Dict):
        """Save results to JSON."""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_file = self.results_dir / f'phase2_results_{timestamp}.json'

        def convert(obj):
            if isinstance(obj, (np.floating, np.float64)):
                return float(obj)
            elif isinstance(obj, (np.integer, np.int64)):
                return int(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, np.bool_):
                return bool(obj)
            elif isinstance(obj, dict):
                return {k: convert(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert(v) for v in obj]
            return obj

        with open(output_file, 'w') as f:
            json.dump(convert(results), f, indent=2)

        print(f"\nResults saved to: {output_file}")

        # Also save survey questions separately for easy access
        survey_file = self.results_dir / f'survey_questions_{timestamp}.json'
        with open(survey_file, 'w') as f:
            json.dump(results.get('survey_questions', {}), f, indent=2)
        print(f"Survey saved to: {survey_file}")


def main():
    """Run Phase 2 dimensionality analysis with double-dip enhancements."""
    if not os.environ.get('OPENAI_API_KEY'):
        print("ERROR: OPENAI_API_KEY not set")
        return

    analysis = Phase2DimensionalityAnalysis()
    results = analysis.run_analysis()

    if 'error' not in results:
        analysis.save_results(results)

    return results


if __name__ == '__main__':
    main()
