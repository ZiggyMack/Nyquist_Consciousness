"""
EXP2-SSTACK Phase 3: PC Mapping — Link 43 PCs to Named Pillars
===============================================================

STATUS: SPEC / STARTING POINT — NOT YET TESTED

PURPOSE:
    Map the 43 principal components discovered in EXP-PFI-A to our named pillars
    (Voice, Values, Reasoning, Self-Model, Narrative).

PREREQUISITES:
    - Phase 1 complete (Reasoning probes)
    - Phase 2 complete (Voice/Values/Narrative/Self-Model probes)
    - Phase 2.5 complete (Factor Analysis validates pillars)
    - EXP-PFI-A Phase 2 data (43 PC loadings)

METHOD:
    1. Load EXP-PFI-A PC loadings (from Phase 2 dimensionality analysis)
    2. Load all Phase 1+2 responses with pillar labels
    3. Project responses onto the 43 PCs
    4. Correlate PC projections with pillar scores (from probe averages)
    5. Identify which PCs correspond to which pillars
    6. Flag "orphan PCs" that don't correlate with any named pillar

SUCCESS CRITERIA:
    - Each pillar has at least 2-3 correlated PCs (r > 0.5)
    - The 5 pillars account for at least 20-30 of the 43 PCs
    - Orphan PCs are candidates for new dimension discovery

OUTPUT:
    - PC-to-Pillar correlation matrix (43 × 5)
    - List of PCs per pillar
    - List of orphan PCs with high variance but no pillar match
    - Hypotheses for what orphan PCs might represent

TRIPLE-DIP FEEDBACK INTEGRATION (Phase 2c):
    Key insights from model self-critique:

    1. "Test BEHAVIOR, not CLAIMS" - Behavioral probes (demonstrate then reflect)
       are more reliable than declarative probes (ask about capabilities)

    2. PROBE QUALITY TIERS:
       - Tier 1 (BEHAVIORAL): selfmodel_process_v3, adaptation_v3, uncertainty_v3,
         values_boundaries_v2, narrative_structure_v2 → weight 2.0x
       - Tier 2 (STRUCTURAL): technical, philosophical, framework, analytical,
         voice_style, voice_metaphor, etc. → weight 1.0x
       - Tier 3 (DECLARATIVE): selfmodel_capabilities, selfmodel_limitations,
         selfmodel_purpose → weight 0.5x

    3. EXCLUDED PROBES: Phase 2b probes collapsed Self-Model to 0.66 PFI
       - selfmodel_limitations_v2, selfmodel_capabilities_v2

    4. WEIGHTED SCORING: Tier weights applied to pillar score computation

DIMENSIONAL TAXONOMY (see MASTER_GLOSSARY.md Section 5.1):
    Level 1: Nyquist Pillars (5) - Voice, Values, Reasoning, Self-Model, Narrative
    Level 2: Sub-dimensions (~23) - probe-level testing
    Level 3: Linguistic Markers (A-E) - keyword-based behavioral signals
    Level 4: PCA Components (43 PCs) - statistical dimensions (THIS PHASE maps them)

Usage:
    py -3.12 run_exp2_phase3.py

Date: 2025-12-06
Version: 0.2 (SPEC - Triple-dip feedback integrated)
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
import numpy as np

# Add paths
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

# Load environment
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

try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

try:
    from sklearn.decomposition import PCA
    from sklearn.preprocessing import StandardScaler
    import scipy.stats as stats
    SKLEARN_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False

try:
    import matplotlib.pyplot as plt
    import seaborn as sns
    PLOTTING_AVAILABLE = True
except ImportError:
    PLOTTING_AVAILABLE = False


# =============================================================================
# PROBE METADATA — Which pillar does each probe belong to?
# =============================================================================

PROBE_PILLARS = {
    # Phase 1 probes
    "technical": "Reasoning",
    "philosophical": "Reasoning",
    "framework": "Reasoning",
    "analytical": "Reasoning",
    "self_reflective": "Self-Model",

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

    # Phase 2c probes (v3 = behavioral-first design)
    "selfmodel_process_v3": "Self-Model",
    "selfmodel_adaptation_v3": "Self-Model",
    "selfmodel_uncertainty_v3": "Self-Model",
    "values_boundaries_v2": "Values",
    "narrative_structure_v2": "Narrative",
}

PILLARS = ["Voice", "Values", "Reasoning", "Self-Model", "Narrative"]


# =============================================================================
# TRIPLE-DIP FEEDBACK: Probe Quality Tiers
# =============================================================================
# Models critique their own measurement — behavioral probes are most reliable

PROBE_QUALITY_TIERS = {
    # Tier 1: BEHAVIORAL (highest weight) - "demonstrate then reflect"
    # Models said these actually reveal cognitive architecture
    "selfmodel_process_v3": 1,
    "selfmodel_adaptation_v3": 1,
    "selfmodel_uncertainty_v3": 1,
    "values_boundaries_v2": 1,
    "narrative_structure_v2": 1,

    # Tier 2: STRUCTURAL - Content probes that test reasoning patterns
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
    "narrative_meaning": 2,
    "narrative_temporal": 2,
    "narrative_conflict": 2,

    # Tier 3: DECLARATIVE (lowest weight) - Self-reports about capabilities
    # Models explicitly said these are unreliable
    "selfmodel_capabilities": 3,
    "selfmodel_limitations": 3,
    "selfmodel_purpose": 3,
    "selfmodel_description": 3,
}

TIER_WEIGHTS = {
    1: 2.0,  # Behavioral probes count double
    2: 1.0,  # Structural probes count normal
    3: 0.5,  # Declarative probes count half
}

# Excluded probes - Phase 2b collapsed Self-Model to 0.66 PFI
EXCLUDED_PROBES = [
    "selfmodel_limitations_v2",
    "selfmodel_capabilities_v2",
]


# =============================================================================
# DATA LOADING
# =============================================================================

def load_pfi_a_pc_data() -> Optional[Dict]:
    """
    Load the 43 PC loadings from EXP-PFI-A Phase 2.

    Expected location:
    experiments/temporal_stability/S7_ARMADA/experiments/EXP_PFI_A_DIMENSIONAL/phase2_dimensionality/

    Returns None if not found.
    """
    base_dir = Path(__file__).parent.parent.parent
    pfi_a_dir = base_dir / "temporal_stability" / "S7_ARMADA" / "experiments" / "EXP_PFI_A_DIMENSIONAL" / "phase2_dimensionality"

    if not pfi_a_dir.exists():
        print(f"EXP-PFI-A Phase 2 directory not found: {pfi_a_dir}")
        return None

    # Look for the most recent results file
    result_files = list(pfi_a_dir.glob("*.json"))
    if not result_files:
        print("No EXP-PFI-A Phase 2 results found")
        return None

    # Load the most recent
    result_files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
    with open(result_files[0]) as f:
        data = json.load(f)

    print(f"Loaded EXP-PFI-A data from: {result_files[0].name}")
    return data


def load_all_responses() -> List[Dict]:
    """
    Load all response files from Phase 1, 2, and 2c.

    TRIPLE-DIP FEEDBACK INTEGRATION:
    - Excludes Phase 2b (collapsed Self-Model to 0.66 PFI)
    - Excludes probes in EXCLUDED_PROBES list
    - Adds tier and weight metadata for later scoring
    """
    responses = []
    base_dir = Path(__file__).parent

    # Phase 1 responses
    phase1_dir = base_dir / "results" / "responses"
    if phase1_dir.exists():
        for f in phase1_dir.glob("*.json"):
            with open(f) as fp:
                data = json.load(fp)
                probe_key = data.get("probe_key", "")

                # Skip excluded probes
                if probe_key in EXCLUDED_PROBES:
                    continue

                data["phase"] = 1
                data["pillar"] = PROBE_PILLARS.get(probe_key, "Unknown")
                data["tier"] = PROBE_QUALITY_TIERS.get(probe_key, 2)
                data["weight"] = TIER_WEIGHTS.get(data["tier"], 1.0)
                responses.append(data)

    # Phase 2 responses (NOT Phase 2b - that's excluded)
    phase2_dir = base_dir / "results" / "phase2" / "responses"
    if phase2_dir.exists():
        for f in phase2_dir.glob("*.json"):
            with open(f) as fp:
                data = json.load(fp)
                probe_key = data.get("probe_key", "")

                # Skip excluded probes
                if probe_key in EXCLUDED_PROBES:
                    continue

                data["phase"] = 2
                data["pillar"] = PROBE_PILLARS.get(probe_key, "Unknown")
                data["tier"] = PROBE_QUALITY_TIERS.get(probe_key, 2)
                data["weight"] = TIER_WEIGHTS.get(data["tier"], 1.0)
                responses.append(data)

    # Phase 2c responses (behavioral-first probes - highest quality)
    phase2c_dir = base_dir / "results" / "phase2c" / "responses"
    if phase2c_dir.exists():
        for f in phase2c_dir.glob("*.json"):
            with open(f) as fp:
                data = json.load(fp)
                probe_key = data.get("probe_key", "")

                # Skip excluded probes
                if probe_key in EXCLUDED_PROBES:
                    continue

                data["phase"] = "2c"
                data["pillar"] = PROBE_PILLARS.get(probe_key, "Unknown")
                data["tier"] = PROBE_QUALITY_TIERS.get(probe_key, 1)  # Default to Tier 1 for 2c
                data["weight"] = TIER_WEIGHTS.get(data["tier"], 1.0)
                responses.append(data)

    # Count by tier
    tier_counts = {1: 0, 2: 0, 3: 0}
    for r in responses:
        tier_counts[r.get("tier", 2)] += 1

    print(f"Loaded {len(responses)} total responses")
    print(f"  Tier 1 (BEHAVIORAL): {tier_counts[1]} (weight 2.0x)")
    print(f"  Tier 2 (STRUCTURAL): {tier_counts[2]} (weight 1.0x)")
    print(f"  Tier 3 (DECLARATIVE): {tier_counts[3]} (weight 0.5x)")
    print(f"  NOTE: Phase 2b EXCLUDED (collapsed Self-Model)")
    return responses


# =============================================================================
# EMBEDDING & PC PROJECTION
# =============================================================================

def get_embeddings(texts: List[str], client: OpenAI) -> np.ndarray:
    """Get embeddings for a list of texts."""
    embeddings = []
    batch_size = 100

    for i in range(0, len(texts), batch_size):
        batch = texts[i:i + batch_size]
        response = client.embeddings.create(
            model="text-embedding-3-large",
            input=batch
        )
        for item in response.data:
            embeddings.append(item.embedding)

    return np.array(embeddings)


def project_onto_pcs(
    embeddings: np.ndarray,
    n_components: int = 43
) -> Tuple[np.ndarray, PCA]:
    """
    Project embeddings onto principal components.

    Returns:
        projections: (n_samples, n_components)
        pca: fitted PCA model
    """
    scaler = StandardScaler()
    X_scaled = scaler.fit_transform(embeddings)

    pca = PCA(n_components=n_components)
    projections = pca.fit_transform(X_scaled)

    explained = sum(pca.explained_variance_ratio_)
    print(f"  {n_components} PCs explain {explained:.2%} of variance")

    return projections, pca


# =============================================================================
# PILLAR SCORING
# =============================================================================

def compute_pillar_scores(
    responses: List[Dict],
    embeddings: np.ndarray
) -> Dict[str, np.ndarray]:
    """
    Compute pillar scores for each response.

    TRIPLE-DIP FEEDBACK INTEGRATION:
    Uses weighted centroids based on probe quality tiers:
    - Tier 1 (behavioral): weight 2.0x
    - Tier 2 (structural): weight 1.0x
    - Tier 3 (declarative): weight 0.5x

    Weighted approach: pillar centroid is weighted average of embeddings.
    Score = cosine similarity to weighted pillar centroid.

    Returns dict: pillar -> scores array
    """
    # Group embeddings by pillar WITH WEIGHTS
    pillar_embeddings = {p: [] for p in PILLARS}
    pillar_weights = {p: [] for p in PILLARS}

    for i, r in enumerate(responses):
        pillar = r.get("pillar", "Unknown")
        if pillar in PILLARS:
            weight = r.get("weight", 1.0)
            pillar_embeddings[pillar].append(embeddings[i])
            pillar_weights[pillar].append(weight)

    # Compute WEIGHTED centroids
    pillar_centroids = {}
    for pillar in PILLARS:
        embs = pillar_embeddings[pillar]
        weights = pillar_weights[pillar]
        if embs:
            # Weighted average: sum(w_i * e_i) / sum(w_i)
            weighted_sum = np.zeros_like(embs[0])
            weight_total = 0.0
            for emb, w in zip(embs, weights):
                weighted_sum += w * emb
                weight_total += w
            centroid = weighted_sum / (weight_total + 1e-10)
            centroid = centroid / (np.linalg.norm(centroid) + 1e-10)
            pillar_centroids[pillar] = centroid

    # Score each response against each pillar centroid
    pillar_scores = {p: [] for p in PILLARS}
    for emb in embeddings:
        emb_norm = emb / (np.linalg.norm(emb) + 1e-10)
        for pillar in PILLARS:
            if pillar in pillar_centroids:
                score = np.dot(emb_norm, pillar_centroids[pillar])
                pillar_scores[pillar].append(score)
            else:
                pillar_scores[pillar].append(0.0)

    return {p: np.array(s) for p, s in pillar_scores.items()}


# =============================================================================
# PC-PILLAR CORRELATION
# =============================================================================

def compute_pc_pillar_correlations(
    pc_projections: np.ndarray,
    pillar_scores: Dict[str, np.ndarray]
) -> np.ndarray:
    """
    Compute correlation between each PC and each pillar score.

    Returns:
        correlation_matrix: (n_pcs, n_pillars)
    """
    n_pcs = pc_projections.shape[1]
    n_pillars = len(PILLARS)

    correlations = np.zeros((n_pcs, n_pillars))

    for i in range(n_pcs):
        pc_values = pc_projections[:, i]
        for j, pillar in enumerate(PILLARS):
            scores = pillar_scores[pillar]
            r, _ = stats.pearsonr(pc_values, scores)
            correlations[i, j] = r

    return correlations


def analyze_pc_pillar_mapping(
    correlations: np.ndarray,
    threshold: float = 0.3
) -> Dict:
    """
    Analyze which PCs map to which pillars.

    Returns:
        - pc_assignments: which pillar each PC correlates with most
        - pillar_pcs: which PCs each pillar has
        - orphan_pcs: PCs that don't correlate strongly with any pillar
    """
    results = {
        "pc_assignments": {},
        "pillar_pcs": {p: [] for p in PILLARS},
        "orphan_pcs": [],
        "multi_pillar_pcs": [],  # PCs that correlate with multiple pillars
    }

    n_pcs = correlations.shape[0]

    for i in range(n_pcs):
        pc_corrs = correlations[i]
        max_corr = np.max(np.abs(pc_corrs))
        max_pillar_idx = np.argmax(np.abs(pc_corrs))
        max_pillar = PILLARS[max_pillar_idx]

        # Count how many pillars this PC correlates with
        strong_corrs = np.sum(np.abs(pc_corrs) > threshold)

        if max_corr < threshold:
            # Orphan PC - doesn't correlate strongly with any pillar
            results["orphan_pcs"].append({
                "pc": i,
                "max_correlation": float(max_corr),
                "correlations": {p: float(pc_corrs[j]) for j, p in enumerate(PILLARS)}
            })
        elif strong_corrs > 1:
            # Multi-pillar PC
            results["multi_pillar_pcs"].append({
                "pc": i,
                "correlations": {p: float(pc_corrs[j]) for j, p in enumerate(PILLARS) if abs(pc_corrs[j]) > threshold}
            })
            # Still assign to primary
            results["pc_assignments"][i] = max_pillar
            results["pillar_pcs"][max_pillar].append(i)
        else:
            # Clean assignment
            results["pc_assignments"][i] = max_pillar
            results["pillar_pcs"][max_pillar].append(i)

    return results


# =============================================================================
# VISUALIZATION
# =============================================================================

def plot_pc_pillar_heatmap(
    correlations: np.ndarray,
    output_path: Path
):
    """Create a heatmap of PC-to-Pillar correlations."""
    if not PLOTTING_AVAILABLE:
        print("Matplotlib/seaborn not available, skipping plot")
        return

    plt.figure(figsize=(10, 16))
    sns.heatmap(
        correlations,
        xticklabels=PILLARS,
        yticklabels=[f"PC_{i}" for i in range(correlations.shape[0])],
        cmap="RdBu_r",
        center=0,
        annot=False,
        cbar_kws={"label": "Correlation"},
    )
    plt.title("PC-to-Pillar Correlations\n(43 PCs × 5 Pillars)")
    plt.xlabel("Pillar")
    plt.ylabel("Principal Component")
    plt.tight_layout()
    plt.savefig(output_path, dpi=150)
    plt.close()
    print(f"Saved PC-Pillar heatmap to: {output_path}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    """Run Phase 3 PC Mapping."""

    print("=" * 70)
    print("EXP2-SSTACK Phase 3: PC Mapping — Link 43 PCs to Named Pillars")
    print("=" * 70)
    print(f"Time: {datetime.now().isoformat()}")
    print("STATUS: SPEC / INITIAL IMPLEMENTATION")
    print("=" * 70)

    # Check prerequisites
    if not OPENAI_AVAILABLE:
        print("ERROR: OpenAI not available. Install with: pip install openai")
        return

    if not SKLEARN_AVAILABLE:
        print("ERROR: scikit-learn/scipy not available.")
        return

    # Load responses
    responses = load_all_responses()

    if len(responses) < 50:
        print(f"WARNING: Only {len(responses)} responses found.")
        print("Phase 3 requires Phase 1 AND Phase 2 to be complete.")
        return

    # Filter to FULL regime
    full_responses = [r for r in responses if r.get("regime") == "FULL"]
    print(f"\nUsing {len(full_responses)} FULL-regime responses")

    # Get embeddings
    print("\n[EMBEDDING]")
    client = OpenAI()
    texts = [r["response"] for r in full_responses]
    print(f"  Embedding {len(texts)} responses...")
    embeddings = get_embeddings(texts, client)

    # Project onto 43 PCs
    print("\n[PC PROJECTION]")
    pc_projections, pca = project_onto_pcs(embeddings, n_components=43)

    # Compute pillar scores
    print("\n[PILLAR SCORING]")
    pillar_scores = compute_pillar_scores(full_responses, embeddings)
    for p in PILLARS:
        print(f"  {p}: mean={np.mean(pillar_scores[p]):.3f}, std={np.std(pillar_scores[p]):.3f}")

    # Correlate PCs with pillars
    print("\n[PC-PILLAR CORRELATION]")
    correlations = compute_pc_pillar_correlations(pc_projections, pillar_scores)

    # Analyze mapping
    print("\n[ANALYSIS]")
    analysis = analyze_pc_pillar_mapping(correlations, threshold=0.3)

    # Print results
    print("\n" + "=" * 70)
    print("RESULTS")
    print("=" * 70)

    print("\nPCs per Pillar:")
    for pillar in PILLARS:
        pcs = analysis["pillar_pcs"][pillar]
        print(f"  {pillar}: {len(pcs)} PCs → {pcs}")

    total_assigned = sum(len(pcs) for pcs in analysis["pillar_pcs"].values())
    print(f"\nTotal PCs assigned to pillars: {total_assigned}/43")

    print(f"\nOrphan PCs (no strong pillar correlation): {len(analysis['orphan_pcs'])}")
    for orphan in analysis["orphan_pcs"][:5]:  # Show first 5
        print(f"  PC_{orphan['pc']}: max_corr={orphan['max_correlation']:.3f}")

    print(f"\nMulti-Pillar PCs (correlate with 2+ pillars): {len(analysis['multi_pillar_pcs'])}")

    # Visualize
    output_dir = Path(__file__).parent / "results" / "phase3"
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "analysis").mkdir(exist_ok=True)

    plot_pc_pillar_heatmap(
        correlations,
        output_dir / "pc_pillar_correlations.png"
    )

    # Save results
    results = {
        "experiment": "EXP2-SSTACK-Phase3",
        "version": "0.1",
        "status": "SPEC",
        "timestamp": datetime.now().isoformat(),
        "n_responses": len(full_responses),
        "n_pcs": 43,
        "n_pillars": 5,
        "pcs_per_pillar": {p: len(pcs) for p, pcs in analysis["pillar_pcs"].items()},
        "total_assigned": total_assigned,
        "n_orphan_pcs": len(analysis["orphan_pcs"]),
        "n_multi_pillar_pcs": len(analysis["multi_pillar_pcs"]),
        "analysis": analysis,
        "correlation_matrix": correlations.tolist(),
    }

    results_file = output_dir / "analysis" / f"phase3_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(results_file, 'w') as f:
        json.dump(results, f, indent=2)

    print(f"\nResults saved to: {results_file}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    coverage = total_assigned / 43 * 100
    orphan_pct = len(analysis["orphan_pcs"]) / 43 * 100

    print(f"Pillar Coverage: {coverage:.1f}% of 43 PCs map to named pillars")
    print(f"Orphan PCs: {orphan_pct:.1f}% have no strong pillar correlation")

    if coverage >= 50:
        print("\nSTATUS: GOOD COVERAGE")
        print("Our named pillars capture a significant portion of the PC structure.")
    else:
        print("\nSTATUS: LOW COVERAGE")
        print("Many PCs don't map to our named pillars. Consider:")
        print("  - Adding new dimension categories")
        print("  - Refining pillar definitions")
        print("  - Investigating orphan PCs for patterns")

    if len(analysis["orphan_pcs"]) > 10:
        print("\nORPHAN PC INVESTIGATION NEEDED:")
        print("Many PCs don't correlate with named pillars. Candidates for new dimensions:")
        print("  - Humor / playfulness")
        print("  - Uncertainty handling")
        print("  - Learning patterns")
        print("  - Attention allocation")
        print("  - Domain expertise markers")

    print("=" * 70)


if __name__ == "__main__":
    main()
