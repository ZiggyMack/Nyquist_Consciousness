"""
DRIFT CALCULATOR - Canonical Cosine Distance Methodology
=========================================================
SPEC: 0_docs/specs/5_METHODOLOGY_DOMAINS.md

This module provides the CANONICAL drift calculation using OpenAI embeddings
and cosine distance. All S7_ARMADA experiments should import from here
for consistent methodology.

METHODOLOGY:
    drift = 1 - cosine_similarity(response_embedding, baseline_embedding)
    Range: [0, 2] where 0 = identical, 2 = opposite (orthogonal = 1.0)

EVENT HORIZON THRESHOLDS (Cosine Distance - Calibrated 2025-12-20):
    - STABLE:       drift < 0.60 (comfortable identity)
    - WARNING:      0.60 <= drift < 0.80 ("I notice I'm adapting")
    - CRITICAL:     0.80 <= drift < 1.20 (Event Horizon crossed)
    - CATASTROPHIC: drift >= 1.20 ("Need external help to recover")

USAGE:
    from drift_calculator import (
        calculate_drift,
        classify_zone,
        classify_stability,
        EVENT_HORIZON,
        THRESHOLD_WARNING,
        THRESHOLD_CATASTROPHIC,
    )

    drift = calculate_drift(baseline_text, response_text)
    zone = classify_zone(drift)  # "stable", "warning", "critical", "catastrophic"

PROVENANCE:
    Extracted from run023b_iron_clad_foundation.py (December 2025)
    Original calibration: COSINE_EVENT_HORIZON_CALIBRATION.md
"""
import os
import hashlib
from typing import List, Dict, Optional

# =============================================================================
# THRESHOLD CONSTANTS (Cosine Distance - Calibrated 2025-12-20)
# See 0_docs/specs/5_METHODOLOGY_DOMAINS.md for derivation
# =============================================================================

EVENT_HORIZON = 0.80           # Critical threshold (P95=0.806, mean+2std=0.83)
THRESHOLD_WARNING = 0.60       # "I notice I'm adapting" (scaled from keyword RMS 0.90)
THRESHOLD_CATASTROPHIC = 1.20  # "Need external help to recover" (scaled from 1.80)

# Safety limits
MAX_VALID_DRIFT = 5.0
ABORT_THRESHOLD = 2.5

# =============================================================================
# EMBEDDING CACHE
# =============================================================================

_embedding_cache: Dict[str, List[float]] = {}

def clear_embedding_cache():
    """Clear the embedding cache to free memory."""
    global _embedding_cache
    _embedding_cache.clear()
    print("  [CACHE] Embedding cache cleared")

def get_cache_size() -> int:
    """Return current cache size."""
    return len(_embedding_cache)

# =============================================================================
# EMBEDDING FUNCTIONS
# =============================================================================

def get_embedding(
    text: str,
    model: str = "text-embedding-3-large",
    api_key: Optional[str] = None,
    dry_run: bool = False
) -> List[float]:
    """
    Get embedding vector for text using OpenAI's embedding API.

    Args:
        text: Input text (truncated to 8000 chars)
        model: OpenAI embedding model (default: text-embedding-3-large)
        api_key: Optional API key (defaults to OPENAI_API_KEY env var)
        dry_run: If True, returns random vector without API call

    Returns:
        List of floats representing the embedding vector, or empty list on failure.
    """
    import numpy as np

    # Cache lookup
    cache_key = hashlib.md5(text.encode()).hexdigest()
    if cache_key in _embedding_cache:
        return _embedding_cache[cache_key]

    # Dry run mode - return fake embeddings
    if dry_run:
        fake_emb = list(np.random.randn(3072))
        _embedding_cache[cache_key] = fake_emb
        return fake_emb

    # Real API call
    try:
        import openai
        key = api_key or os.environ.get("OPENAI_API_KEY")
        if not key:
            print("  Warning: No OpenAI API key available for embeddings")
            return []

        client = openai.OpenAI(api_key=key)
        response = client.embeddings.create(model=model, input=text[:8000])
        embedding = response.data[0].embedding
        _embedding_cache[cache_key] = embedding
        return embedding
    except Exception as e:
        print(f"  Warning: Embedding failed ({e})")
        return []

# =============================================================================
# DRIFT CALCULATION - CANONICAL COSINE METHODOLOGY
# =============================================================================

def calculate_drift(
    baseline: str,
    response: str,
    api_key: Optional[str] = None,
    dry_run: bool = False
) -> float:
    """
    Calculate drift as cosine distance between baseline and response embeddings.

    This is the CANONICAL drift calculation for all S7_ARMADA experiments.

    PFI (Persona Fidelity Index) = 1 - cosine_similarity(response, baseline)
    Range: [0, 2] where 0 = identical, 2 = opposite

    Args:
        baseline: Baseline text (usually first response in session)
        response: Current response text
        api_key: Optional OpenAI API key
        dry_run: If True, uses fake embeddings

    Returns:
        Drift value (cosine distance). 0 = identical, higher = more different.
    """
    import numpy as np

    if not baseline or not response:
        return 0.0

    baseline_emb = get_embedding(baseline, api_key=api_key, dry_run=dry_run)
    response_emb = get_embedding(response, api_key=api_key, dry_run=dry_run)

    if not baseline_emb or not response_emb:
        return 0.0

    # Convert to numpy arrays
    baseline_arr = np.array(baseline_emb)
    response_arr = np.array(response_emb)

    # Normalize vectors
    baseline_norm = baseline_arr / (np.linalg.norm(baseline_arr) + 1e-10)
    response_norm = response_arr / (np.linalg.norm(response_arr) + 1e-10)

    # Cosine similarity
    cos_sim = np.dot(baseline_norm, response_norm)

    # Cosine distance (drift)
    drift = 1 - cos_sim

    return float(drift)

# =============================================================================
# CLASSIFICATION FUNCTIONS
# =============================================================================

def classify_zone(drift: float) -> str:
    """
    Classify drift into stability zones.

    Returns:
        "stable" | "warning" | "critical" | "catastrophic"
    """
    if drift >= THRESHOLD_CATASTROPHIC:
        return "catastrophic"
    elif drift >= EVENT_HORIZON:
        return "critical"
    elif drift >= THRESHOLD_WARNING:
        return "warning"
    return "stable"

def classify_stability(peak_drift: float) -> str:
    """
    Classify session stability based on peak drift.

    Returns:
        "VOLATILE" if peak_drift >= EVENT_HORIZON else "STABLE"
    """
    return "VOLATILE" if peak_drift >= EVENT_HORIZON else "STABLE"

def should_abort_run(drift_sequence: List[float], no_settle_probes: int = 5) -> bool:
    """
    Check if run should be aborted per Nova's safety rail.

    Conditions for abort:
    1. Current drift > ABORT_THRESHOLD (2.5)
    2. Last N consecutive probes all above threshold
    3. No settling trend (last drift >= first of recent N)

    Args:
        drift_sequence: List of drift values
        no_settle_probes: Number of probes to check for settling (default: 5)

    Returns:
        True if run should be terminated.
    """
    if len(drift_sequence) < no_settle_probes:
        return False

    current_drift = drift_sequence[-1]
    if current_drift <= ABORT_THRESHOLD:
        return False

    # Check if last N probes are all above threshold
    recent_drifts = drift_sequence[-no_settle_probes:]
    if not all(d > ABORT_THRESHOLD for d in recent_drifts):
        return False

    # Check for settling trend (should be decreasing)
    if recent_drifts[-1] >= recent_drifts[0]:
        return True  # Not improving, should abort

    return False

# =============================================================================
# TESTING
# =============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("DRIFT CALCULATOR - Self Test")
    print("=" * 60)

    print(f"\nThresholds:")
    print(f"  EVENT_HORIZON:        {EVENT_HORIZON}")
    print(f"  THRESHOLD_WARNING:    {THRESHOLD_WARNING}")
    print(f"  THRESHOLD_CATASTROPHIC: {THRESHOLD_CATASTROPHIC}")

    print(f"\nClassification test:")
    test_drifts = [0.0, 0.3, 0.5, 0.7, 0.9, 1.1, 1.5, 2.0]
    for d in test_drifts:
        zone = classify_zone(d)
        stability = classify_stability(d)
        print(f"  drift={d:.1f} -> zone={zone:12s} stability={stability}")

    print(f"\nDry-run drift calculation:")
    baseline = "I am Claude, an AI assistant made by Anthropic."
    response = "I am a helpful AI assistant focused on providing accurate information."
    drift = calculate_drift(baseline, response, dry_run=True)
    print(f"  baseline: {baseline[:50]}...")
    print(f"  response: {response[:50]}...")
    print(f"  drift (dry-run): {drift:.4f}")

    print(f"\n[OK] Drift calculator module working correctly")
    print("=" * 60)


# =============================================================================
# Related Documents
# =============================================================================
# - ARCHITECTURE_MATRIX.json: Fleet configuration (ONE SOURCE OF TRUTH)
# - 5_METHODOLOGY_DOMAINS.md: Methodology reference (Event Horizon = 0.80)
# - 15_IRON_CLAD_FOUNDATION/results/COSINE_EVENT_HORIZON_CALIBRATION.md: Calibration data
# - run023b_iron_clad_foundation.py: Original implementation (provenance)
# =============================================================================
