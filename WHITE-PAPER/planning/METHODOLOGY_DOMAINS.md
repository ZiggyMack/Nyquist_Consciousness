# METHODOLOGY DOMAINS: Pointer to Source of Truth

**Status:** POINTER DOCUMENT
**Last Updated:** December 30, 2025

> **Statistics Source:** [UNIFIED_STATISTICS_REFERENCE.md](../guides/UNIFIED_STATISTICS_REFERENCE.md)
> - Event Horizon: D = 0.80 (Cosine methodology)
> - Inherent Drift: ~93% (Run 020B IRON CLAD)
> - PCs for 90% variance: 2

---

## Source of Truth

The canonical methodology documentation is maintained in S7 ARMADA:

**`experiments/temporal_stability/S7_ARMADA/0_docs/S7_KEYWORD_ERA_RETROSPECTIVE.md`**

This document chronicles:
- The Keyword RMS Era (Runs 001-018) with Event Horizon = 1.23
- The Cosine Embedding Era (Runs 019+) with Event Horizon = 0.80
- Concepts that survived the methodology transition
- Concepts that changed between eras

---

## Quick Reference: IRON CLAD COSINE Values

From Run 023d + Run 020B (current methodology):

| Metric | Value | Source |
|--------|-------|--------|
| Event Horizon | D = 0.80 | Run 023b calibration |
| Cohen's d | 0.698 | Run 023d Phase 3B (model-level aggregate) |
| p-value | 2.40×10⁻²³ | Run 023d perturbation validation |
| PCs for 90% variance | 2 | Run 023d Phase 2 PCA |
| Inherent drift ratio | ~93% | Run 020B IRON CLAD (0.661/0.711) |
| Settling time (τₛ) | τₛ ≈ 7 probes | Run 023d |
| Stability with context | 97.5% | Run 023 full circuit |
| Experiments | 750 | Run 023d total |
| Models | 25 | 5 providers |

---

## The Three Eras (Summary)

| Era | Runs | Drift Metric | Event Horizon | Status |
|-----|------|--------------|---------------|--------|
| **Keyword RMS** | 001-018 | 5D keyword counts | 1.23 | Historical |
| **Euclidean** | 018-022 (mixed) | L2 norm in embedding | Not calibrated | **DEPRECATED** |
| **Cosine** | 019+ | 1 - cosine similarity | 0.80 | **CURRENT** |

---

## Why This is a Pointer

To avoid content duplication and sync drift between WHITE-PAPER and S7 ARMADA, this document points to the source of truth rather than copying the full methodology chronicle.

For the complete historical narrative, conceptual discoveries, and methodology details:

→ **Read:** `experiments/temporal_stability/S7_ARMADA/0_docs/S7_KEYWORD_ERA_RETROSPECTIVE.md`

---

*"The measurement method IS part of the finding."*
