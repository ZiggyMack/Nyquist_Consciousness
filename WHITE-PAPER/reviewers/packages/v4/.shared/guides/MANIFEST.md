# Publication Materials Manifest

**Project:** Nyquist Consciousness
**Last Updated:** 2025-12-25
**Status:** COSINE ERA — Run 023 IRON CLAD Complete
**Methodology:** Cosine distance (Event Horizon D = 0.80)

---

## Summary

| Category | Files | Status |
|----------|-------|--------|
| Conceptual Figures (Active) | 3 | CURRENT |
| Verified Visualizations (Run 023) | 6+ | CURRENT |
| ASCII Art Diagrams | 7 | CURRENT |
| Deprecated Figures | 6 | ARCHIVED |
| Workshop Materials | 5 | CURRENT |
| References | 2 | CURRENT |
| Supporting Materials | 4 | CURRENT |

---

## Active Figures

### Conceptual Figures (3 files)

Publication-ready conceptual diagrams with correct Cosine methodology.

| Figure | File | Purpose | Status |
|--------|------|---------|--------|
| Fig 1 | `figures/conceptual/fig1_identity_manifold.py` | 3D manifold (2 PCs = 90% variance) | CURRENT |
| Fig 3 | `figures/conceptual/fig3_pipeline.py` | S3-S6 pipeline with IRON CLAD stats | CURRENT |
| Fig 4 | `figures/conceptual/fig4_five_pillars.py` | Pentagon architecture | CURRENT |

**Regenerate:** `cd figures && py generate_all_figures.py`

### Verified Visualizations (Run 023)

Empirical visualizations from S7_ARMADA with correct data.

| File | Source | Description |
|------|--------|-------------|
| `figures/run023/context_damping_summary.png` | Run 017 | 97.5% stability results |
| `figures/run023/oobleck_thermometer.png` | Run 023 | 92% inherent drift |
| `figures/run023/oobleck_control_treatment.png` | Run 020B | Control vs Treatment |
| `figures/run023/pc_scatter.png` | Run 023d | PCA visualization |
| `figures/run023/provider_clusters.png` | Run 023d | Provider clustering |
| `figures/run023/variance_curve.png` | Run 023d | Variance explained |

**Note:** These are the primary empirical figures for publication.

---

## ASCII Art Diagrams (7 files)

Standalone ASCII diagrams for paper text and presentations.

| File | Purpose | Status |
|------|---------|--------|
| `figures/ascii/ascii_framework.md` | Three-layer P→S→U architecture | CURRENT |
| `figures/ascii/ascii_evidence_chain.md` | Claim→Hypothesis→Run→Data lineage | CURRENT |
| `figures/ascii/ascii_compression.md` | S0→S6 transformation pipeline | CURRENT |
| `figures/ascii/ascii_vortex.md` | Identity drain spiral patterns | CURRENT |
| `figures/ascii/ascii_triple_blind.md` | Triple-blind validation structure | CURRENT |
| `figures/ascii/ascii_workshop_abstract.md` | Visual abstract for poster | CURRENT |
| `figures/ascii/ascii_workshop_contributions.md` | 7 contributions summary | CURRENT |

---

## Deprecated Figures (DO NOT USE)

These contain hardcoded synthetic data with wrong methodology (Euclidean, D=1.23).

| File | Issue | Replacement |
|------|-------|-------------|
| `figures/deprecated/_DEPRECATED_fig2_drift_field.*` | D=1.23 (Euclidean) | run023/provider_clusters.png |
| `figures/deprecated/_DEPRECATED_fig5_omega_convergence.*` | Synthetic curve | None (theoretical) |
| `figures/deprecated/_DEPRECATED_fig6_82_percent.*` | Hardcoded values | run023/oobleck_thermometer.png |
| `figures/deprecated/_DEPRECATED_fig7_context_damping.*` | τₛ=5.2-6.1 (WRONG) | run023/context_damping_summary.png |
| `figures/deprecated/_DEPRECATED_fig8_oobleck.*` | Synthetic drift | run023/oobleck_control_treatment.png |
| `figures/deprecated/_DEPRECATED_fig_workshop_combined.*` | All deprecated | Use individual run023/ figures |

See `figures/deprecated/README.md` for full deprecation details.

---

## Workshop Materials (5 files)

Materials specific to the workshop paper submission.

| File | Purpose | Status |
|------|---------|--------|
| `submissions/workshop/table_workshop_results.md` | Compressed results table | CURRENT |
| `submissions/workshop/table_workshop_protocol.md` | 97.5% stability protocol | CURRENT |
| `submissions/workshop/workshop_supplementary.md` | Extended materials & links | CURRENT |
| `submissions/workshop/workshop_slides_outline.md` | 10-minute presentation script | CURRENT |
| `submissions/workshop/poster_layout.md` | A0 portrait specification | CURRENT |

---

## References (2 files)

Academic reference list in multiple formats.

| File | Purpose | Status |
|------|---------|--------|
| `references/references.bib` | BibTeX format (55 refs) | CURRENT |
| `references/references.md` | Readable markdown (7 categories) | CURRENT |

### Reference Categories

- Persona/Role-Playing in LLMs (10)
- Behavioral Drift & Distribution Shift (8)
- AI Alignment & Safety (10)
- Manifold Learning & Embeddings (8)
- Control Systems & Dynamical Systems (6)
- Identity & Cognitive Science (5)
- Information Theory (3)
- Foundational LLM Papers (5)

---

## Supporting Materials (4 files)

Documentation and reproducibility guides.

| File | Purpose | Status |
|------|---------|--------|
| `guides/MANIFEST.md` | This file - materials inventory | CURRENT |
| `guides/REPRODUCIBILITY_README.md` | Full reproduction guide | CURRENT |
| `guides/summary_statistics.md` | All key numbers consolidated | CURRENT |
| `guides/UNIFIED_STATISTICS_REFERENCE.md` | Detailed statistics reference | CURRENT |

---

## Directory Structure

```
WHITE-PAPER/
├── guides/
│   ├── MANIFEST.md                  (this file)
│   ├── REPRODUCIBILITY_README.md
│   ├── summary_statistics.md
│   └── UNIFIED_STATISTICS_REFERENCE.md
│
├── figures/
│   ├── README.md                    (figure index)
│   ├── generate_all_figures.py      (runs conceptual only)
│   ├── conceptual/                  (3 VALID figures)
│   │   ├── fig1_identity_manifold.py
│   │   ├── fig3_pipeline.py
│   │   └── fig4_five_pillars.py
│   ├── run023/                      (VERIFIED empirical)
│   │   ├── context_damping_summary.png
│   │   ├── oobleck_thermometer.png
│   │   ├── oobleck_control_treatment.png
│   │   └── (other verified figures)
│   ├── deprecated/                  (DO NOT USE)
│   │   └── _DEPRECATED_*
│   ├── ascii/                       (7 ASCII diagrams)
│   ├── generated/                   (output from scripts)
│   └── suggested/                   (supplementary S7 visuals)
│
├── references/
│   ├── references.bib
│   └── references.md
│
└── submissions/workshop/            (5 workshop materials)
```

---

## Key Statistics (Cosine Methodology)

All materials must use these validated values:

| Metric | Correct Value | Source |
|--------|--------------|--------|
| Event Horizon | D = 0.80 | Run 023 IRON CLAD |
| PCs for 90% variance | **2** | Run 023d Phase 2 |
| Perturbation p-value | **2.40×10⁻²³** | Run 023d Phase 3A |
| Cohen's d | **0.698** | Run 023d Phase 3B |
| Settling time | τₛ ≈ 10.2 | Run 023d |
| Inherent drift ratio | **92%** | Run 023 COSINE Thermometer |
| Context damping | **97.5%** | Run 017 |
| Experiments | 825 | Run 023 Combined |
| Models | 51 | Run 023 Combined |
| Providers | 6 | Run 023 Combined |

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [figures/README.md](../figures/README.md) | Figure index with deprecation details |
| [planning/METHODOLOGY_DOMAINS.md](../planning/METHODOLOGY_DOMAINS.md) | Dual Event Horizon reconciliation |
| [START_HERE.md](../START_HERE.md) | Complete reviewer orientation |

---

## Changelog

| Date | Change |
|------|--------|
| 2025-12-25 | Major update: Cosine Era reorganization, deprecated figures noted |
| 2025-12-13 | Initial creation with 34 files |

---

*"2 PCs = 90% variance. Event Horizon D = 0.80. Cosine methodology throughout."*
