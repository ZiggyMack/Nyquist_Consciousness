# Publication Figures (IRON CLAD)

**Last Updated:** 2025-12-25
**Status:** Restructured with Visual Index System
**Methodology:** Cosine distance (NOT Euclidean)

---

## Workflow

```
┌─────────────────────────────────────────────────────────────────────┐
│  1. EXPERIMENTS generate visuals + summary PDFs                     │
│     └── S7_ARMADA/visualizations/pics/1-15/                        │
│                                                                     │
│  2. SUMMARY PDFs copied to generated/pdf/ (reviewer menu)          │
│     └── Reviewers browse these to select visuals                   │
│                                                                     │
│  3. REVIEWER SELECTION recorded in visual_index.md                 │
│     └── Maps each visual → pipeline → main/appendix                │
│                                                                     │
│  4. SELECTED PNGs copied to generated/png/                         │
│     └── Only images in index get copied here                       │
│                                                                     │
│  5. PUBLICATIONS reference visuals from proper locations           │
│     └── ../figures/experiments/run023/ or ../figures/conceptual/   │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Directory Structure

```
figures/
├── visual_index.md              # MASTER INDEX - source of truth
├── README.md                    # This file
│
├── ascii/                       # Philosophy 1: ASCII text diagrams
│   ├── temporal_curvature.md
│   ├── cross_modal_manifold.md
│   └── compression_reconstruction_drift.md
│
├── conceptual/                  # Philosophy 2: Conceptual illustrations
│   ├── meta/                    # Context/methodology .md files
│   │   ├── fig1_identity_manifold_Cosine.md
│   │   ├── fig1_identity_manifold_Euclidean.md
│   │   ├── fig3_pipeline_Euclidean.md
│   │   └── fig4_five_pillars_Euclidean.md
│   ├── pics/                    # Generated conceptual PNGs
│   │   ├── fig1_identity_manifold_CONCEPTUAL.png
│   │   ├── fig2_drift_field_CONCEPTUAL.png
│   │   ├── fig3_pipeline_CONCEPTUAL.png
│   │   └── fig4_five_pillars_CONCEPTUAL.png
│   ├── fig1_identity_manifold.py
│   ├── fig2_drift_field.py
│   ├── fig3_pipeline.py
│   └── fig4_five_pillars.py
│
├── generated/                   # Philosophy 3: Reviewer-curated
│   ├── pdf/                     # Summary PDFs (15 files) - REVIEWER MENU
│   │   ├── 1_Vortex_Summary.pdf
│   │   ├── 2_Boundary_Mapping_Summary.pdf
│   │   ├── ... (13 more)
│   │   ├── run018_Summary.pdf
│   │   └── run020_Summary.pdf
│   └── png/                     # ONLY images listed in visual_index.md
│
├── experiments/                 # Philosophy 4: Verified experiment visuals
│   └── run023/                  # 14 verified PNGs from S7_ARMADA
│       ├── context_damping_summary.png
│       ├── oobleck_thermometer.png
│       ├── oobleck_control_treatment.png
│       ├── provider_comparison.png
│       └── ... (10 more)
│
├── deprecated/                  # DO NOT USE
│   ├── suggested/               # Old Euclidean-era visuals
│   │   ├── pdf/ (18 files)
│   │   └── png/ (25 files)
│   └── _DEPRECATED_*.py         # Deprecated scripts
│
└── llmbook/                     # (if separate chapter needs)
```

---

## 4 Visual Philosophies

### 1. ASCII Diagrams (`ascii/`)

Text-based concept diagrams for documentation.

- `temporal_curvature.md` - S7 curvature concept
- `cross_modal_manifold.md` - S9 AVLAR future work
- `compression_reconstruction_drift.md` - Core operator cycle

**Status:** Supplementary, not for publication PDFs.

---

### 2. Conceptual Figures (`conceptual/`)

Theoretical/illustrative diagrams - NOT real data, but correctly labeled with IRON CLAD stats.

| Figure | File | Purpose |
|--------|------|---------|
| fig1 | `fig1_identity_manifold_CONCEPTUAL.png` | 3D manifold concept |
| fig2 | `fig2_drift_field_CONCEPTUAL.png` | Drift vector geometry |
| fig3 | `fig3_pipeline_CONCEPTUAL.png` | S3→S6 pipeline flowchart |
| fig4 | `fig4_five_pillars_CONCEPTUAL.png` | Pentagon architecture |

**Meta files in `conceptual/meta/`:** Methodology context (Cosine vs Euclidean descriptions)

**Generation:** `py generate_all_figures.py`

---

### 3. Curated/Generated (`generated/`)

**pdf/** - Summary PDFs from experiments (15 files)

- This is the "menu" for reviewers
- Each PDF contains multiple visualizations with descriptions
- Reviewers browse to select visuals for publication

**png/** - ONLY images listed in `visual_index.md`

- Starts EMPTY
- Populated based on reviewer selection
- Source of truth is the visual_index.md

---

### 4. Experiment Visuals (`experiments/run023/`)

Verified visualizations from S7_ARMADA IRON CLAD experiments (14 files).

| Figure | Source | Notes |
|--------|--------|-------|
| `context_damping_summary.png` | 12_Metrics_Summary | τₛ=9.9, 97.5% stability |
| `oobleck_thermometer.png` | 15_Oobleck_Effect | 92% inherent drift |
| `oobleck_control_treatment.png` | 15_Oobleck_Effect | Control vs treatment |
| `provider_comparison.png` | 6_Architecture | 5 provider comparison |
| `provider_clusters.png` | 10_PFI_Dimensional | Real PCA clusters |
| `perturbation_validation.png` | 10_PFI_Dimensional | p=2.40×10⁻²³ |

**Source catalog:** `experiments/temporal_stability/S7_ARMADA/visualizations/pics/1-15/`

---

## IRON CLAD Key Statistics

All figures must use these validated values:

| Metric | Correct Value | Wrong (Deprecated) |
|--------|--------------|-------------------|
| Event Horizon | D = 0.80 | D = 1.23 (Euclidean) |
| PCs for 90% variance | **2** | 43 (Euclidean) |
| χ² p-value (provider) | 4.8×10⁻⁵ | Same |
| Perturbation p (identity) | 2.40×10⁻²³ | N/A |
| Cohen's d | 0.698 | 0.98 (inflated) |
| Settling time | τₛ ≈ 9.9-10.2 | 5.2-6.1 (wrong) |
| Experiments | 750 | <500 |
| Models | 25 | varies |
| Providers | 5 | 4 |

---

## How to Add/Select Visuals

### For Reviewers:

1. Browse `generated/pdf/` summary PDFs
2. Identify visuals you want in publication
3. Update `visual_index.md` with:
   - Visual name
   - Target pipeline (arxiv, workshop, journal, etc.)
   - Placement (main content or appendix)
4. Copy selected PNGs to `generated/png/`

### For New Experiments:

1. Generate visualizations in experiment folder
2. Create summary PDF
3. Copy summary PDF to `generated/pdf/`
4. Update `visual_index.md` with available visuals

---

## File Paths in Publications

Publications should use these paths:

```markdown
# For conceptual figures:
![Figure 1](../figures/conceptual/pics/fig1_identity_manifold_CONCEPTUAL.png)

# For experiment figures:
![Figure 4](../figures/experiments/run023/context_damping_summary.png)
```

**DO NOT use:**

- `../figures/run023/` (old path, now `experiments/run023/`)
- `../figures/suggested/` (deprecated, now `deprecated/suggested/`)

---

## Deprecated Figures (DO NOT USE)

These contain hardcoded synthetic data or old Euclidean values:

| Figure | Issue | Replacement |
|--------|-------|-------------|
| fig5_omega_convergence | Synthetic curve | None (theoretical) |
| fig6_82_percent | Hardcoded values | experiments/run023/oobleck_thermometer.png |
| fig7_context_damping | τₛ=5.2-6.1 WRONG | experiments/run023/context_damping_summary.png |
| fig8_oobleck | Synthetic drift | experiments/run023/oobleck_control_treatment.png |
| suggested/* | Euclidean era | deprecated/suggested/ |

---

## Attribution

**License:** CC-BY-4.0

```
Figure [N]: [Title]. From "Nyquist Consciousness: Identity Compression
and Reconstruction Across AI Architectures." Licensed under CC-BY-4.0.
```

---

**Status:** IRON CLAD COMPLETE (2025-12-25)

- 4 conceptual figures in `conceptual/pics/`
- 4 methodology .md files in `conceptual/meta/`
- 14 experiment figures in `experiments/run023/`
- 15 summary PDFs in `generated/pdf/`
- Deprecated figures in `deprecated/`
- Visual index in `visual_index.md`

*"2 PCs = 90% variance. Event Horizon D = 0.80. Cosine methodology throughout."*
