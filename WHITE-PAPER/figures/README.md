# Publication Figures (IRON CLAD)

**Last Updated:** 2025-12-25
**Status:** Reorganized - 4 Visual Philosophies
**Methodology:** Cosine distance (NOT Euclidean)

---

## 4 Visual Philosophies

### 1. ASCII Diagrams (`ascii/`)
Text-based concept diagrams for documentation and quick reference.
- `temporal_curvature.md` - S7 curvature measurement concept
- `cross_modal_manifold.md` - S9 AVLAR future work
- `compression_reconstruction_drift.md` - Core operator cycle

**Status:** Supplementary, not for publication PDFs.

---

### 2. Conceptual Figures (`conceptual/pics/`)
Theoretical/illustrative diagrams - NOT real data, but correctly labeled.

| Figure | File | Purpose |
|--------|------|---------|
| fig1 | `fig1_identity_manifold_CONCEPTUAL.png` | 3D manifold concept |
| fig2 | `fig2_drift_field_CONCEPTUAL.png` | Drift vector geometry |
| fig3 | `fig3_pipeline_CONCEPTUAL.png` | S3→S6 pipeline flowchart |
| fig4 | `fig4_five_pillars_CONCEPTUAL.png` | Pentagon architecture |

**Generation:** `py generate_all_figures.py`

---

### 3. Curated/Selected Figures (`run023/`)
Verified visualizations selected from S7_ARMADA experiments for publication.

| Figure | Source | Replaces |
|--------|--------|----------|
| `context_damping_summary.png` | pics/12_Metrics_Summary/ | DEPRECATED fig7 |
| `oobleck_thermometer.png` | pics/15_Oobleck_Effect/ | DEPRECATED fig6 |
| `oobleck_control_treatment.png` | pics/15_Oobleck_Effect/ | DEPRECATED fig8 |
| `provider_comparison.png` | pics/6_Architecture/ | DEPRECATED fig2 |
| `provider_clusters.png` | pics/10_PFI_Dimensional/ | Real PCA data |
| `perturbation_validation.png` | pics/10_PFI_Dimensional/ | Statistical validation |

**Selection criteria:** Reviewers pick from available visualizations.

---

### 4. Experiment Visualizations (Source)
Full catalog of generated visualizations from S7_ARMADA experiments.

**Location:** `experiments/temporal_stability/S7_ARMADA/visualizations/pics/`

| Folder | Contents |
|--------|----------|
| 1_Vortex/ | Identity vortex drain visualizations |
| 2_Boundary_Mapping/ | Phase portraits, 3D basins |
| 3_Stability/ | Stability analysis, pillar analysis |
| 4_Rescue/ | Rescue dynamics, recovery heatmaps |
| 5_Settling/ | Settling curves, waterfall spectrograms |
| 6_Architecture/ | Provider comparison |
| 7_interactive/ | HTML interactive visualizations |
| 8_Radar_Oscilloscope/ | Radar plots, oscilloscope views |
| 9_FFT_Spectral/ | FFT analysis, pole-zero plots |
| 10_PFI_Dimensional/ | PCA, perturbation validation |
| 11_Unified_Dashboard/ | Per-model dashboards |
| 12_Metrics_Summary/ | Context damping, fleet network |
| 15_Oobleck_Effect/ | 82% finding visualizations |
| run018/ | Historical Euclidean runs |
| run020/ | Historical ratio analysis |

**These are the "menu" for reviewers to select from.**

---

## Directory Structure

```
figures/
├── README.md                    (this file)
├── generate_all_figures.py      (Runs conceptual figures only)
│
├── conceptual/                  (Philosophy 2: Conceptual diagrams)
│   ├── pics/                    (OUTPUT - PNG files)
│   │   ├── fig1_identity_manifold_CONCEPTUAL.png
│   │   ├── fig2_drift_field_CONCEPTUAL.png
│   │   ├── fig3_pipeline_CONCEPTUAL.png
│   │   └── fig4_five_pillars_CONCEPTUAL.png
│   ├── fig1_identity_manifold.py
│   ├── fig2_drift_field.py
│   ├── fig3_pipeline.py
│   ├── fig4_five_pillars.py
│   └── *.md (methodology descriptions)
│
├── run023/                      (Philosophy 3: Curated selections)
│   └── (verified visualizations for publication)
│
├── deprecated/                  (DO NOT USE - wrong data)
│   └── _DEPRECATED_*.py
│
├── generated/                   (EMPTY - cleared stale files)
│   ├── png/
│   └── pdf/
│
├── ascii/                       (Philosophy 1: ASCII diagrams)
└── schemas/                     (Architectural reference)
```

---

## IRON CLAD Key Statistics

All figures must use these validated values (cosine methodology):

| Metric | Correct Value | Wrong (Deprecated) |
|--------|--------------|-------------------|
| Event Horizon | D = 0.80 | D = 1.23 (Euclidean) |
| PCs for 90% variance | **2** | 43 (Euclidean) |
| χ² p-value (provider) | 4.8×10⁻⁵ | Same (agnostic) |
| Perturbation p (identity) | 2.40×10⁻²³ | N/A |
| Cohen's d | 0.698 | 0.98 (inflated) |
| Settling time | τₛ ≈ 9.9-10.2 | 5.2-6.1 (wrong) |
| Experiments | 750 | <500 |
| Models | 25 | varies |
| Providers | 5 | 4 |

---

## Deprecated Figures (DO NOT USE)

These contain hardcoded synthetic data:

| Figure | Issue | Replacement |
|--------|-------|-------------|
| fig5_omega_convergence | Synthetic curve | None (theoretical) |
| fig6_82_percent | Hardcoded values | run023/oobleck_thermometer.png |
| fig7_context_damping | τₛ=5.2-6.1 WRONG | run023/context_damping_summary.png |
| fig8_oobleck | Synthetic drift | run023/oobleck_control_treatment.png |
| fig_workshop_combined | All deprecated | Use individual figures |

See `deprecated/README.md` for details.

---

## Figure Generation

### Regenerate Conceptual Figures
```bash
cd WHITE-PAPER/figures
py generate_all_figures.py
```

Output: `conceptual/pics/*.png`

### Copy Curated Figures to run023/
```bash
# From S7_ARMADA experiments
cp experiments/temporal_stability/S7_ARMADA/visualizations/pics/12_Metrics_Summary/context_damping_summary.png WHITE-PAPER/figures/run023/
cp experiments/temporal_stability/S7_ARMADA/visualizations/pics/15_Oobleck_Effect/oobleck_thermometer.png WHITE-PAPER/figures/run023/
```

---

## Color Schemes

### Provider Colors
- **Anthropic:** Blue (#2196F3)
- **OpenAI:** Purple (#9C27B0)
- **Google:** Green (#4CAF50)
- **xAI:** Orange (#FF9800)
- **Together:** Brown (#795548)

### Pillar Colors (Five Pillars)
- **Nova:** Purple (#9C27B0)
- **Claude:** Blue (#2196F3)
- **Gemini:** Green (#4CAF50)
- **Grok:** Red (#F44336)
- **Ziggy:** Orange (#FF9800)
- **Omega:** Gold (#FFD700)

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
- Deprecated figures in `deprecated/`
- Curated selections in `run023/`
- Source visualizations in S7_ARMADA `pics/1-15/`

*"2 PCs = 90% variance. Event Horizon D = 0.80. Cosine methodology throughout."*
