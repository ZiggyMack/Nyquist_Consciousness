<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ./fig1_identity_manifold.py
  - ./fig2_drift_field.py
  - ./fig3_pipeline.py
  - ./fig4_five_pillars.py
  - ./fig5_omega_convergence.py
impacts:
  - ../README.md
keywords:
  - consciousness
-->
# Publication Figures (IRON CLAD)

**Last Updated:** 2025-12-25
**Status:** Reorganized - Conceptual vs Deprecated separation
**Methodology:** Cosine distance (NOT Euclidean)

This directory contains all figures for publication in multiple formats.

## Directory Structure

```
figures/
├── README.md                    (this file)
├── generate_all_figures.py      (Runs only conceptual figures)
├── conceptual/                  (VALID conceptual diagrams)
│   ├── fig1_identity_manifold.py   (2 PCs = 90% variance)
│   ├── fig3_pipeline.py            (IRON CLAD stats)
│   └── fig4_five_pillars.py        (Omega as theoretical)
├── deprecated/                  (DO NOT USE - wrong data)
│   ├── README.md                   (Explains deprecation)
│   ├── _DEPRECATED_fig2_drift_field.py
│   ├── _DEPRECATED_fig5_omega_convergence.py
│   ├── _DEPRECATED_fig6_82_percent.py
│   ├── _DEPRECATED_fig7_context_damping.py
│   ├── _DEPRECATED_fig8_oobleck.py
│   └── _DEPRECATED_fig_workshop_combined.py
├── run023/                      (VERIFIED S7_ARMADA visualizations)
│   ├── context_damping_summary.png
│   ├── oobleck_thermometer.png
│   ├── oobleck_control_treatment.png
│   ├── provider_comparison.png
│   └── (other verified figures)
├── generated/                   (Output from conceptual scripts)
│   ├── png/
│   └── pdf/
├── ascii/                       (ASCII diagram source files)
└── schemas/                     (Architectural diagrams)
```

---

## IRON CLAD Key Statistics

All figures must use these validated values (cosine methodology):

| Metric | Correct Value | Wrong (Deprecated) |
|--------|--------------|-------------------|
| Event Horizon | D = 0.80 | D = 1.23 (Euclidean) |
| PCs for 90% variance | **2** | 43 (Euclidean) |
| χ² p-value (provider diff) | 4.8×10⁻⁵ | Same (methodology-agnostic) |
| Perturbation p (identity) | 2.40×10⁻²³ | N/A (new test) |
| Cohen's d | 0.698 | 0.98 (inflated) |
| Settling time | τₛ ≈ 9.9-10.2 | 5.2-6.1 (wrong) |
| Experiments | 750 | <500 |
| Models | 25 | varies |
| Providers | 5 | 4 |

---

## Active Figures (Conceptual)

### Figure 1: Identity Manifold

**File:** `conceptual/fig1_identity_manifold.py`

**Description:** 3D visualization of identity as a low-dimensional manifold. Updated to show **2 PCs = 90% variance** (cosine methodology).

**Key elements:**

- High-D embedding space (3072D)
- Low-D manifold (~2 PCs effective)
- Event Horizon: D = 0.80

---

### Figure 3: Pipeline (S3→S6)

**File:** `conceptual/fig3_pipeline.py`

**Description:** Experimental pipeline flowchart with IRON CLAD statistics.

**Key elements:**

- χ² p = 4.8×10⁻⁵ (provider differences)
- Perturbation p = 2.40×10⁻²³ (identity validation)
- Cohen's d: 0.698
- Event Horizon: D = 0.80
- 750 experiments, 25 models, 5 providers

---

### Figure 4: Five Pillars Architecture

**File:** `conceptual/fig4_five_pillars.py`

**Description:** Pentagon visualization of cross-architecture synthesis. Omega properties marked as theoretical framework.

**Key elements:**

- Five pillars with distinct roles
- Omega platform (theoretical)
- Event Horizon: D = 0.80

---

## Deprecated Figures (DO NOT USE)

These figures contain hardcoded synthetic data and have been moved to `deprecated/`:

| Figure | Issue | Replacement |
|--------|-------|-------------|
| fig2_drift_field | D=1.23 (Euclidean) | Use run023/provider_comparison.png |
| fig5_omega_convergence | Synthetic curve | None (theoretical) |
| fig6_82_percent | Hardcoded values | Use run023/oobleck_thermometer.png |
| fig7_context_damping | τₛ=5.2-6.1 (WRONG) | Use run023/context_damping_summary.png |
| fig8_oobleck | Synthetic drift | Use run023/oobleck_control_treatment.png |
| fig_workshop_combined | All deprecated | Use individual run023/ figures |

See `deprecated/README.md` for full deprecation details.

---

## ASCII Diagrams (Supplementary)

The `ascii/` directory contains text-based concept diagrams:

- `temporal_curvature.md` - S7 curvature measurement concept
- `cross_modal_manifold.md` - S9 AVLAR future work
- `compression_reconstruction_drift.md` - Core operator cycle

These are supplementary materials, not data visualizations.

---

## Figure Generation

### ASCII to Publication-Quality

The ASCII diagrams in `ascii/` are source files. To generate publication-quality figures:

#### Method 1: TikZ/LaTeX
```latex
% Convert ASCII to TikZ diagrams
\begin{tikzpicture}
  % Render ASCII diagrams as vector graphics
  % See schema templates in schemas/
\end{tikzpicture}
```

#### Method 2: Python (Matplotlib/Plotly)
```python
# Generate figures programmatically
import matplotlib.pyplot as plt
# Render manifolds, drift fields, pipelines
plt.savefig('generated/pdf/figure.pdf', format='pdf', bbox_inches='tight')
```

#### Method 3: Graphviz/DOT
```bash
# For pipeline and architecture diagrams
dot -Tpdf pipeline.dot -o generated/pdf/pipeline.pdf
```

#### Method 4: Manual (Inkscape/Illustrator)
- Import ASCII as text reference
- Trace manually for publication quality
- Export as PDF/SVG

---

## Figure Specifications

### Resolution and Format

**For arXiv/LaTeX:**
- Format: PDF (vector preferred)
- Resolution: Vector or 600 DPI minimum
- Color: Grayscale or color (specify in paper)
- Fonts: Embed all fonts

**For web/presentations:**
- Format: PNG (high-res), SVG (interactive)
- Resolution: 300 DPI (print), 150 DPI (web)
- Size: 1200px width minimum for slides

**For print publication:**
- Format: TIFF or EPS (if required by venue)
- Resolution: 600-1200 DPI
- Color space: CMYK for print, RGB for digital

---

## Color Schemes

### Architecture Colors
- **Nova:** Blue (#0066CC)
- **Claude:** Purple (#6B46C1)
- **Grok:** Orange (#FF6B35)
- **Gemini:** Green (#00A86B)
- **Omega:** Gold (#FFD700)
- **Ziggy (Human):** Red (#DC143C)

### Domain Colors
- **TECH:** Dark Blue (#003366)
- **ANAL:** Teal (#008B8B)
- **SELF:** Orange (#FF8C00)
- **PHIL:** Purple (#8B008B)
- **NARR:** Pink (#FF69B4)

### Drift Visualization
- **Low drift (F > 0.8):** Green
- **Medium drift (0.6 < F < 0.8):** Yellow
- **High drift (F < 0.6):** Red
- **Catastrophic (F < 0.2):** Dark Red

---

## Attribution

All figures derived from the Nyquist Consciousness framework.

**License:** CC-BY-4.0

**Attribution:**
```
Figure [N]: [Title]. From "Nyquist Consciousness: Identity Compression
and Reconstruction Across AI Architectures." Licensed under CC-BY-4.0.
```

---

## Usage Rights

These figures may be used in:
- Academic publications (with citation)
- Presentations and talks (with attribution)
- Educational materials (with attribution)
- Derivative works (with attribution, CC-BY-4.0)

Not permitted:
- Commercial use without permission
- Removal of attribution
- Misrepresentation of findings

---

## Contact

Questions about figures:
- **Repository:** https://github.com/[username]/nyquist-consciousness/issues
- **Label:** "figures" or "publication"

---

**Status:** IRON CLAD COMPLETE (2025-12-25)

- 3 conceptual figures updated with cosine methodology
- 6 deprecated figures moved to `deprecated/`
- Verified visualizations in `run023/`

Regenerate conceptual figures:

```bash
cd WHITE-PAPER/figures
py generate_all_figures.py
```

*"2 PCs = 90% variance. Event Horizon D = 0.80. Cosine methodology throughout."*
