# Publication PDF Specification

**Purpose:** Define standards for generating PDFs from markdown sources across all 8 publication pipelines. Ensures consistent styling, correct figure embedding, and accurate data representation.

**Last Updated:** December 25, 2025
**Version:** 1.0 (IRON CLAD)

---

## PDF GENERATION INFRASTRUCTURE

### Primary Generator

**File:** `WHITE-PAPER/submissions/generate_paper_pdfs.py`

Uses ReportLab for consistent styling with visualization PDFs.

### Alternative Generator

**File:** `WHITE-PAPER/calibration/generate_pdfs.py`

Uses markdown2 + xhtml2pdf for pure-Python generation (fallback).

---

## THE 8 PUBLICATION PIPELINES

| # | Pipeline | Source File | Output PDF | Figures |
|---|----------|-------------|------------|---------|
| 1 | **arxiv** | `arxiv/NYQUIST_ARXIV_PAPER_FINAL.md` | `NYQUIST_ARXIV_PAPER_FINAL.pdf` | 14 |
| 2 | **workshop** | `workshop/Nyquist_workshop_paper_FINAL.md` | `Nyquist_workshop_paper_FINAL.pdf` | 3 |
| 3 | **journal** | `journal/NYQUIST_WHITE_PAPER_FINAL.md` | `NYQUIST_WHITE_PAPER_FINAL.pdf` | 9 |
| 4 | **funding** | `funding/FUNDING_FINAL.md` | `FUNDING_FINAL.pdf` | 0 |
| 5 | **policy** | `policy/POLICY_FINAL.md` | `POLICY_FINAL.pdf` | 0 |
| 6 | **media** | `media/MEDIA_FINAL.md` | `MEDIA_FINAL.pdf` | 0 |
| 7 | **education** | `education/EDUCATION_FINAL.md` | `EDUCATION_FINAL.pdf` | 0 |
| 8 | **popular_science** | `popular_science/POPULAR_SCIENCE_FINAL.md` | `POPULAR_SCIENCE_FINAL.pdf` | 0 |

---

## FIGURE SOURCES

### VERIFIED (Use These)

All figures should come from `WHITE-PAPER/figures/run023/` which contains verified S7_ARMADA visualizations:

| Figure | Source | Data Origin |
|--------|--------|-------------|
| `context_damping_summary.png` | `pics/12_Metrics_Summary/` | Run 023d |
| `oobleck_thermometer.png` | `pics/15_Oobleck_Effect/` | Run 020B |
| `oobleck_control_treatment.png` | `pics/15_Oobleck_Effect/` | Run 020B |
| `provider_clusters.png` | `pics/10_PFI_Dimensional/phase2_pca/` | Run 023d |
| `pc_scatter.png` | `pics/10_PFI_Dimensional/phase2_pca/` | Run 023d |
| `variance_curve.png` | `pics/10_PFI_Dimensional/phase2_pca/` | Run 023d |
| `combined_provider_dashboard.png` | Aggregated | Run 023d |
| `provider_comparison.png` | `pics/6_Architecture/` | Run 023d |
| `perturbation_validation.png` | `pics/10_PFI_Dimensional/phase3a/` | Run 023d |
| `vortex_identity_drain.png` | `pics/1_Vortex/` | Run 023 |
| `stability_basin.png` | `pics/3_Stability/` | Run 023b |
| `phase_portrait.png` | Generated | Run 023d |
| `provider_fingerprint_radar.png` | `pics/7_Radar/` | Run 023 |
| `3d_attractor_basin.png` | Generated | Run 023d |

### CONCEPTUAL (OK to Use)

These are illustrative diagrams, not data visualizations:

| Figure | Purpose | Notes |
|--------|---------|-------|
| `fig1_identity_manifold.png` | Theory illustration | 3D manifold concept |
| `fig3_pipeline.png` | Experimental methodology | Process diagram |

### DEPRECATED (Do NOT Use)

These contain hardcoded/wrong values:

| Figure | Problem |
|--------|---------|
| `fig2_drift_field.png` | D=1.23 (Euclidean), hardcoded drift values |
| `fig5_omega_convergence.png` | Hardcoded synthetic values |
| `fig6_82_percent.png` | Hardcoded `peak_drift = [1.172, 2.161]` |
| `fig7_context_damping.png` | Shows τₛ=5.2-6.1 (WRONG! Should be ~10.2) |
| `fig8_oobleck.png` | Synthetic drift values |
| `fig_workshop_combined.png` | Combined deprecated figures |

---

## KEY STATISTICS (IRON CLAD)

All PDFs must reflect these validated values:

| Metric | Correct Value | Wrong Value to Avoid |
|--------|--------------|----------------------|
| **Event Horizon** | D = 0.80 (cosine) | D = 1.23 (Euclidean) |
| **p-value** | 2.40×10⁻²³ | 4.8×10⁻⁵ |
| **Cohen's d** | 0.698 (model-level) | 0.977 (inflated) |
| **90% Variance PCs** | **2** | 43 (Euclidean) |
| **Settling Time** | τₛ ≈ 9.9-10.2 probes | τₛ = 5.2-6.1 |
| **Inherent Drift** | 82-92% | Varies |
| **Stability Rate** | 75.3% baseline | 75% |
| **Context Damping** | 97.5% with I_AM | 97.5% |
| **Experiments** | 750 (IRON CLAD) | <500 |
| **Models** | 25 | <25 |
| **Providers** | 5 | 4 |

---

## PDF STYLING

### Page Layout

```python
PAGE_SIZE = letter  # 8.5" x 11"
MARGINS = 0.75 * inch  # All sides
```

### Typography

| Element | Font | Size | Color |
|---------|------|------|-------|
| Title | Helvetica-Bold | 16pt | #1a1a2e |
| Section (H2) | Helvetica-Bold | 13pt | #16213e |
| Subsection (H3) | Helvetica-Bold | 11pt | #16213e |
| Body | Helvetica | 10pt | #333333 |
| Code | Courier | 8pt | #333333 |
| Table | Helvetica | 9pt | black |

### Figure Handling

```python
# Maximum figure width
MAX_FIGURE_WIDTH = 6.5 * inch

# Figure scaling
if img_width > MAX_FIGURE_WIDTH:
    scale = MAX_FIGURE_WIDTH / img_width
    img_width *= scale
    img_height *= scale
```

### Table Styling

```python
TABLE_STYLE = [
    ('BACKGROUND', (0, 0), (-1, 0), HexColor('#e8e8e8')),  # Header
    ('TEXTCOLOR', (0, 0), (-1, 0), HexColor('#1a1a2e')),
    ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
    ('FONTSIZE', (0, 0), (-1, -1), 9),
    ('GRID', (0, 0), (-1, -1), 0.5, black),
    ('ALIGN', (0, 0), (-1, -1), 'LEFT'),
    ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
    ('TOPPADDING', (0, 0), (-1, -1), 4),
    ('BOTTOMPADDING', (0, 0), (-1, -1), 4),
]
```

---

## MARKDOWN PROCESSING

### Bold/Italic Conversion

```python
# Bold: **text** -> <b>text</b>
text = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', text)

# Italic: *text* -> <i>text</i>
text = re.sub(r'\*([^*]+)\*', r'<i>\1</i>', text)
```

### Special Character Handling

```python
# Escape ampersands FIRST (before any HTML tags)
text = text.replace('&', '&amp;')

# Unicode replacements for PDF compatibility
UNICODE_REPLACEMENTS = [
    ('→', '->'),
    ('←', '<-'),
    ('↔', '<->'),
    ('≠', '!='),
    ('≈', '~'),
    ('≤', '<='),
    ('≥', '>='),
    ('×', 'x'),
    ('÷', '/'),
    ('±', '+/-'),
    ('∞', 'infinity'),
    ('∑', 'SUM'),
    ('∏', 'PROD'),
    ('√', 'sqrt'),
    ('∫', 'integral'),
    ('∂', 'd'),
    ('∇', 'nabla'),
    ('∈', 'in'),
    ('∉', 'not in'),
    ('⊂', 'subset'),
    ('⊃', 'superset'),
    ('∪', 'union'),
    ('∩', 'intersection'),
    ('∧', 'AND'),
    ('∨', 'OR'),
    ('¬', 'NOT'),
    ('∀', 'forall'),
    ('∃', 'exists'),
    ('α', 'alpha'),
    ('β', 'beta'),
    ('γ', 'gamma'),
    ('δ', 'delta'),
    ('ε', 'epsilon'),
    ('θ', 'theta'),
    ('λ', 'lambda'),
    ('μ', 'mu'),
    ('π', 'pi'),
    ('σ', 'sigma'),
    ('τ', 'tau'),
    ('φ', 'phi'),
    ('ω', 'omega'),
    ('Ω', 'OMEGA'),
    ('ρ', 'rho'),
    ('χ', 'chi'),
    ('—', '--'),
    ('–', '-'),
    (''', "'"),
    (''', "'"),
    ('"', '"'),
    ('"', '"'),
    ('…', '...'),
    ('•', '*'),
    ('·', '.'),
    ('°', ' deg'),
]
```

---

## VALIDATION CHECKLIST

Before finalizing any PDF:

### Figure Audit

- [ ] All figures reference `run023/` or conceptual diagrams
- [ ] No figures from `generated/png/` except fig1, fig3
- [ ] Figure numbering is sequential (1, 2, 3, 4...)
- [ ] Figure captions match content
- [ ] All figures embed correctly (not broken links)

### Statistics Audit

- [ ] Event Horizon = D = 0.80 (NOT 1.23)
- [ ] p-value = 2.40×10⁻²³ (NOT 4.8×10⁻⁵)
- [ ] Settling time τₛ ≈ 9.9-10.2 (NOT 5.2-6.1)
- [ ] PCs for 90% variance = 2 (NOT 43)
- [ ] Methodology = cosine distance (NOT Euclidean)

### Formatting Audit

- [ ] No `<b>` or `</b>` visible in rendered PDF
- [ ] Tables render with proper borders
- [ ] Code blocks have monospace font
- [ ] Greek letters render correctly (or use text equivalents)
- [ ] No broken page breaks mid-table

---

## REGENERATION COMMAND

```bash
cd WHITE-PAPER/submissions
python generate_paper_pdfs.py
```

Output directory: `WHITE-PAPER/reviewers/packages/pdf/`

---

## VERSION HISTORY

| Date | Version | Changes |
|------|---------|---------|
| 2025-12-25 | 1.0 | Initial IRON CLAD spec |

---

*"Verified data only. No hardcoded figures. Cosine methodology throughout."*
