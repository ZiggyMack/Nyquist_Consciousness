# Visual Index - Nyquist Consciousness Publication
## UPDATED: December 30, 2025 (Opus 4.5 Review)

**Purpose:** Master index of all visuals for arxiv and workshop submissions
**Methodology:** Run 023 IRON CLAD COSINE (750 experiments, 25 models, 5 providers)
**Status:** Publication-Ready with noted exceptions

---

## Figure Status Summary

| Category | Count | Status |
|----------|-------|--------|
| Run 023 Experimental | 14 | Ready |
| Conceptual Diagrams | 2 | Needs generation |
| Oobleck Suite | 6 | Ready |
| PCA/Dimensional | 8 | Ready |

### Missing Figures Resolution

| Figure | Status | Resolution Path |
|--------|--------|-----------------|
| `fig1_identity_manifold.png` | MISSING | Run `python figures/conceptual/fig1_identity_manifold.py` OR use `3d_attractor_basin.png` |
| `fig3_pipeline.png` | MISSING | Run `python figures/conceptual/fig3_pipeline.py` OR use ASCII from `ascii_framework.md` |

---

## Key Metrics to Primary Visuals

| Metric | Authoritative Value | Primary Visual | Backup Visual |
|--------|---------------------|----------------|---------------|
| **Event Horizon** | D = 0.80 | `phase_portrait.png` | `3d_attractor_basin.png` |
| **Cohen's d** | 0.698 | `cross_model_comparison.png` | `perturbation_validation.png` |
| **Inherent Drift** | ~93% | `oobleck_thermometer.png` | `oobleck_control_treatment.png` |
| **p-value** | 2.40e-23 | `perturbation_validation.png` | - |
| **PCs for 90%** | 2 | `variance_curve.png` | `pc_scatter.png` |
| **Settling Time** | tau_s = 7 | `settling_curves.png` | - |
| **Context Damping** | 97.5% | `context_damping_summary.png` | - |

---

## Source Paths

**S7_ARMADA Visualizations:**
```
experiments/temporal_stability/S7_ARMADA/visualizations/pics/
├── 1_Vortex/               # Identity vortex spirals
├── 2_Boundary_Mapping/     # Phase portraits, 3D basins (D=0.80)
├── 3_Stability/            # Stability analysis, pillar comparison
├── 5_Settling/             # Settling curves (tau_s = 7)
├── 6_Architecture/         # Provider comparison (5 providers)
├── 8_Radar_Oscilloscope/   # Radar fingerprints
├── 10_PFI_Dimensional/     # PCA validation (d=0.698, p=2.40e-23)
├── 12_Metrics_Summary/     # Context damping, network diagrams
├── 13_Model_Waveforms/     # Per-model waveforms
├── 14_Ringback/            # Ringback oscillation
├── 15_Oobleck_Effect/      # ~93% inherent drift finding (Run 020B IRON CLAD)
└── run020/                 # Control vs Treatment (source of ~93%)
```

---

## Section 1: Workshop Figures (4-8 pages)

**Requirement:** 3-5 high-impact figures for focused claims

### Recommended Workshop Figure Set

| Priority | Visual | Claim | Shows | File |
|----------|--------|-------|-------|------|
| **1** | Thermometer | E | ~93% inherent drift | `oobleck_thermometer.png` |
| **2** | Control vs Treatment | E | Bar comparison | `oobleck_control_treatment.png` |
| **3** | Context Damping | D | 97.5% stability | `context_damping_summary.png` |
| 4 | Cross-Model | A | d=0.698 effect | `cross_model_comparison.png` |
| 5 | Phase Portrait | B | D=0.80 threshold | `phase_portrait.png` |

**Workshop Priority:** Figures 1-3 are essential; 4-5 if space permits.

---

## Section 2: arXiv Figures (25-35 pages)

**Requirement:** Complete visual evidence package

### Main Content Figures (8)

| # | Visual | Claim | Key Metric | Source |
|---|--------|-------|------------|--------|
| 1 | Identity Manifold | Conceptual | - | `fig1_identity_manifold.png` (MISSING) |
| 2 | Experimental Pipeline | Conceptual | - | `fig3_pipeline.png` (MISSING) |
| 3 | Provider Clusters | A | PC space | `provider_clusters.png` |
| 4 | Context Damping | D | 97.5% | `context_damping_summary.png` |
| 5 | Thermometer | E | ~93% | `oobleck_thermometer.png` |
| 6 | Control vs Treatment | E | Bars | `oobleck_control_treatment.png` |
| 7 | Provider Comparison | Cross-arch | 5 providers | `provider_comparison.png` |
| 8 | Combined Dashboard | Summary | All metrics | `combined_provider_dashboard.png` |

### Appendix Figures (10+)

| # | Visual | Shows | Source |
|---|--------|-------|--------|
| F1 | Vortex Identity Drain | Phase space trajectories | `vortex_identity_drain.png` |
| F2 | Phase Portrait | D=0.80 threshold | `phase_portrait.png` |
| F3 | Stability Basin | Stable vs volatile | `stability_basin.png` |
| F4 | Provider Fingerprint Radar | 5-D signatures | `provider_fingerprint_radar.png` |
| F5 | 3D Attractor Basin | Basin geometry | `3d_attractor_basin.png` |
| F6 | Perturbation Validation | p=2.40e-23 | `perturbation_validation.png` |
| F7 | Variance Curve | 2 PCs = 90% | `variance_curve.png` |
| F8 | PC Scatter | PC1 vs PC2 | `pc_scatter.png` |
| F9 | Settling Curves | tau_s = 7 | `settling_curves.png` |
| F10 | Model Waveforms | Per-model patterns | `model_waveforms/*.png` |

---

## Section 3: Claims-to-Visuals Matrix

| Claim | Statement | Primary Visual | Backup | Required For |
|-------|-----------|----------------|--------|--------------|
| **A** | PFI is valid (rho=0.91, d=0.698) | `cross_model_comparison.png` | `perturbation_validation.png` | arXiv, Workshop |
| **B** | Regime threshold D=0.80 | `phase_portrait.png` | `3d_attractor_basin.png` | arXiv |
| **C** | Damped oscillator (tau_s=7) | `settling_curves.png` | `waterfall_settling_fleet.png` | arXiv |
| **D** | Context damping (97.5%) | `context_damping_summary.png` | - | Both |
| **E** | ~93% inherent drift | `oobleck_thermometer.png` | `oobleck_control_treatment.png` | Both |

---

## Section 4: Complete Oobleck Visual Suite

**Source:** `15_Oobleck_Effect/` (Run 020B IRON CLAD COSINE)
**Status:** All figures ready

| Visual | Size | Purpose | Use In |
|--------|------|---------|--------|
| `oobleck_thermometer.png` | 126 KB | **Primary ~93% finding** | Workshop Fig 1, arXiv Fig 5 |
| `oobleck_control_treatment.png` | 219 KB | Control vs Treatment bars | Workshop Fig 2, arXiv Fig 6 |
| `oobleck_phase_breakdown.png` | 194 KB | Phase-by-phase analysis | arXiv appendix |
| `oobleck_per_model_breakdown.png` | 270 KB | Per-model breakdown | arXiv appendix |
| `oobleck_cross_platform.png` | 201 KB | Cross-platform comparison | arXiv appendix |
| `oobleck_trajectory_overlay.png` | 246 KB | Trajectory overlay | arXiv appendix |

---

## Section 5: PFI Dimensional Suite (d=0.698 Evidence)

**Source:** `10_PFI_Dimensional/`
**Status:** All figures ready

### Phase 2: PCA Validation (2 PCs = 90%)

| Visual | Purpose | Key Finding |
|--------|---------|-------------|
| `variance_curve.png` | Explained variance | **2 PCs = 90%** |
| `pc_scatter.png` | PC1 vs PC2 scatter | Provider clustering |
| `provider_clusters.png` | Provider separation | Distinct geometries |
| `event_horizon_contour.png` | EH in PC space | D=0.80 contour |

### Phase 3A: Synthetic Perturbation (p=2.40e-23)

| Visual | Purpose | Key Finding |
|--------|---------|-------------|
| `perturbation_comparison.png` | **p-value validation** | **p=2.40e-23** |
| `eh_crossings.png` | EH crossing analysis | Threshold behavior |
| `ship_comparison.png` | Ship-level comparison | Model variability |

### Phase 3B: Cross-Model (d=0.698)

| Visual | Purpose | Key Finding |
|--------|---------|-------------|
| `cross_model_comparison.png` | **Effect size main figure** | **d=0.698** |
| `cross_model_histogram.png` | Distribution | Normal-ish |
| `provider_matrix.png` | Provider discrimination | Separability |

---

## Section 6: Summary PDF Menu (Reviewer Package)

**Location:** `reviewers/packages/v5/visualization_pdfs/` (16 PDFs)

| PDF | Key Visuals | Primary Claim |
|-----|-------------|---------------|
| `1_Vortex_Summary.pdf` | Identity vortex | Visual intro |
| `2_Boundary_Mapping_Summary.pdf` | Phase portrait, 3D basin | B |
| `3_Stability_Summary.pdf` | Stability analysis | C |
| `4_Rescue_Summary.pdf` | Recovery dynamics | C |
| `5_Settling_Summary.pdf` | Settling curves | C |
| `6_Architecture_Summary.pdf` | Provider comparison | Cross-arch |
| `8_Radar_Oscilloscope_Summary.pdf` | Radar fingerprints | Cross-arch |
| `9_FFT_Spectral_Summary.pdf` | Spectral analysis | C |
| `10_PFI_Dimensional_Summary.pdf` | PCA, perturbation | A, B |
| `11_Unified_Dashboard_Summary.pdf` | Combined dashboard | All |
| `12_Metrics_Summary.pdf` | Context damping | D |
| `13_Model_Waveforms_Summary.pdf` | Per-model patterns | C |
| `14_Ringback_Summary.pdf` | Oscillation | C |
| `15_Oobleck_Effect_Summary.pdf` | ~93% finding | **E** |
| `16_Laplace_Analysis_Summary.pdf` | Laplace domain | C |
| `run018_Summary.pdf` | IRON CLAD damping | D |
| `run020_Summary.pdf` | IRON CLAD inherent | E |

---

## Section 7: Final Paper to Figure Map

### arXiv Paper: `NYQUIST_ARXIV_PAPER_FINAL.md`

| Figure # | Caption | Source File | Status |
|----------|---------|-------------|--------|
| 1 | Identity Manifold | `fig1_identity_manifold.png` | MISSING - Generate |
| 2 | Experimental Pipeline | `fig3_pipeline.png` | MISSING - Generate |
| 3 | Provider Identity Clusters | `provider_clusters.png` | Ready |
| 4 | Context Damping Effect | `context_damping_summary.png` | Ready |
| 5 | The Thermometer Result | `oobleck_thermometer.png` | Ready |
| - | Combined Provider Analysis | `combined_provider_dashboard.png` | Ready |
| 6 | Oobleck Effect | `oobleck_control_treatment.png` | Ready |
| - | Provider Comparison | `provider_comparison.png` | Ready |
| F1-F6 | Appendix | Various | Ready |

### Workshop Paper: `Nyquist_workshop_paper_FINAL.md`

| Figure # | Caption | Source File | Status |
|----------|---------|-------------|--------|
| 1 | Context Damping Effect | `context_damping_summary.png` | Ready |
| 2 | The Thermometer Result | `oobleck_thermometer.png` | Ready |
| 3 | Oobleck Effect | `oobleck_control_treatment.png` | Ready |

### Journal Paper: `JOURNAL_PAPER_FINAL.md`

| Figure # | Caption | Source File | Status |
|----------|---------|-------------|--------|
| 1 | Identity Manifold | `fig1_identity_manifold.png` | MISSING - Generate |
| 2 | Context Damping | `context_damping_summary.png` | Ready |
| 3 | Thermometer | `oobleck_thermometer.png` | Ready |
| 4 | Oobleck Effect | `oobleck_control_treatment.png` | Ready |
| 5 | Pipeline | `fig3_pipeline.png` | MISSING - Generate |
| 6 | Cross-Provider | `combined_provider_dashboard.png` | Ready |

---

## Section 8: Figure Generation Commands

For missing conceptual figures:

```bash
# Generate Identity Manifold (Figure 1)
cd figures/conceptual/
python fig1_identity_manifold.py
# Output: pics/fig1_identity_manifold_CONCEPTUAL.png

# Generate Pipeline (Figure 2/5)
python fig3_pipeline.py
# Output: pics/fig3_pipeline_CONCEPTUAL.png
```

**Alternative (if Python fails):**

Use ASCII diagrams from `figures/ascii/`:
- `ascii_framework.md` - Pipeline figure
- Embed as code block or convert to image

---

## Section 9: Deprecated Visuals (DO NOT USE)

| Visual | Reason | Era |
|--------|--------|-----|
| Any with "D=1.23" | Keyword RMS threshold | Pre-Cosine |
| Any with "43 PCs" | Euclidean methodology | Pre-Cosine |
| Any with "d=0.98" | Experiment-level, not model-level | Pre-IRON CLAD |
| Any from Run 001-008 | Discovery era, not validated | Pre-Control |

---

## Section 10: High-Impact Unused Visualizations

**From Opus 4.5 Visualization Audit:** We have 120+ figures but only use ~8-10.

### Top 10 Recommended Additions

| # | Visualization | Location | Best For | Shows |
|---|--------------|----------|----------|-------|
| 1 | 2 PC Variance Curve | `10_PFI/` | ALL papers (Claim A) | 2 PCs = 90% variance |
| 2 | Provider Radar Fingerprints | `8_Radar/` | ALL papers | 5-D provider signatures |
| 3 | Oobleck Decomposition | `15_Oobleck/` | ALL papers | Rate-dependent resistance |
| 4 | Quartz Validation r=0.927 | `16_Laplace/` | Methodology | Cross-embedding validation |
| 5 | Provider Identity Manifolds | `5_Settling/` | Journal cover | 3D provider landscapes |
| 6 | Recovery Heatmap | `4_Rescue/` | arXiv Claim C | Model-by-model recovery |
| 7 | Phase Portrait | `2_Boundary/` | arXiv Methodology | D=0.80 basin structure |
| 8 | FFT Spectral Signatures | `9_FFT/` | Journal | Frequency-domain analysis |
| 9 | Full 19,500-point Manifold | `1_Vortex/` | Cover/Flagship | Complete identity space |
| 10 | Per-Model Drift Heatmap | `20_Run/` | ALL Claim E | Model variability |

### Recommended Paper Additions

**For arXiv (space available):**
- Add `variance_curve.png` to Section 4 (Claim A evidence)
- Add `provider_fingerprint_radar.png` to Section 5 (Architecture)
- Add `recovery_heatmap.png` to Appendix

**For Workshop (if 5th figure allowed):**
- Add `provider_fingerprint_radar.png` (striking visual)

**For Journal (comprehensive):**
- Use `provider_identity_manifolds.png` for cover image
- Add full FFT spectral suite to supplementary

---

## Validation Checklist

Before submission, verify:

- [ ] All figure paths resolve
- [ ] No D=1.23 references in main figures
- [ ] Thermometer shows ~93% (not 82%)
- [ ] Event Horizon labeled D=0.80
- [ ] Provider count = 5 (not 6)
- [ ] Model count = 25 (IRON CLAD)
- [ ] Experiment count = 750 (Run 023d)
- [ ] Missing figures generated or substituted

---

*Run 023 IRON CLAD: 750 experiments, 25 models, 5 providers*
*Run 020B IRON CLAD: 248 sessions, 37 ships, ~93% inherent drift*
*Cosine Methodology: Event Horizon D=0.80, Cohen's d=0.698, p=2.40e-23*

**Last Updated:** December 30, 2025 (Opus 4.5 Review - v5 Release)
