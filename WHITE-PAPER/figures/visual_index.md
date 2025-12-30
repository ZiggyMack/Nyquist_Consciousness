# Visual Index - Nyquist Consciousness Publication

**Last Updated:** 2025-12-30
**Purpose:** Master index of all visuals for arxiv and workshop submissions
**Methodology:** Run 023 IRON CLAD COSINE (750 experiments, 25 models, 5 providers)

---

## Key Metrics to Visualize

| Metric | Value | Primary Visual |
|--------|-------|----------------|
| **Event Horizon** | D = 0.80 | `phase_portrait.png`, `3d_basin.png` |
| **Cohen's d** | 0.698 | `cross_model_comparison.png` |
| **Inherent Drift** | ~93% | `oobleck_thermometer.png` |
| **p-value** | 2.40e-23 | `perturbation_comparison.png` |
| **PCs for 90%** | 2 | `variance_curve.png` |
| **Settling Time** | τₛ ≈ 7 | `settling_curves.png` |

---

## Source Paths

**S7_ARMADA Visualizations:**
```
experiments/temporal_stability/S7_ARMADA/visualizations/pics/
├── 1_Vortex/           # Identity vortex spirals
├── 2_Boundary_Mapping/ # Phase portraits, 3D basins (D=0.80)
├── 3_Stability/        # Stability analysis, pillar comparison
├── 5_Settling/         # Settling curves (τₛ ≈ 7)
├── 6_Architecture/     # Provider comparison (5 providers)
├── 8_Radar_Oscilloscope/ # Radar fingerprints
├── 10_PFI_Dimensional/ # PCA validation (d=0.698, p=2.40e-23)
├── 12_Metrics_Summary/ # Context damping, network diagrams
├── 13_Model_Waveforms/ # Per-model waveforms
├── 14_Ringback/        # Ringback oscillation
├── 15_Oobleck_Effect/  # ~93% inherent drift finding (Run 020B IRON CLAD)
└── run020/             # Control vs Treatment (source of ~93%)
```

---

## Section 1: Workshop Figures (4-8 pages)

**Requirement:** 3-5 high-impact figures for focused claims

### Recommended Workshop Figures

| # | Visual | Source Path | Shows | Claim |
|---|--------|-------------|-------|-------|
| 1 | `oobleck_thermometer.png` | `15_Oobleck_Effect/` | **~93% inherent drift pie chart** | E |
| 2 | `oobleck_control_treatment.png` | `15_Oobleck_Effect/` | Control vs Treatment bars | E |
| 3 | `cross_model_comparison.png` | `10_PFI_Dimensional/phase3b_crossmodel/` | **d=0.698 cross-provider effect** | A |
| 4 | `settling_curves.png` | `5_Settling/` | Settling time τₛ ≈ 7 | C |
| 5 | `run023b_phase_portrait.png` | `2_Boundary_Mapping/` | Phase portrait with D=0.80 | B |

**Workshop Visual Summary:**
- Fig 1: The ~93% Thermometer (headline finding)
- Fig 2: Control vs Treatment comparison
- Fig 3: Cross-model d=0.698 validation
- Fig 4: Settling dynamics
- Fig 5: Phase portrait (optional, space permitting)

---

## Section 2: arXiv Figures (25-35 pages)

**Requirement:** Complete visual evidence package

### Main Content (6-8 figures)

| # | Visual | Source Path | Shows | Claim |
|---|--------|-------------|-------|-------|
| 1 | `oobleck_thermometer.png` | `15_Oobleck_Effect/` | **~93% inherent drift** | E |
| 2 | `oobleck_control_treatment.png` | `15_Oobleck_Effect/` | Control vs Treatment | E |
| 3 | `cross_model_comparison.png` | `10_PFI_Dimensional/phase3b_crossmodel/` | **d=0.698** | A |
| 4 | `perturbation_comparison.png` | `10_PFI_Dimensional/phase3a_synthetic/` | **p=2.40e-23** | A |
| 5 | `run023b_phase_portrait.png` | `2_Boundary_Mapping/` | Phase portrait, **D=0.80** | B |
| 6 | `settling_curves.png` | `5_Settling/` | **τₛ ≈ 7 probes** | C |
| 7 | `context_damping_summary.png` | `12_Metrics_Summary/` | **97.5% stability** | D |
| 8 | `provider_comparison.png` | `6_Architecture/` | 5-provider comparison | Cross-arch |

### Appendix / Supplementary (8-12 figures)

| # | Visual | Source Path | Shows |
|---|--------|-------------|-------|
| A1 | `variance_curve.png` | `10_PFI_Dimensional/phase2_pca/` | **2 PCs = 90% variance** |
| A2 | `pc_scatter.png` | `10_PFI_Dimensional/phase2_pca/` | PC1 vs PC2 scatter |
| A3 | `provider_clusters.png` | `10_PFI_Dimensional/phase2_pca/` | Provider clustering |
| A4 | `provider_matrix.png` | `10_PFI_Dimensional/phase3b_crossmodel/` | Provider discrimination matrix |
| A5 | `run023b_3d_basin.png` | `2_Boundary_Mapping/` | 3D attractor basin |
| A6 | `run023b_stability_basin.png` | `3_Stability/` | Stability basin analysis |
| A7 | `run023_vortex.png` | `1_Vortex/` | Identity vortex (all providers) |
| A8 | `run023_vortex_x4.png` | `1_Vortex/` | Vortex 4-panel grid |
| A9 | `oobleck_phase_breakdown.png` | `15_Oobleck_Effect/` | Phase-by-phase breakdown |
| A10 | `oobleck_per_model_breakdown.png` | `15_Oobleck_Effect/` | Per-model breakdown |
| A11 | `oobleck_cross_platform.png` | `15_Oobleck_Effect/` | Cross-platform comparison |
| A12 | `oobleck_trajectory_overlay.png` | `15_Oobleck_Effect/` | Trajectory overlay |

---

## Section 3: Complete Oobleck Visual Suite

**Source:** `15_Oobleck_Effect/` (Run 020B IRON CLAD COSINE)

| Visual | Size | Purpose | Recommended For |
|--------|------|---------|-----------------|
| `oobleck_thermometer.png` | 126 KB | **Primary ~93% finding** | Workshop, arXiv main |
| `oobleck_control_treatment.png` | 219 KB | Control vs Treatment bars | Workshop, arXiv main |
| `oobleck_phase_breakdown.png` | 194 KB | Phase-by-phase analysis | arXiv appendix |
| `oobleck_per_model_breakdown.png` | 270 KB | Per-model breakdown | arXiv appendix |
| `oobleck_cross_platform.png` | 201 KB | Cross-platform comparison | arXiv appendix |
| `oobleck_trajectory_overlay.png` | 246 KB | Trajectory overlay | arXiv appendix |

---

## Section 4: PFI Dimensional Suite (d=0.698 Evidence)

**Source:** `10_PFI_Dimensional/`

### Phase 2: PCA Validation

| Visual | Purpose |
|--------|---------|
| `phase2_pca/variance_curve.png` | 2 PCs capture 90% variance |
| `phase2_pca/pc_scatter.png` | PC1 vs PC2 scatter |
| `phase2_pca/provider_clusters.png` | Provider clustering in PC space |
| `phase2_pca/event_horizon_contour.png` | EH contour in PC space |

### Phase 3A: Synthetic Perturbation (p=2.40e-23)

| Visual | Purpose |
|--------|---------|
| `phase3a_synthetic/perturbation_comparison.png` | **p=2.40e-23 validation** |
| `phase3a_synthetic/eh_crossings.png` | EH crossing analysis |
| `phase3a_synthetic/ship_comparison.png` | Ship-level comparison |

### Phase 3B: Cross-Model (d=0.698)

| Visual | Purpose |
|--------|---------|
| `phase3b_crossmodel/cross_model_comparison.png` | **d=0.698 main figure** |
| `phase3b_crossmodel/cross_model_histogram.png` | Distribution histogram |
| `phase3b_crossmodel/provider_matrix.png` | Provider discrimination |

---

## Section 5: Summary PDF Menu (for Reviewers)

**Location:** `reviewers/packages/v3/visualization_pdfs/`

| PDF | Key Visuals |
|-----|-------------|
| `10_PFI_Dimensional_Summary.pdf` | variance_curve, perturbation_comparison, cross_model_comparison |
| `15_Oobleck_Effect_Summary.pdf` | oobleck_thermometer, oobleck_control_treatment, full suite |
| `2_Boundary_Mapping_Summary.pdf` | phase_portrait, 3d_basin |
| `5_Settling_Summary.pdf` | settling_curves |
| `6_Architecture_Summary.pdf` | provider_comparison |
| `12_Metrics_Summary.pdf` | context_damping_summary |

---

## Section 6: Claims-to-Visuals Matrix

| Claim | Statement | Primary Visual | Backup Visual |
|-------|-----------|----------------|---------------|
| **A** | PFI is valid (ρ=0.91, d=0.698) | `cross_model_comparison.png` | `perturbation_comparison.png` |
| **B** | Regime threshold D=0.80 | `run023b_phase_portrait.png` | `run023b_3d_basin.png` |
| **C** | Damped oscillator (τₛ≈7) | `settling_curves.png` | `waterfall_settling_fleet.png` |
| **D** | Context damping (97.5%) | `context_damping_summary.png` | - |
| **E** | ~93% inherent drift | `oobleck_thermometer.png` | `oobleck_control_treatment.png` |

---

## Section 7: Final Paper → Figure Map (PDF Generation)

**Purpose:** Maps each final submission markdown file to the exact figures embedded within.

### arXiv Paper: `NYQUIST_ARXIV_PAPER_FINAL.md` (17 figures)

| Figure # | Caption | Source File | Path |
|----------|---------|-------------|------|
| 1 | Identity Manifold | `fig1_identity_manifold.png` | `../figures/generated/png/` |
| 2 | Experimental Pipeline | `fig3_pipeline.png` | `../figures/generated/png/` |
| 3 | Provider Identity Clusters | `provider_clusters.png` | `../figures/experiments/run023/` |
| 4 | Context Damping Effect | `context_damping_summary.png` | `../figures/experiments/run023/` |
| 5 | The Thermometer Result | `oobleck_thermometer.png` | `../figures/experiments/run023/` |
| - | Combined Provider Analysis | `combined_provider_dashboard.png` | `../figures/experiments/run023/` |
| 6 | Oobleck Effect - Control vs Treatment | `oobleck_control_treatment.png` | `../figures/experiments/run023/` |
| - | Provider Comparison | `provider_comparison.png` | `../figures/experiments/run023/` |
| App | Vortex: Identity Drain | `vortex_identity_drain.png` | `../figures/experiments/run023/` |
| App | Phase Portrait | `phase_portrait.png` | `../figures/experiments/run023/` |
| App | Stability Basin | `stability_basin.png` | `../figures/experiments/run023/` |
| App | Provider Fingerprint Radar | `provider_fingerprint_radar.png` | `../figures/experiments/run023/` |
| App | 3D Attractor Basin | `3d_attractor_basin.png` | `../figures/experiments/run023/` |
| App | Perturbation Validation | `perturbation_validation.png` | `../figures/experiments/run023/` |

### Journal/White Paper: `NYQUIST_WHITE_PAPER_FINAL.md` (10 figures)

| Figure # | Caption | Source File | Path |
|----------|---------|-------------|------|
| 1 | Identity Manifold | `fig1_identity_manifold.png` | `../figures/generated/png/` |
| - | Event Horizon Validation | `perturbation_validation.png` | `../figures/experiments/run023/` |
| 2 | Context Damping Effect | `context_damping_summary.png` | `../figures/experiments/run023/` |
| 3 | The Thermometer Result | `oobleck_thermometer.png` | `../figures/experiments/run023/` |
| - | Cross-Platform Provider Analysis | `combined_provider_dashboard.png` | `../figures/experiments/run023/` |
| 4 | Oobleck Effect - Control vs Treatment | `oobleck_control_treatment.png` | `../figures/experiments/run023/` |
| - | Training Architecture Signatures | `provider_comparison.png` | `../figures/experiments/run023/` |
| 5 | Experimental Pipeline | `fig3_pipeline.png` | `../figures/generated/png/` |
| 6 | Cross-Provider Comparison | `combined_provider_dashboard.png` | `../figures/experiments/run023/` |

### Workshop Paper: `Nyquist_workshop_paper_FINAL.md` (3 figures)

| Figure # | Caption | Source File | Path |
|----------|---------|-------------|------|
| 1 | Context Damping Effect | `context_damping_summary.png` | `../figures/experiments/run023/` |
| 2 | The Thermometer Result | `oobleck_thermometer.png` | `../figures/experiments/run023/` |
| 3 | Oobleck Effect - Control vs Treatment | `oobleck_control_treatment.png` | `../figures/experiments/run023/` |

### Figure Source Summary

| Source Directory | # Used | Notes |
|-----------------|--------|-------|
| `../figures/generated/png/` | 2 | Conceptual diagrams (manifold, pipeline) |
| `../figures/experiments/run023/` | 12 | Run 023 IRON CLAD experimental data |

**Missing Figures (from PDF generation warnings):**

- `fig1_identity_manifold.png` - Conceptual diagram, needs generation
- `fig3_pipeline.png` - Pipeline schematic, needs generation

---

## Notes

- All visuals are from Run 023 IRON CLAD unless noted
- SVG versions available for all PNGs (vector format)
- D=1.23 visuals are deprecated (Keyword RMS era)
- Folder 7 (interactive) contains HTML only - not for publication
- Run 018/020B PDFs preserved as IRON CLAD reference

---

*Run 023 IRON CLAD: 750 experiments, 25 models, 5 providers*
*Run 020B IRON CLAD: 248 sessions, 37 ships, ~93% inherent drift*
*Cosine Methodology: Event Horizon D=0.80, Cohen's d=0.698, p=2.40e-23*
