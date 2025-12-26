# Visual-to-Pipeline Matrix

**Generated:** 2025-12-26
**Purpose:** At-a-glance view of which visuals are used in each publication pipeline
**Methodology:** Run 023 IRON CLAD COSINE

---

## Master Matrix: Visuals x Pipelines

| Visual | Claim | Workshop | arXiv | Journal | PopSci | Education | Policy | Funding | Media |
|--------|-------|:--------:|:-----:|:-------:|:------:|:---------:|:------:|:-------:|:-----:|
| **PRIMARY FIGURES** |
| `oobleck_thermometer.png` | E | **X** | **X** | **X** | X | X | X | X | X |
| `oobleck_control_treatment.png` | E | **X** | **X** | **X** | - | - | X | X | - |
| `cross_model_comparison.png` | A | **X** | **X** | **X** | - | - | - | X | - |
| `perturbation_comparison.png` | A | - | **X** | **X** | - | - | - | X | - |
| `run023b_phase_portrait.png` | B | X | **X** | **X** | - | - | - | X | - |
| `settling_curves.png` | C | **X** | **X** | **X** | - | - | - | X | - |
| `context_damping_summary.png` | D | - | **X** | **X** | - | - | X | X | - |
| `provider_comparison.png` | - | - | **X** | **X** | - | - | - | X | - |
| **APPENDIX/SUPPLEMENTARY** |
| `variance_curve.png` | A | - | A | **X** | - | X | - | X | - |
| `pc_scatter.png` | A | - | A | **X** | - | - | - | - | - |
| `provider_clusters.png` | A | - | A | **X** | - | - | - | - | - |
| `provider_matrix.png` | A | - | A | **X** | - | - | - | - | - |
| `run023b_3d_basin.png` | B | - | A | **X** | - | - | - | - | - |
| `run023b_stability_basin.png` | B | - | A | **X** | - | - | - | - | - |
| `run023_vortex.png` | - | - | A | **X** | X | - | - | - | X |
| `run023_vortex_x4.png` | - | - | A | **X** | - | - | - | - | - |
| `oobleck_phase_breakdown.png` | E | - | A | **X** | - | - | - | - | - |
| `oobleck_per_model_breakdown.png` | E | - | A | **X** | - | - | - | - | - |
| `oobleck_cross_platform.png` | E | - | A | **X** | - | - | - | - | - |
| `oobleck_trajectory_overlay.png` | E | - | A | **X** | - | - | - | - | - |

**Legend:**
- **X** = Primary figure (main content)
- A = Appendix/Supplementary
- X = Recommended for this audience
- `-` = Not included

---

## Pipeline Summary

| Pipeline | Target | Primary Figs | Appendix Figs | Total | Focus |
|----------|--------|:------------:|:-------------:|:-----:|-------|
| **Workshop** | NeurIPS/AAAI | 5 | 0 | 5 | Claims A,B,C,E only |
| **arXiv** | cs.AI preprint | 8 | 12 | 20 | Complete evidence |
| **Journal** | Nature MI | 8 | 12 | 20 | Comprehensive |
| **PopSci** | Atlantic/Wired | 2 | 0 | 2 | Thermometer + Vortex |
| **Education** | OER/Coursera | 2 | 0 | 2 | Visual learners |
| **Policy** | Think tanks | 3 | 0 | 3 | Key findings only |
| **Funding** | NSF/DARPA | 8 | 0 | 8 | All claims |
| **Media** | Press/TED | 2 | 0 | 2 | Eye-catching |

---

## By Claim: Which Visuals Support Each

### Claim A: PFI Validity (rho=0.91, d=0.698)

| Visual | Type | Pipelines |
|--------|------|-----------|
| `cross_model_comparison.png` | **Primary** | Workshop, arXiv, Journal, Funding |
| `perturbation_comparison.png` | **Primary** | arXiv, Journal, Funding |
| `variance_curve.png` | Supporting | arXiv(A), Journal, Education, Funding |
| `pc_scatter.png` | Supporting | arXiv(A), Journal |
| `provider_clusters.png` | Supporting | arXiv(A), Journal |
| `provider_matrix.png` | Supporting | arXiv(A), Journal |

### Claim B: Regime Threshold (D=0.80)

| Visual | Type | Pipelines |
|--------|------|-----------|
| `run023b_phase_portrait.png` | **Primary** | Workshop, arXiv, Journal, Funding |
| `run023b_3d_basin.png` | Supporting | arXiv(A), Journal |
| `run023b_stability_basin.png` | Supporting | arXiv(A), Journal |

### Claim C: Damped Oscillator (tau_s=10.2)

| Visual | Type | Pipelines |
|--------|------|-----------|
| `settling_curves.png` | **Primary** | Workshop, arXiv, Journal, Funding |

### Claim D: Context Damping (97.5%)

| Visual | Type | Pipelines |
|--------|------|-----------|
| `context_damping_summary.png` | **Primary** | arXiv, Journal, Policy, Funding |

### Claim E: 92% Inherent Drift (Thermometer)

| Visual | Type | Pipelines |
|--------|------|-----------|
| `oobleck_thermometer.png` | **PRIMARY** | ALL 8 PIPELINES |
| `oobleck_control_treatment.png` | **Primary** | Workshop, arXiv, Journal, Policy, Funding |
| `oobleck_phase_breakdown.png` | Supporting | arXiv(A), Journal |
| `oobleck_per_model_breakdown.png` | Supporting | arXiv(A), Journal |
| `oobleck_cross_platform.png` | Supporting | arXiv(A), Journal |
| `oobleck_trajectory_overlay.png` | Supporting | arXiv(A), Journal |

---

## Visual Coverage Gaps Analysis

### Well-Covered (All 5 Claims Have Visuals)

| Claim | Status | Notes |
|-------|--------|-------|
| A (PFI) | COMPLETE | 6 visuals, strong evidence |
| B (D=0.80) | COMPLETE | 3 visuals including 3D |
| C (tau_s) | ADEQUATE | 1 visual (could add more) |
| D (Context) | ADEQUATE | 1 visual (could add more) |
| E (92%) | EXCELLENT | 6 visuals, comprehensive |

### Potential Gaps to Consider

| Gap | Description | Recommendation |
|-----|-------------|----------------|
| Claim C depth | Only 1 settling visual | Consider adding per-provider settling |
| Claim D depth | Only 1 context damping visual | Consider before/after comparison |
| Cross-provider | `provider_comparison.png` only | Strong enough for now |
| PopSci visuals | Only thermometer + vortex | Could add simplified infographic |
| Media visuals | Only 2 eye-catchers | Consider animated GIF for web |

---

## Source Locations Quick Reference

```
experiments/temporal_stability/S7_ARMADA/visualizations/pics/
├── 1_Vortex/                    # run023_vortex*.png
├── 2_Boundary_Mapping/          # run023b_phase_portrait.png, *_3d_basin.png
├── 3_Stability/                 # run023b_stability_basin.png
├── 5_Settling/                  # settling_curves.png
├── 6_Architecture/              # provider_comparison.png
├── 10_PFI_Dimensional/
│   ├── phase2_pca/             # variance_curve, pc_scatter, provider_clusters
│   ├── phase3a_synthetic/      # perturbation_comparison.png
│   └── phase3b_crossmodel/     # cross_model_comparison.png, provider_matrix
├── 12_Metrics_Summary/          # context_damping_summary.png
└── 15_Oobleck_Effect/           # oobleck_*.png (6 files)
```

---

## Recommended Visual Review Checklist

For Opus 4.5 / Reviewer validation:

- [ ] **Thermometer (E):** Is 92% prominently displayed? Clear labeling?
- [ ] **Cross-model (A):** Is d=0.698 clearly shown? Provider breakdown visible?
- [ ] **Phase Portrait (B):** Is D=0.80 threshold marked? Clean visualization?
- [ ] **Settling (C):** Is tau_s=10.2 labeled? Multiple providers shown?
- [ ] **Context Damping (D):** Is 97.5% improvement clear?
- [ ] **All Oobleck suite:** Consistent styling? Same color scheme?
- [ ] **Provider comparison:** All 5 providers represented?

---

*Run 023 IRON CLAD: 750 experiments, 25 models, 5 providers*
*Cosine Methodology: D=0.80, d=0.698, 92% inherent, p=2.40e-23*
