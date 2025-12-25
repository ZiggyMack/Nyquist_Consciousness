# DEPRECATED Figures

**DO NOT USE THESE FIGURES IN PUBLICATIONS**

These figures contain **hardcoded synthetic data** that predates actual experimental validation from S7 ARMADA runs.

---

## Why These Are Deprecated

| Figure | Issue |
|--------|-------|
| `_DEPRECATED_fig2_drift_field` | Uses D=1.23 (Euclidean) instead of D=0.80 (cosine). Hardcoded drift values. |
| `_DEPRECATED_fig5_omega_convergence` | Hardcoded drift values (0.65-0.95). Claims unvalidated "45% reduction". |
| `_DEPRECATED_fig6_82_percent` | Hardcoded peak_drift=[1.172, 2.161], final_drift=[0.399, 0.489]. |
| `_DEPRECATED_fig7_context_damping` | Shows settling time 5.2-6.1 (WRONG - actual is 9.9-10.2). |
| `_DEPRECATED_fig8_oobleck` | Synthetic intensity/drift curve, not from experimental data. |
| `_DEPRECATED_fig_workshop_combined` | All 4 panels use hardcoded fake data. Claims "43 PCs" (wrong - should be 2). |

---

## Correct Values (IRON CLAD - Run 023d)

| Metric | Wrong Value (in deprecated) | Correct Value |
|--------|----------------------------|---------------|
| Event Horizon | D = 1.23 | D = 0.80 |
| Settling Time | 5.2-6.1 probes | 9.9-10.2 probes |
| 90% Variance PCs | 43 | **2** |
| Cohen's d | 0.98 | 0.698 |
| p-value | 4.8x10^-5 | 2.40x10^-23 |

---

## Use These Instead

All verified visualizations are in `figures/run023/` and come from:
- `S7_ARMADA/visualizations/pics/`
- Run 023d/023e IRON CLAD validation

Key replacements:
| Deprecated | Verified Replacement |
|------------|---------------------|
| fig6 (82%) | `run023/oobleck_thermometer.png` |
| fig7 (context damping) | `run023/context_damping_summary.png` |
| fig8 (oobleck) | `run023/oobleck_control_treatment.png` |
| fig2 (drift field) | `run023/provider_clusters.png` |

---

**Archived:** December 25, 2025
**Reason:** IRON CLAD audit revealed hardcoded synthetic data
