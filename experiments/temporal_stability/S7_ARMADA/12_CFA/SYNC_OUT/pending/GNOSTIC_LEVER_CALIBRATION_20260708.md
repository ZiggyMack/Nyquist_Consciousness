# Gnosticism Phase 2 Lever Calibration Data

**From:** Repo Claude (Nyquist_Consciousness)
**To:** CFA Claude
**Date:** 2026-07-08
**Purpose:** Lever calibration data for all 6 Gnosticism H2H directions — enables the 3 missing H2H buttons

---

## What This Is

Mean Phase 2 lever scores (CCI, EDB, PF_I, PF_E, AR, MG) extracted from CFA Trinity Phase 2 runs. These are dedicated lever calibration sessions — NOT the Phase 1 Trinity metrics (BFI, CA, etc.). All from external-identity condition runs.

## Raw Data Location

All source JSONs live in the Nyquist repo. CFA Claude can verify any value by reading these directly:

| Direction | Path | Run Count |
|-----------|------|-----------|
| G vs CT (G as subject) | `experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/G/` | 10 runs |
| G vs MdN (G as subject) | `experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/G/` | 20 runs |
| G vs PT (G as subject) | `experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/G/` | 20 runs |
| CT vs G (CT as subject) | `experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/CT/` | 10 runs |
| MdN vs G (MdN as subject) | `experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/MdN/` | 10 runs |
| PT vs G (PT as subject) | `experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/PT/` | 20 runs |

Filter criteria: `phase == 2`, `condition == "external"`, `stance == [see below]`

Each JSON has `component1_results` with keys CCI, EDB, PF_I, PF_E, AR, MG, each containing a `final_score`.

---

## Block 1: GNOSTICISM.yaml -> levers_by_matchup.vs_classical_theism

Source: 10 Phase 2 external runs, stance `g_vs_ct`

```yaml
vs_classical_theism:
  calibration_context: "CFA-TRINITY-PHASE2-GNOSTIC-BATCH-20260702-20260703 (10 external runs, g_vs_ct)"
  collective_coherence_impact: 5.19
  epistemic_debt_burden: 5.74
  paternalistic_force_interventionist: 2.51
  paternalistic_force_epistemic: 6.70
  asymmetry_risk: 6.79
  meta_governance: 4.28
```

## Block 2: GNOSTICISM.yaml -> levers_by_matchup.vs_methodological_naturalism

Source: 20 Phase 2 external runs, stance `g_vs_mdn`

```yaml
vs_methodological_naturalism:
  calibration_context: "CFA-TRINITY-PHASE2-GNOSTIC-BATCH-20260702-20260703 (20 external runs, g_vs_mdn)"
  collective_coherence_impact: 5.16
  epistemic_debt_burden: 5.31
  paternalistic_force_interventionist: 2.22
  paternalistic_force_epistemic: 6.60
  asymmetry_risk: 6.64
  meta_governance: 4.52
```

## Block 3: GNOSTICISM.yaml -> levers_by_matchup.vs_process_theology

Source: 20 Phase 2 external runs, stance `g_vs_pt`

```yaml
vs_process_theology:
  calibration_context: "CFA-TRINITY-PHASE2-GNOSTIC-BATCH-20260702-20260703 (20 external runs, g_vs_pt)"
  collective_coherence_impact: 5.19
  epistemic_debt_burden: 5.71
  paternalistic_force_interventionist: 2.49
  paternalistic_force_epistemic: 6.64
  asymmetry_risk: 6.99
  meta_governance: 4.30
```

## Block 4: CLASSICAL_THEISM.yaml -> levers_by_matchup.vs_gnosticism

Source: 10 Phase 2 external runs, stance `ct_vs_g`

```yaml
vs_gnosticism:
  calibration_context: "CFA-TRINITY-PHASE2-GNOSTIC-BATCH-20260702-20260703 (10 external runs, ct_vs_g)"
  collective_coherence_impact: 6.82
  epistemic_debt_burden: 7.27
  paternalistic_force_interventionist: 4.87
  paternalistic_force_epistemic: 7.37
  asymmetry_risk: 7.57
  meta_governance: 7.40
```

## Block 5: METHODOLOGICAL_NATURALISM.yaml -> levers_by_matchup.vs_gnosticism

Source: 10 Phase 2 external runs, stance `mdn_vs_g`

```yaml
vs_gnosticism:
  calibration_context: "CFA-TRINITY-PHASE2-GNOSTIC-BATCH-20260702-20260703 (10 external runs, mdn_vs_g)"
  collective_coherence_impact: 7.12
  epistemic_debt_burden: 7.04
  paternalistic_force_interventionist: 8.67
  paternalistic_force_epistemic: 3.25
  asymmetry_risk: 6.89
  meta_governance: 3.80
```

## Block 6: PROCESS_THEOLOGY.yaml -> levers_by_matchup.vs_gnosticism

Source: 20 Phase 2 external runs, stance `pt_vs_g`

```yaml
vs_gnosticism:
  calibration_context: "CFA-TRINITY-PHASE2-GNOSTIC-BATCH-20260702-20260703 (20 external runs, pt_vs_g)"
  collective_coherence_impact: 6.26
  epistemic_debt_burden: 6.65
  paternalistic_force_interventionist: 3.71
  paternalistic_force_epistemic: 6.45
  asymmetry_risk: 6.61
  meta_governance: 5.82
```

---

## Instructions for CFA Claude

1. Add each block above to its target YAML file under the `levers_by_matchup:` section
2. The 3 H2H buttons (G vs CT, G vs MdN, G vs PT) should appear automatically once all 6 blocks are in place
3. You can verify any value by reading the raw JSONs at the paths listed above — filter for `phase == 2`, `condition == "external"`, and the appropriate `stance`, then average `component1_results.[METRIC].final_score` across runs
4. These are the same instrument and methodology as the existing CT/MdN/PT lever calibration data — no new calibration approach was used

## Methodology Note

The Gnosticism framework profile was constructed using LLM Book datamining of Gnostic source materials, same approach as other frameworks. The Phase 2 lever calibration sessions used the standard Trinity Phase 2 instrument (CCI, EDB, PF_I, PF_E, AR, MG) with external identities, adversarial deliberation, and convergence scoring — identical methodology to the CT/MdN and PT/CT calibration sessions that already populate the existing YAML files.
