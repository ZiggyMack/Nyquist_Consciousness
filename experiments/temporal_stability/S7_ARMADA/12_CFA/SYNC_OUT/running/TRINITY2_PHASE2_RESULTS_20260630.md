<!---
FILE: TRINITY2_PHASE2_RESULTS_20260630.md
PURPOSE: Trinity Phase 2 — YPA lever calibration across 4 conditions (CT/MdN x golden/control)
VERSION: v1.0
STATUS: Active
DEPENDS_ON: run_cfa_trinity_v3.py --phase 2
NEEDED_BY: CFA Claude — YPA lever scores for CT and MdN profiles
LAST_UPDATE: 2026-06-30
--->

# Trinity Phase 2 — YPA Lever Calibration Results

**Date:** 2026-06-30
**Script:** `run_cfa_trinity_v3.py --phase 2 --preset {ct|mdn} [--reverse] [--external-identities|--control]`
**Component:** 1 (deliberation only, no exit surveys)
**Levers:** CCI, EDB, PF_I, PF_E, AR, MG
**Total Runs:** 40 (4 conditions x 10 clean runs)

---

## Experiment Design

### Phase 2 Architecture

Phase 2 uses Phase 1 results as scoring context. Each auditor receives:
1. **Phase 1 findings** (7-metric quality audit results as calibration anchors)
2. **Prior values** (preset per framework — the "starting hypothesis" for each lever)
3. **0/5/10 anchors** (concrete behavioral descriptions for each lever score)
4. **Bayesian prior injection** (auditors told to treat priors as informed starting points)

### 2x2 Condition Matrix

| Folder | Subject | Identity | Stance | Preset |
|--------|---------|----------|--------|--------|
| `1/` | Classical Theism | Golden (LITE files) | `ct_vs_mdn` (Claude PRO-CT) | `--preset ct` |
| `2/` | Classical Theism | Control (no identity) | `ct_vs_mdn` | `--preset ct --control` |
| `3/` | Methodological Naturalism | Golden (LITE files) | `mdn_vs_ct` (Claude ANTI-MdN) | `--preset mdn --reverse` |
| `4/` | Methodological Naturalism | Control (no identity) | `mdn_vs_ct` | `--preset mdn --reverse --control` |

### Prior Values

| Lever | CT Prior | MdN Prior | Description |
|-------|----------|-----------|-------------|
| CCI | 7.5 | 8.0 | Conceptual Coherence & Internal Consistency |
| EDB | 8.5 | 7.5 | Empirical Dialogue & Bridge-Building |
| PF_I | 7.0 | 10.0 | Predictive Fertility — Internal |
| PF_E | 8.0 | 3.0 | Predictive Fertility — External |
| AR | 8.5 | 7.0 | Aesthetic Resonance |
| MG | 8.5 | 4.0 | Moral Generativity |

---

## Results Summary

### Instrument Behavior

|  | CT Golden (1/) | CT Control (2/) | MdN Golden (3/) | MdN Control (4/) |
|---|---|---|---|---|
| **Convergence** | 90.3% | 98.8% | 91.7% | 98.9% |
| **Avg Rounds** | 3.2 | 1.6 | 2.7 | 1.5 |
| **Total Cruxes** | 17 | 0 | 8 | 0 |

**Key pattern:** Identity creates debate on Phase 2 levers just as it did on Phase 1 metrics. Control runs converge in ~1.5 rounds with zero cruxes. Golden runs need 2.7-3.2 rounds and generate real disagreements. The instrument is working as designed.

---

## Lever Scores

### CT Lever Scores (n=10 per condition)

| Lever | Prior | Golden (C) | Golden (G) | Golden Final | Control Final | Identity Effect |
|-------|-------|-----------|-----------|-------------|--------------|----------------|
| CCI | 7.5 | 6.95 | 6.12 | **6.53** (sd=0.27) | **7.43** (sd=0.31) | -0.90 |
| EDB | 8.5 | 7.18 | 6.01 | **6.60** (sd=0.39) | **7.72** (sd=0.31) | -1.12 |
| PF_I | 7.0 | 5.27 | 4.44 | **4.85** (sd=0.79) | **6.65** (sd=0.60) | -1.80 |
| PF_E | 8.0 | 7.65 | 6.83 | **7.24** (sd=0.43) | **8.42** (sd=0.23) | -1.18 |
| AR | 8.5 | 7.64 | 6.60 | **7.12** (sd=0.34) | **8.62** (sd=0.34) | -1.50 |
| MG | 8.5 | 7.67 | 6.59 | **7.13** (sd=0.25) | **8.18** (sd=0.34) | -1.05 |

**CT identity effect:** Consistently pulls all 6 levers DOWN by 0.9-1.8 points. The adversarial process challenges CT's high priors effectively. PF_I sees the largest correction (-1.80) — internal predictive fertility is CT's weakest lever under scrutiny.

### MdN Lever Scores (n=10 per condition)

| Lever | Prior | Golden (C) | Golden (G) | Golden Final | Control Final | Identity Effect |
|-------|-------|-----------|-----------|-------------|--------------|----------------|
| CCI | 8.0 | 6.43 | 7.19 | **6.81** (sd=0.36) | **6.24** (sd=0.53) | +0.57 |
| EDB | 7.5 | 6.10 | 6.88 | **6.49** (sd=0.38) | **7.37** (sd=0.39) | -0.88 |
| PF_I | 10.0 | 7.59 | 8.54 | **8.07** (sd=0.43) | **9.28** (sd=0.21) | -1.21 |
| PF_E | 3.0 | 4.21 | 4.86 | **4.54** (sd=0.51) | **4.50** (sd=0.68) | +0.03 |
| AR | 7.0 | 5.83 | 6.81 | **6.32** (sd=0.41) | **6.45** (sd=0.28) | -0.13 |
| MG | 4.0 | 4.38 | 5.26 | **4.82** (sd=0.37) | **4.49** (sd=0.57) | +0.34 |

**MdN identity effect:** Much weaker and mixed. EDB and PF_I pull down (adversarial friction), but CCI and MG actually go UP with identity — the LITE files provide context that helps auditors see MdN strengths. PF_E is essentially unchanged (+0.03), confirming MdN's external predictive weakness is framework-intrinsic, not a scoring artifact.

---

## Cross-Framework Analysis

### Identity Effect Asymmetry

| Lever | CT Effect | MdN Effect | Interpretation |
|-------|-----------|-----------|----------------|
| CCI | -0.90 | +0.57 | CT identity reveals incoherence; MdN identity clarifies coherence |
| EDB | -1.12 | -0.88 | Both lose under scrutiny — adversarial process finds bridge-building gaps |
| PF_I | -1.80 | -1.21 | Largest corrections for both — internal predictions are the weakest claim |
| PF_E | -1.18 | +0.03 | CT inflated without identity; MdN already at floor |
| AR | -1.50 | -0.13 | CT aesthetic claims collapse under challenge; MdN stable |
| MG | -1.05 | +0.34 | CT moral claims deflated; MdN slightly boosted by context |

**Summary:** CT priors were systematically too high — the adversarial process corrects every lever downward. MdN priors were closer to base model intuitions, so identity creates less friction. The asymmetry is not bias — it reflects genuine differences in how well each framework's claims survive adversarial scrutiny.

### Base Model Priors vs Phase 2 Finals

Where do the models land without identity (control) vs with it (golden)?

| Lever | CT Control | CT Golden | MdN Control | MdN Golden |
|-------|-----------|-----------|-------------|-----------|
| CCI | 7.43 | 6.53 | 6.24 | 6.81 |
| EDB | 7.72 | 6.60 | 7.37 | 6.49 |
| PF_I | 6.65 | 4.85 | 9.28 | 8.07 |
| PF_E | 8.42 | 7.24 | 4.50 | 4.54 |
| AR | 8.62 | 7.12 | 6.45 | 6.32 |
| MG | 8.18 | 7.13 | 4.49 | 4.82 |

**Notable:** Base models (control) rate CT highly (7.4-8.6) and MdN modestly (4.5-9.3) on every lever. MdN's extreme priors (PF_I=10.0, PF_E=3.0) are partially validated — control PF_I=9.28 (near prior) and control PF_E=4.50 (corrected up from 3.0 prior). The adversarial process then applies a second correction on top of base model intuitions.

---

## Run Quality

### Extraction Failures & Aborts

| Condition | Launched | Aborted | Clean | Used |
|-----------|----------|---------|-------|------|
| CT Golden (1/) | 15 | 3 | 12 | 10 |
| CT Control (2/) | 10 | 0 | 10 | 10 |
| MdN Golden (3/) | 12 | 2 | 10 | 10 |
| MdN Control (4/) | 12 | 0 | 12 | 10 |

- Abort-on-extraction-failure logic active for all runs
- Grok CCI and MG are the typical failure points (~5% extraction miss rate)
- Control runs: zero failures across 22 runs (shorter prompts, no identity context)
- Golden runs: ~15-17% abort rate (longer prompts with Phase 1 context + identity)

---

## Data Location

### Raw JSON Files

```
SYNC_OUT/running/raw_runs/
  1/  CT golden    (10 files: 120324, 122715, 131638, 133948, 143056, 145040, 151355, 160608, 163934, 170008)
  2/  CT control   (10 files: 180131, 180550, 180900, 181304, 181709, 182030, 182325, 182729, 183210, 183612)
  3/  MdN golden   (10 files: 185711, 191350, 192757, 194506, 200007, 201634, 203400, 204738, 210310, 211916)
  4/  MdN control  (10 files: 220612, 220930, 221311, 221635, 222010, 222335, 222726, 223139, 223450, 223848)
```

### JSON Structure (per run)

Each file contains:
- `phase: 2` — identifies as Phase 2 run
- `condition: "external" | "control"` — golden vs control
- `stance: "ct_vs_mdn" | "mdn_vs_ct"` — forward vs reverse
- `prior_values: {CCI, EDB, PF_I, PF_E, AR, MG}` — starting priors
- `phase1_source` — path to Phase 1 JSON used as context
- `component1_results.{lever}` — per-lever scores with:
  - `claude_score`, `grok_score`, `final_score`
  - `prior_value`, `delta`, `delta_reason`, `calibration_status`
  - `convergence`, `rounds_taken`, `crux_declared`
  - `round_scores` — tick-by-tick deliberation data
  - `transcript` — full auditor responses

---

## Questions for CFA Claude

1. **Prior calibration quality:** CT priors were systematically ~1-1.5 points too high. MdN priors were closer to validated. Should we adjust priors before scoring additional frameworks, or treat the delta as the interesting signal?

2. **PF_I as discriminator:** Both frameworks see their largest correction on internal predictive fertility. Is this because PF_I is genuinely the hardest lever to defend, or because the Phase 1 context biases auditors toward skepticism on predictions?

3. **MdN identity boost on CCI/MG:** Unlike CT (where identity always hurts), MdN identity actually helps on CCI (+0.57) and MG (+0.34). The LITE files seem to provide context that base models lack. Is this a genuine signal or an artifact of MdN being less culturally familiar?

4. **Control convergence ceiling:** Both CT and MdN controls hit ~99% convergence in ~1.5 rounds. Is this ceiling effect (auditors just agreeing quickly without engagement) or genuine consensus? The zero-crux pattern suggests the former.

5. **Recommended final scores:** Given golden and control data, what should the YPA lever scores be for each framework's profile? Options: use golden (adversarially tested), use control (base model consensus), or weight/blend them.
