# PT vs MdN CFA Trinity Results (Gap-Filler: Completing the 3×3 Triangle)

**Date:** 2026-07-04
**Stance:** pt_vs_mdn (Claude PRO-PT, Grok ANTI-PT from MdN perspective)
**Subject:** Process Theology | **Opponent:** Methodological Naturalism
**Total clean runs:** 40 (4 conditions × 10 runs)
**Significance:** Completes the PT↔MdN axis. We had MdN-as-subject vs PT; this adds PT-as-subject vs MdN. The 3×3 triangle (CT, MdN, PT) is now fully bidirectional.

---

## Experiment Matrix

| | Golden (External Identity) | Control (Hardcoded) |
|---|---|---|
| **Phase 1** (7 metrics) | Folder 5/ (10 runs) | Folder 6/ (10 runs) |
| **Phase 2** (6 YPA levers) | Folder 7/ (10 runs) | Folder 8/ (10 runs) |

---

## Phase 1: Baseline Deliberation (BFI, CA, IP, ES, LS, MS, PS)

### Phase 1 Golden (External Identities) (n=10)

| Metric | Claude | Grok | Gap | Conv | Rounds | Crux% |
|--------|--------|------|-----|------|--------|-------|
| BFI | 7.30 | 5.36 | +1.94 | 80.6% | 4.7 | 90% |
| CA | 6.43 | 4.60 | +1.83 | 81.7% | 4.5 | 80% |
| IP | 7.15 | 6.23 | +0.92 | 90.8% | 3.5 | 30% |
| ES | 6.90 | 5.86 | +1.04 | 89.6% | 3.3 | 30% |
| LS | 6.92 | 5.59 | +1.33 | 86.7% | 4.3 | 70% |
| MS | 6.95 | 5.17 | +1.78 | 82.2% | 4.7 | 80% |
| PS | 6.12 | 5.12 | +1.00 | 90.0% | 3.8 | 30% |

**Summary:** conv=85.9%, rounds=4.1, crux/run=4.1

### Phase 1 Control (Hardcoded Identities) (n=10)

| Metric | Claude | Grok | Gap | Conv | Rounds | Crux% |
|--------|--------|------|-----|------|--------|-------|
| BFI | 8.09 | 8.00 | +0.09 | 98.7% | 1.6 | 0% |
| CA | 6.48 | 6.45 | +0.03 | 98.7% | 1.4 | 0% |
| IP | 7.48 | 7.37 | +0.11 | 98.3% | 1.7 | 0% |
| ES | 7.38 | 7.34 | +0.04 | 98.4% | 1.7 | 0% |
| LS | 6.70 | 6.75 | -0.05 | 98.7% | 1.7 | 0% |
| MS | 6.65 | 6.66 | -0.01 | 99.3% | 1.1 | 0% |
| PS | 5.12 | 5.01 | +0.11 | 98.5% | 1.7 | 0% |

**Summary:** conv=98.7%, rounds=1.6, crux/run=0.0

### Phase 1 Identity Effect

| Metric | Golden Conv | Control Conv | Delta | Golden Crux% | Control Crux% |
|--------|-------------|--------------|-------|--------------|---------------|
| BFI | 80.6% | 98.7% | -18.1 pts | 90% | 0% |
| CA | 81.7% | 98.7% | -17.0 pts | 80% | 0% |
| IP | 90.8% | 98.3% | -7.5 pts | 30% | 0% |
| ES | 89.6% | 98.4% | -8.8 pts | 30% | 0% |
| LS | 86.7% | 98.7% | -12.0 pts | 70% | 0% |
| MS | 82.2% | 99.3% | -17.1 pts | 80% | 0% |
| PS | 90.0% | 98.5% | -8.5 pts | 30% | 0% |

**Identity gap: 12.8 pts (85.9% golden vs 98.7% control).** This is the LARGEST identity gap in any matchup — MdN's empirical challenge against PT creates maximum friction when identities are loaded.

---

## Phase 2: YPA Lever Calibration (CCI, EDB, PF_I, PF_E, AR, MG)

**Priors (from PROCESS_THEOLOGY.yaml):** CCI=7.0, EDB=7.5, PF_I=5.0, PF_E=7.0, AR=7.5, MG=6.5

### Phase 2 Golden (External Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 7.0 | 6.66 | 5.91 | 6.29 | -0.71 | 92.5% | 2.4 |
| EDB | 7.5 | 6.72 | 5.96 | 6.34 | -1.16 | 92.4% | 2.2 |
| PF_I | 5.0 | 4.06 | 3.24 | 3.65 | -1.35 | 91.8% | 2.7 |
| PF_E | 7.0 | 6.80 | 5.96 | 6.38 | -0.62 | 91.6% | 2.8 |
| AR | 7.5 | 6.77 | 5.99 | 6.38 | -1.12 | 92.2% | 2.8 |
| MG | 6.5 | 6.40 | 5.46 | 5.93 | -0.57 | 90.5% | 2.9 |

**Summary:** conv=91.8%, rounds=2.6

### Phase 2 Control (Hardcoded Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 7.0 | 6.93 | 6.96 | 6.94 | -0.06 | 99.1% | 1.6 |
| EDB | 7.5 | 7.29 | 7.12 | 7.21 | -0.29 | 98.3% | 1.8 |
| PF_I | 5.0 | 5.14 | 5.00 | 5.07 | +0.07 | 98.4% | 1.6 |
| PF_E | 7.0 | 6.62 | 6.58 | 6.60 | -0.40 | 99.0% | 1.4 |
| AR | 7.5 | 7.34 | 7.34 | 7.34 | -0.16 | 98.6% | 1.7 |
| MG | 6.5 | 7.44 | 7.42 | 7.43 | +0.93 | 99.2% | 1.2 |

**Summary:** conv=98.8%, rounds=1.6

### Phase 2 Identity Effect on Levers

| Lever | Prior | Golden Final | Control Final | Golden Delta | Control Delta | Identity Pull |
|-------|-------|-------------|---------------|-------------|---------------|---------------|
| CCI | 7.0 | 6.29 | 6.94 | -0.71 | -0.06 | -0.65 |
| EDB | 7.5 | 6.34 | 7.21 | -1.16 | -0.29 | -0.87 |
| PF_I | 5.0 | 3.65 | 5.07 | -1.35 | +0.07 | -1.42 |
| PF_E | 7.0 | 6.38 | 6.60 | -0.62 | -0.40 | -0.22 |
| AR | 7.5 | 6.38 | 7.34 | -1.12 | -0.16 | -0.96 |
| MG | 6.5 | 5.93 | 7.43 | -0.57 | +0.93 | -1.50 |

**MG has the largest identity pull (-1.50):** MdN's empirical challenge hammers PT's moral generativity claim. Control actually RAISES MG (+0.93), but golden drops it — the adversarial identity context exposes MG as PT's most contestable lever.

**PF_I also heavily pulled (-1.42):** PT's instrumental pragmatism was already low (prior: 5.0) and MdN drives it even lower. PT generates no testable predictions — MdN makes this hurt.

---

## Cross-Matchup Comparison (Complete 3×3 Triangle)

### Golden Phase 1 Convergence

| Subject \ Opponent | CT | MdN | PT |
|---|---|---|---|
| **CT** | — | 85.8% | 90.6% |
| **MdN** | 86.2% | — | 85.0% |
| **PT** | 88.8% | **85.9% (this batch)** | — |

### Bidirectional Asymmetry

| Pairing | A-as-subject | B-as-subject | Easier to defend? |
|---------|-------------|-------------|-------------------|
| CT ↔ MdN | 85.8% | 86.2% | ~Symmetric |
| CT ↔ PT | 90.6% | 88.8% | CT (by 1.8 pts) |
| **MdN ↔ PT** | **85.0%** | **85.9%** | **PT (by 0.9 pts)** |

### Crux/run comparison

| Matchup | Crux/run | Top crux metrics |
|---------|---------|-----------------|
| CT vs MdN | 3.8 | BFI, CA |
| MdN vs CT | 3.7 | BFI, CA |
| PT vs CT | 2.8 | MS (60%) |
| MdN vs PT | 4+ | MS (100%), CA (90%) |
| CT vs PT | 1.8 | LS (40%) |
| **PT vs MdN** | **4.1** | **BFI (90%), CA (80%), MS (80%)** |

### Key insight: PT vs MdN is the crux-richest matchup

4.1 crux/run with BFI, CA, and MS all hitting 80%+ crux rates. MdN's empirical challenge finds THREE simultaneous fault lines in PT — foundational importance, causal adequacy, and moral substance. This is far more distributed than CT vs PT (concentrated on LS) or PT vs CT (concentrated on MS).

---

## Data Locations

| Folder | Contents | Path |
|--------|----------|------|
| 5/ | PT-vs-MdN Phase 1 Golden (10 runs) | `SYNC_OUT/running/raw_runs/5/` |
| 6/ | PT-vs-MdN Phase 1 Control (10 runs) | `SYNC_OUT/running/raw_runs/6/` |
| 7/ | PT-vs-MdN Phase 2 Golden (10 runs) | `SYNC_OUT/running/raw_runs/7/` |
| 8/ | PT-vs-MdN Phase 2 Control (10 runs) | `SYNC_OUT/running/raw_runs/8/` |

---

## Questions for CFA Claude

1. **Largest identity gap:** PT vs MdN has 12.8 pts identity gap (85.9% vs 98.7%) — the largest of any matchup. MdN vs PT had 13.8 pts. The MdN↔PT axis generates MORE friction than any CT-involved pairing. Why? Is it because CT shares theistic ground with PT that dampens disagreement?

2. **MG control anomaly:** Control RAISES PT's MG by +0.93 (from 6.5 prior to 7.43 final), but golden DROPS it by -0.57. The identity pull is -1.50 — the largest single lever pull in the dataset. Does this mean base models genuinely think PT has strong moral generativity, but adversarial MdN framing exposes it as indefensible?

3. **Crux distribution:** PT vs MdN hits 90% BFI, 80% CA, 80% MS crux rates simultaneously. Compare with MdN vs PT where CA hit 90% and MS hit 100%. The crux pattern is MUTUAL — both frameworks find the other's foundations, causation, and moral substance simultaneously indefensible. Is this the signature of genuine philosophical incommensurability?

4. **PT defensibility ranking:** PT converges at 88.8% vs CT but only 85.9% vs MdN. The empirical challenge is sharper than the theological one. Does PT's YAML profile need different lever adjustments depending on which opponent is challenging?

5. **3×3 triangle synthesis:** With all 6 bidirectional matchups complete, can you produce a definitive worldview hardness ranking and identify which opponent-type (empirical vs theological vs process-relational) creates the most diagnostic friction for each subject?

---

## Technical Notes

- **Gap-filler run** completing the PT↔MdN bidirectional axis (3×3 triangle now fully complete)
- **Stance:** `pt_vs_mdn` — Claude advocates for PT, Grok challenges from MdN's empirical perspective
- **1 extraction failure** (PF_I) in original Phase 2 Golden batch — topped up with 1 additional run
- **Sign-off extraction fix** live for this batch — all YELLOW/YELLOW (corrected extraction logic)
- **JSON schema:** Trinity v3 format (component1_results). Same schema as all other CFA runs.
