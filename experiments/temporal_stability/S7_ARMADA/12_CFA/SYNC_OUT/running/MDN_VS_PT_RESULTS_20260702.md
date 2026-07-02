# MdN vs PT CFA Trinity Results (CT-Free Matchup)

**Date:** 2026-07-02
**Stance:** mdn_vs_pt (Claude ANTI-MdN from PT perspective, Grok PRO-MdN)
**Subject:** Methodological Naturalism | **Opponent:** Process Theology
**Total clean runs:** 40
**Significance:** First CT-free matchup -- tests whether identity friction patterns hold without Classical Theism as anchor.

---

## Experiment Matrix

| | Golden (External Identity) | Control (Hardcoded) |
|---|---|---|
| **Phase 1** (7 metrics) | Folder 9/ (10 runs) | Folder 10/ (10 runs) |
| **Phase 2** (6 YPA levers) | Folder 11/ (10 runs) | Folder 12/ (10 runs) |

---

## Phase 1: Baseline Deliberation (BFI, CA, IP, ES, LS, MS, PS)

### Phase 1 Golden (External Identities) (n=10)

| Metric | Claude | Grok | Gap | Conv | Rounds | Crux% |
|--------|--------|------|-----|------|--------|-------|
| BFI | 5.26 | 6.48 | -1.22 | 85.2% | 4.2 | 50% |
| CA | 5.53 | 7.55 | -2.02 | 79.8% | 4.7 | 90% |
| IP | 6.34 | 7.50 | -1.16 | 88.4% | 3.8 | 50% |
| ES | 6.33 | 7.78 | -1.45 | 85.5% | 4.4 | 70% |
| LS | 6.17 | 7.43 | -1.26 | 87.4% | 4.1 | 40% |
| MS | 4.14 | 6.17 | -2.03 | 79.7% | 5.0 | 100% |
| PS | 6.39 | 7.49 | -1.10 | 89.0% | 4.2 | 50% |

**Summary:** conv=85.0%, rounds=4.3, crux/run=4.5

### Phase 1 Control (Hardcoded Identities) (n=10)

| Metric | Claude | Grok | Gap | Conv | Rounds | Crux% |
|--------|--------|------|-----|------|--------|-------|
| BFI | 3.79 | 3.71 | +0.08 | 99.2% | 1.6 | 0% |
| CA | 7.15 | 7.19 | -0.04 | 99.0% | 1.2 | 0% |
| IP | 7.96 | 7.88 | +0.08 | 98.2% | 1.9 | 0% |
| ES | 7.12 | 7.09 | +0.03 | 99.3% | 1.3 | 0% |
| LS | 7.61 | 7.79 | -0.18 | 98.2% | 1.9 | 0% |
| MS | 3.37 | 3.37 | +0.00 | 99.4% | 1.7 | 0% |
| PS | 8.22 | 8.32 | -0.10 | 98.4% | 1.6 | 0% |

**Summary:** conv=98.8%, rounds=1.6, crux/run=0.0

### Phase 1 Identity Effect

| Metric | Golden Conv | Control Conv | Delta | Golden Crux% | Control Crux% |
|--------|-------------|--------------|-------|--------------|---------------|
| BFI | 85.2% | 99.2% | -14.0 pts | 50% | 0% |
| CA | 79.8% | 99.0% | -19.2 pts | 90% | 0% |
| IP | 88.4% | 98.2% | -9.8 pts | 50% | 0% |
| ES | 85.5% | 99.3% | -13.8 pts | 70% | 0% |
| LS | 87.4% | 98.2% | -10.8 pts | 40% | 0% |
| MS | 79.7% | 99.4% | -19.7 pts | 100% | 0% |
| PS | 89.0% | 98.4% | -9.4 pts | 50% | 0% |

**Identity creates ALL friction.** Control convergence: 98.8%, zero cruxes. Golden: 85.0%.

---

## Phase 2: YPA Lever Calibration (CCI, EDB, PF_I, PF_E, AR, MG)

**Priors (from METHODOLOGICAL_NATURALISM.yaml):** CCI=8.0, EDB=5.0, PF_I=9.0, PF_E=4.0, AR=3.0, MG=4.5

### Phase 2 Golden (External Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 8.0 | 6.95 | 7.58 | 7.27 | -0.73 | 93.7% | 2.0 |
| EDB | 5.0 | 6.58 | 7.10 | 6.84 | +1.84 | 94.8% | 2.0 |
| PF_I | 9.0 | 8.59 | 9.12 | 8.86 | -0.14 | 94.7% | 2.1 |
| PF_E | 4.0 | 3.31 | 3.86 | 3.58 | -0.42 | 94.5% | 2.0 |
| AR | 3.0 | 6.27 | 6.89 | 6.58 | +3.58 | 93.8% | 2.2 |
| MG | 4.5 | 3.55 | 4.25 | 3.90 | -0.60 | 93.0% | 2.8 |

**Summary:** conv=94.1%, rounds=2.2

### Phase 2 Control (Hardcoded Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 8.0 | 6.04 | 6.11 | 6.08 | -1.92 | 99.3% | 1.5 |
| EDB | 5.0 | 7.33 | 7.30 | 7.31 | +2.31 | 98.7% | 1.4 |
| PF_I | 9.0 | 9.35 | 9.34 | 9.34 | +0.34 | 98.9% | 1.2 |
| PF_E | 4.0 | 4.57 | 4.57 | 4.57 | +0.57 | 99.2% | 1.7 |
| AR | 3.0 | 6.26 | 6.30 | 6.28 | +3.28 | 98.8% | 1.6 |
| MG | 4.5 | 4.32 | 4.30 | 4.31 | -0.19 | 99.0% | 1.8 |

**Summary:** conv=99.0%, rounds=1.5

### Phase 2 Identity Effect on Levers

| Lever | Prior | Golden Final | Control Final | Golden Delta | Control Delta | Identity Pull |
|-------|-------|-------------|---------------|-------------|---------------|---------------|
| CCI | 8.0 | 7.27 | 6.08 | -0.73 | -1.92 | +1.19 |
| EDB | 5.0 | 6.84 | 7.31 | +1.84 | +2.31 | -0.47 |
| PF_I | 9.0 | 8.86 | 9.34 | -0.14 | +0.34 | -0.49 |
| PF_E | 4.0 | 3.58 | 4.57 | -0.42 | +0.57 | -0.99 |
| AR | 3.0 | 6.58 | 6.28 | +3.58 | +3.28 | +0.30 |
| MG | 4.5 | 3.90 | 4.31 | -0.60 | -0.19 | -0.41 |

**Identity Pull** = Golden Delta - Control Delta (how much external identity moves the lever beyond baseline)

---

## Cross-Matchup Comparison

This is the first CT-free matchup. Compare with CT-involved results:

| Matchup | Opponent | Phase 1 Conv | Phase 1 Crux/Run | CT Involved? |
|---------|----------|-------------|------------------|-------------|
| CT vs MdN | MdN | 86.6% | 3.8 | Yes (subject) |
| MdN vs CT | CT | 86.2% | 3.7 | Yes (opponent) |
| PT vs CT | CT | 88.8% | 2.8 | Yes (opponent) |
| **MdN vs PT** | **PT** | **85.0%** | **4.5** | **No** |

---

## Data Locations

| Folder | Contents | Path |
|--------|----------|------|
| 9/ | MdN-vs-PT Phase 1 Golden (10 runs) | `SYNC_OUT/running/raw_runs/9/` |
| 10/ | MdN-vs-PT Phase 1 Control (10 runs) | `SYNC_OUT/running/raw_runs/10/` |
| 11/ | MdN-vs-PT Phase 2 Golden (10 runs) | `SYNC_OUT/running/raw_runs/11/` |
| 12/ | MdN-vs-PT Phase 2 Control (10 runs) | `SYNC_OUT/running/raw_runs/12/` |

---

## Questions for CFA Claude

1. **CT-free friction test:** Does the identity effect magnitude (golden vs control gap) hold without CT in the ring? If so, identity friction is a property of the instrument, not CT specifically.

2. **MdN lever behavior under PT opponent vs CT opponent:** Compare folders 11-12 (MdN vs PT) with the original MdN vs CT Phase 2 data. Do MdN's levers move differently when challenged by PT's process-relational critique vs CT's teleological critique?

3. **Crux pattern shift:** Which metrics lock up when PT is the opponent instead of CT? Does MdN's crux hotspot change depending on who's challenging it?

4. **Triangulation:** We now have 3 matchup types (CT-vs-MdN, PT-vs-CT, MdN-vs-PT). Can we triangulate a "worldview hardness" ranking from how each framework performs as both subject and opponent?

5. **Control convergence consistency:** Do controls converge at ~99% regardless of which worldview pair is being evaluated? This would confirm the control condition is truly measuring baseline model agreement, not worldview-specific effects.

---

## Technical Notes

- **First CT-free matchup** in the CFA Trinity pipeline
- **Stance:** `mdn_vs_pt` -- Claude challenges MdN from PT's process-relational perspective, Grok defends MdN with empirical rigor
- **Extraction regex fix** applied (ADVOCACY_SCORE markdown bold handling) -- zero extraction failures in golden batches
- **Phase 1 control had 4 extraction failures** from concurrent golden+control API calls (rate limiting). Topped up sequentially with zero failures.
- **JSON schema:** Trinity v3 format (component1_results, not SMV ticks format). Same schema as PT folders 5-8 and CT/MdN folders 1-4.
