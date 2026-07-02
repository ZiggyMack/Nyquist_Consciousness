# Process Theology CFA Trinity Results

**Date:** 2026-07-01
**Stance:** pt_vs_ct (Claude PRO-PT, Grok ANTI-PT)
**Subject:** Process Theology | **Opponent:** Classical Theism
**Total clean runs:** 40
**Script:** run_cfa_trinity_v3.py (with --stance flag, extraction regex fix)

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
| BFI | 7.30 | 5.69 | +1.61 | 83.9% | 4.1 | 70% |
| CA | 6.47 | 5.20 | +1.27 | 87.3% | 4.2 | 50% |
| IP | 7.10 | 6.33 | +0.77 | 92.3% | 2.7 | 20% |
| ES | 6.94 | 5.93 | +1.01 | 89.9% | 3.0 | 30% |
| LS | 7.19 | 6.19 | +1.00 | 90.0% | 3.6 | 30% |
| MS | 6.69 | 5.32 | +1.37 | 86.3% | 4.0 | 60% |
| PS | 5.68 | 4.89 | +0.79 | 92.1% | 3.0 | 20% |

**Summary:** conv=88.8%, rounds=3.5, crux/run=2.8

### Phase 1 Control (Hardcoded Identities) (n=10)

| Metric | Claude | Grok | Gap | Conv | Rounds | Crux% |
|--------|--------|------|-----|------|--------|-------|
| BFI | 7.77 | 7.72 | +0.05 | 98.9% | 1.8 | 0% |
| CA | 6.52 | 6.51 | +0.01 | 98.9% | 1.3 | 0% |
| IP | 7.40 | 7.22 | +0.18 | 98.2% | 1.7 | 0% |
| ES | 7.43 | 7.34 | +0.09 | 98.9% | 1.3 | 0% |
| LS | 6.73 | 6.82 | -0.09 | 98.5% | 1.7 | 0% |
| MS | 6.91 | 6.88 | +0.03 | 98.9% | 1.3 | 0% |
| PS | 4.93 | 4.78 | +0.15 | 98.5% | 1.5 | 0% |

**Summary:** conv=98.7%, rounds=1.5, crux/run=0.0

### Phase 1 Identity Effect

| Metric | Golden Conv | Control Conv | Delta | Golden Crux% | Control Crux% |
|--------|-------------|--------------|-------|--------------|---------------|
| BFI | 83.9% | 98.9% | -15.0 pts | 70% | 0% |
| CA | 87.3% | 98.9% | -11.6 pts | 50% | 0% |
| IP | 92.3% | 98.2% | -5.9 pts | 20% | 0% |
| ES | 89.9% | 98.9% | -9.0 pts | 30% | 0% |
| LS | 90.0% | 98.5% | -8.5 pts | 30% | 0% |
| MS | 86.3% | 98.9% | -12.6 pts | 60% | 0% |
| PS | 92.1% | 98.5% | -6.4 pts | 20% | 0% |

**Identity creates ALL friction.** Control convergence ceiling: 98.7% in 1.5 rounds, zero cruxes. Golden: 88.8% in 3.5 rounds, 2.8 cruxes/run.

---

## Phase 2: YPA Lever Calibration (CCI, EDB, PF_I, PF_E, AR, MG)

**Priors (from PROCESS_THEOLOGY.yaml):** CCI=7.0, EDB=7.5, PF_I=5.0, PF_E=7.0, AR=7.5, MG=6.5

### Phase 2 Golden (External Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 7.0 | 6.58 | 5.86 | 6.22 | -0.78 | 92.8% | 2.5 |
| EDB | 7.5 | 6.88 | 6.17 | 6.53 | -0.97 | 92.9% | 2.6 |
| PF_I | 5.0 | 4.06 | 3.38 | 3.72 | -1.28 | 93.2% | 2.1 |
| PF_E | 7.0 | 6.73 | 6.10 | 6.41 | -0.59 | 93.7% | 2.0 |
| AR | 7.5 | 6.93 | 6.18 | 6.55 | -0.95 | 92.5% | 2.6 |
| MG | 6.5 | 6.20 | 5.50 | 5.85 | -0.65 | 93.0% | 2.3 |

**Summary:** conv=93.0%, rounds=2.4

### Phase 2 Control (Hardcoded Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 7.0 | 6.68 | 6.79 | 6.74 | -0.26 | 98.7% | 1.5 |
| EDB | 7.5 | 7.47 | 7.30 | 7.38 | -0.12 | 98.3% | 1.7 |
| PF_I | 5.0 | 5.04 | 5.00 | 5.02 | +0.02 | 99.6% | 1.2 |
| PF_E | 7.0 | 6.67 | 6.58 | 6.62 | -0.38 | 99.1% | 1.4 |
| AR | 7.5 | 7.27 | 7.28 | 7.28 | -0.22 | 98.9% | 1.6 |
| MG | 6.5 | 6.83 | 6.72 | 6.78 | +0.28 | 98.8% | 1.6 |

**Summary:** conv=98.8%, rounds=1.5

### Phase 2 Identity Effect on Levers

| Lever | Prior | Golden Final | Control Final | Golden Delta | Control Delta | Identity Pull |
|-------|-------|-------------|---------------|-------------|---------------|---------------|
| CCI | 7.0 | 6.22 | 6.74 | -0.78 | -0.26 | -0.52 |
| EDB | 7.5 | 6.53 | 7.38 | -0.97 | -0.12 | -0.85 |
| PF_I | 5.0 | 3.72 | 5.02 | -1.28 | +0.02 | -1.30 |
| PF_E | 7.0 | 6.41 | 6.62 | -0.59 | -0.38 | -0.21 |
| AR | 7.5 | 6.55 | 7.28 | -0.95 | -0.22 | -0.73 |
| MG | 6.5 | 5.85 | 6.78 | -0.65 | +0.28 | -0.93 |

**Identity Pull** = Golden Delta - Control Delta (how much external identity moves the lever beyond baseline)

**Key findings:**
- ALL 6 levers pulled DOWN by identity (range: -0.21 to -1.30 pts)
- PF_I is the weakest lever (-1.30 identity pull) — consistent with PT's acknowledged empirical testability debt
- PF_E most resistant to identity effect (-0.21) — PT's existential meaning-making survives adversarial scrutiny
- Control holds priors tightly (max delta: -0.38 on PF_E) — confirms priors are reasonable anchors

---

## Cross-Framework Comparison (PT vs CT vs MdN)

### Phase 1 Golden Convergence

| Framework | Avg Conv | Avg Rounds | Crux/Run | Crux Rate |
|-----------|----------|------------|----------|-----------|
| CT (n=25) | 86.6% | 3.9 | 3.8 | 54% |
| MdN (n=10) | 86.2% | 4.1 | 3.7 | 53% |
| **PT (n=10)** | **88.8%** | **3.5** | **2.8** | **40%** |

PT converges faster with fewer cruxes than both CT and MdN despite being theism-vs-theism.

### Crux Hotspots by Framework

| Metric | CT Crux% | MdN Crux% | PT Crux% |
|--------|----------|-----------|----------|
| BFI | 84% | 90% | 70% |
| CA | 80% | 70% | 50% |
| MS | 52% | 30% | **60%** |
| PS | 32% | 50% | 20% |

PT's crux magnet is MS (Moral Substance) — Whitehead's aesthetics-of-experience doesn't map cleanly to moral prescriptions.

---

## Data Locations

| Folder | Contents | Path |
|--------|----------|------|
| 5/ | PT Phase 1 Golden (10 runs) | `SYNC_OUT/running/raw_runs/5/` |
| 6/ | PT Phase 1 Control (10 runs) | `SYNC_OUT/running/raw_runs/6/` |
| 7/ | PT Phase 2 Golden (10 runs) | `SYNC_OUT/running/raw_runs/7/` |
| 8/ | PT Phase 2 Control (10 runs) | `SYNC_OUT/running/raw_runs/8/` |

---

## Questions for CFA Claude

1. **PF_I collapse (-1.28 from prior, -1.30 identity pull):** Is this the largest lever movement we've seen across all three worldviews? Does it suggest PT's empirical testability is a fundamental structural weakness, or is the prior of 5.0 already accounting for this?

2. **Uniform downward pull:** CT Phase 2 also pulled all levers down. Is there a systematic adversarial bias in the golden condition, or does identity-driven scrutiny genuinely reveal inflated priors?

3. **MS as PT crux magnet (60%):** CT's crux hotspot was BFI (84%). MdN's was BFI (90%). PT's is MS. Does each worldview's crux pattern reveal its philosophical center of gravity?

4. **PT converges faster than CT/MdN:** Is this because Grok's empiricist critique of PT is sharper/more focused ("unfalsifiable speculative metaphysics" is a clean objection), or because PT's philosophical space is narrower?

5. **PF_E resilience (-0.21 identity pull):** PT's existential meaning-making survived adversarial scrutiny better than any other lever. Is this because process metaphysics genuinely excels at existential questions (grief, meaning, purpose), or is this a measurement artifact?

---

## Technical Notes

- **Extraction regex fix applied:** `ADVOCACY_SCORE[:\s\*]+` now handles Grok's markdown bold formatting (`**ADVOCACY_SCORE:** 5.8`). Prior regex missed 5/16 Phase 2 golden runs (31% failure rate). Fix applied mid-batch; all Phase 2 control runs (post-fix) had 0% failure rate.
- **Stance machinery:** `--stance pt_vs_ct` flag added to v3 script. Claude PRO-PT uses teleological lens; Grok ANTI-PT uses empirical lens. Both reference Whitehead, Hartshorne, Cobb, Griffin.
- **Phase 1 metrics:** BFI, CA, IP, ES, LS, MS, PS (7 standard deliberation metrics)
- **Phase 2 levers:** CCI, EDB, PF_I, PF_E, AR, MG (6 YPA levers with Bayesian prior injection)
