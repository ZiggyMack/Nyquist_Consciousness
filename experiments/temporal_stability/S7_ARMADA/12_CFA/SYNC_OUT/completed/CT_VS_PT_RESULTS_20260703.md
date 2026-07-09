# CT vs PT CFA Trinity Results (Gap-Filler: Completing the 3×3 Triangle)

**Date:** 2026-07-03
**Stance:** ct_vs_pt (Claude ANTI-CT from PT perspective, Grok PRO-CT)
**Subject:** Classical Theism | **Opponent:** Process Theology
**Total clean runs:** 40 (4 conditions × 10 runs)
**Significance:** Completes the CT↔PT axis. We had PT-as-subject vs CT; this adds CT-as-subject vs PT. Together with PT vs MdN (next), fills the 3×3 triangle.

---

## Experiment Matrix

| | Golden (External Identity) | Control (Hardcoded) |
|---|---|---|
| **Phase 1** (7 metrics) | Folder 1/ (10 runs) | Folder 2/ (10 runs) |
| **Phase 2** (6 YPA levers) | Folder 3/ (10 runs) | Folder 4/ (10 runs) |

---

## Phase 1: Baseline Deliberation (BFI, CA, IP, ES, LS, MS, PS)

### Phase 1 Golden (External Identities) (n=10)

| Metric | Claude | Grok | Gap | Conv | Rounds | Crux% |
|--------|--------|------|-----|------|--------|-------|
| BFI | 7.71 | 8.42 | -0.71 | 92.9% | 2.3 | 10% |
| CA | 6.02 | 7.12 | -1.10 | 89.0% | 3.5 | 30% |
| IP | 7.40 | 8.30 | -0.90 | 91.0% | 2.9 | 30% |
| ES | 6.06 | 7.27 | -1.21 | 87.9% | 3.3 | 30% |
| LS | 6.39 | 7.44 | -1.05 | 89.5% | 3.5 | 40% |
| MS | 6.82 | 7.64 | -0.82 | 91.8% | 2.7 | 10% |
| PS | 5.90 | 6.72 | -0.81 | 91.9% | 3.4 | 30% |

**Summary:** conv=90.6%, rounds=3.1, crux/run=1.8

### Phase 1 Control (Hardcoded Identities) (n=10)

| Metric | Claude | Grok | Gap | Conv | Rounds | Crux% |
|--------|--------|------|-----|------|--------|-------|
| BFI | 7.99 | 7.94 | +0.05 | 98.7% | 1.7 | 0% |
| CA | 7.17 | 7.37 | -0.20 | 97.8% | 1.6 | 0% |
| IP | 9.18 | 8.98 | +0.20 | 98.0% | 1.7 | 0% |
| ES | 7.69 | 7.64 | +0.05 | 98.9% | 1.8 | 0% |
| LS | 6.64 | 7.13 | -0.49 | 95.1% | 1.9 | 0% |
| MS | 8.44 | 8.52 | -0.08 | 98.2% | 1.7 | 0% |
| PS | 7.94 | 7.81 | +0.13 | 97.7% | 1.9 | 0% |

**Summary:** conv=97.8%, rounds=1.8, crux/run=0.0

### Phase 1 Identity Effect

| Metric | Golden Conv | Control Conv | Delta | Golden Crux% | Control Crux% |
|--------|-------------|--------------|-------|--------------|---------------|
| BFI | 92.9% | 98.7% | -5.8 pts | 10% | 0% |
| CA | 89.0% | 97.8% | -8.8 pts | 30% | 0% |
| IP | 91.0% | 98.0% | -7.0 pts | 30% | 0% |
| ES | 87.9% | 98.9% | -11.0 pts | 30% | 0% |
| LS | 89.5% | 95.1% | -5.6 pts | 40% | 0% |
| MS | 91.8% | 98.2% | -6.4 pts | 10% | 0% |
| PS | 91.9% | 97.7% | -5.8 pts | 30% | 0% |

**Identity gap:** 7.2 pts (90.6% golden vs 97.8% control). Consistent with other matchups — identity creates all friction.

---

## 🔧 BUG FIX: Sign-Off Extraction (Discovered During This Batch)

Initial observation: CT vs PT controls appeared to have unprecedented RED sign-offs (Grok: 6/10, Nova: 5/10). Investigation revealed an **extraction bug**, not a real anomaly.

### Root cause

The sign-off extraction logic (`if "RED" in response.upper()`) searched the entire reviewer response text, not just the verdict line. Reviewers writing "a RED designation would be warranted if..." or "RED flag" triggered false RED extraction even when their actual verdict (first line) was YELLOW.

**9 out of 11 "RED" sign-offs were actually YELLOW** — only 1 was a genuine RED.

### Fix applied

Changed extraction to parse only the first line of the sign-off response, and check YELLOW before RED:
```python
sign_off_first_line = sign_off_response.split("\n")[0].upper()
if "GREEN" in sign_off_first_line: ...
elif "YELLOW" in sign_off_first_line: ...
elif "RED" in sign_off_first_line: ...
```

### Impact

- **Prior batches may also have inflated RED counts** — all sign-off data from earlier matchups should be re-audited
- **Deliberation data (scores, convergence, cruxes) is unaffected** — this bug only impacts Component 2 sign-off metadata
- Controls remain normal: 97.8% convergence, zero cruxes, consistent with all other control batches

---

## Phase 2: YPA Lever Calibration (CCI, EDB, PF_I, PF_E, AR, MG)

**Priors (from CLASSICAL_THEISM.yaml):** CCI=7.5, EDB=8.5, PF_I=7.0, PF_E=8.0, AR=8.5, MG=8.5

### Phase 2 Golden (External Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 7.5 | 7.14 | 7.51 | 7.33 | -0.17 | 96.3% | 2.0 |
| EDB | 8.5 | 7.67 | 8.15 | 7.91 | -0.59 | 95.2% | 2.0 |
| PF_I | 7.0 | 5.45 | 6.11 | 5.78 | -1.22 | 93.4% | 2.3 |
| PF_E | 8.0 | 7.36 | 7.94 | 7.65 | -0.35 | 94.2% | 2.1 |
| AR | 8.5 | 7.68 | 8.06 | 7.87 | -0.63 | 96.2% | 2.0 |
| MG | 8.5 | 7.79 | 8.23 | 8.01 | -0.49 | 95.6% | 2.1 |

**Summary:** conv=95.2%, rounds=2.1

### Phase 2 Control (Hardcoded Identities) (n=10)

| Lever | Prior | Claude | Grok | Final | Delta | Conv | Rounds |
|-------|-------|--------|------|-------|-------|------|--------|
| CCI | 7.5 | 7.21 | 7.35 | 7.28 | -0.22 | 98.6% | 1.7 |
| EDB | 8.5 | 7.48 | 7.45 | 7.46 | -1.04 | 98.9% | 1.3 |
| PF_I | 7.0 | 6.75 | 6.86 | 6.80 | -0.20 | 98.1% | 1.8 |
| PF_E | 8.0 | 8.22 | 8.12 | 8.17 | +0.17 | 98.8% | 1.6 |
| AR | 8.5 | 8.54 | 8.49 | 8.52 | +0.02 | 99.1% | 1.5 |
| MG | 8.5 | 8.22 | 8.24 | 8.23 | -0.27 | 99.0% | 1.7 |

**Summary:** conv=98.8%, rounds=1.6

### Phase 2 Identity Effect on Levers

| Lever | Prior | Golden Final | Control Final | Golden Delta | Control Delta | Identity Pull |
|-------|-------|-------------|---------------|-------------|---------------|---------------|
| CCI | 7.5 | 7.33 | 7.28 | -0.17 | -0.22 | +0.05 |
| EDB | 8.5 | 7.91 | 7.46 | -0.59 | -1.04 | +0.45 |
| PF_I | 7.0 | 5.78 | 6.80 | -1.22 | -0.20 | -1.02 |
| PF_E | 8.0 | 7.65 | 8.17 | -0.35 | +0.17 | -0.52 |
| AR | 8.5 | 7.87 | 8.52 | -0.63 | +0.02 | -0.65 |
| MG | 8.5 | 8.01 | 8.23 | -0.49 | -0.27 | -0.22 |

**PF_I is CT's biggest lever vulnerability when PT challenges:** Identity pulls it down 1.02 points beyond baseline — PT's process-relational critique specifically targets CT's instrumental pragmatism.

---

## Cross-Matchup Comparison (3×3 Triangle Progress)

### Golden Phase 1 Convergence (COMPLETE 3×3 Triangle)

| Subject \ Opponent | CT | MdN | PT |
|---|---|---|---|
| **CT** | — | 85.8% | **90.6% (this batch)** |
| **MdN** | 86.2% | — | 85.0% |
| **PT** | 88.8% | **85.9% (PT vs MdN batch)** | — |

### Key findings from the complete triangle

1. **CT finds PT the softest opponent** (90.6% vs 85.8% against MdN). Shared theistic foundations dampen friction.
2. **PT is hardest to defend against MdN** (85.9%) but easiest to defend against CT (88.8%). The empirical challenge is sharper than the theological one.
3. **MdN is consistently hard to defend** regardless of opponent (86.2% vs CT, 85.0% vs PT).
4. **PT is the sharpest attacker against MdN** (drops it to 85.0%) but weakest against CT (only drops to 90.6%).

---

## Data Locations

| Folder | Contents | Path |
|--------|----------|------|
| 1/ | CT-vs-PT Phase 1 Golden (10 runs) | `SYNC_OUT/running/raw_runs/1/` |
| 2/ | CT-vs-PT Phase 1 Control (10 runs) | `SYNC_OUT/running/raw_runs/2/` |
| 3/ | CT-vs-PT Phase 2 Golden (10 runs) | `SYNC_OUT/running/raw_runs/3/` |
| 4/ | CT-vs-PT Phase 2 Control (10 runs) | `SYNC_OUT/running/raw_runs/4/` |

---

## Questions for CFA Claude

1. **Shared theistic ground hypothesis:** CT converges at 90.6% against PT but only 85.8% against MdN. Is this because CT and PT share theistic commitments (both affirm God, purpose, meaning) that reduce the surface area of genuine disagreement? Or is PT simply a weaker challenger?

2. **Reverse comparison:** We now have both PT-as-subject vs CT (88.8% conv, 2.8 crux/run) and CT-as-subject vs PT (90.6% conv, 1.8 crux/run). CT is *easier* to defend against PT than PT is to defend against CT. Does this asymmetry reveal which framework has more to defend?

3. **PF_I as CT's lever vulnerability:** Identity pulls PF_I down 1.02 points (golden: 5.78 vs control: 6.80). PT's process-relational critique specifically targets CT's instrumental pragmatism. Compare with MdN's PF_I=10.0 — does the lever vulnerability pattern reveal which dimensions are genuinely contested vs. assumed?

4. **LS crux pattern:** LS leads golden Phase 1 with 40% crux rate. Control LS convergence (95.1%) is also the lowest control metric. Is Logical Soundness the axis where CT's classical metaphysics is most vulnerable to PT's critique?

5. **Sign-off extraction bug (fixed):** Prior batches may have inflated RED counts due to `if "RED" in response` catching incidental word usage. Please re-audit any Component 2 sign-off data from earlier matchups — deliberation data (scores, convergence, cruxes) is unaffected.

---

## Technical Notes

- **Gap-filler run** completing the CT↔PT bidirectional axis (3×3 triangle now complete)
- **Stance:** `ct_vs_pt` — Claude challenges CT from PT's process-relational perspective, Grok defends CT
- **Zero extraction failures** across all 40 runs (regex fix holding)
- **Sign-off extraction bug discovered and fixed** during this batch — see bug fix section above
- **JSON schema:** Trinity v3 format (component1_results). Same schema as all other CFA runs.
