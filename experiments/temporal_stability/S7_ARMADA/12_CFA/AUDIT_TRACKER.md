# CFA Audit Tracker

**Purpose:** Single source of truth for what runs exist, where they live, and what's outstanding.

**Last updated:** 2026-07-07

---

## Framework Under Test (FUT) Registry

| Abbr | Framework | Added | Phase 2 Preset | Status |
|------|-----------|-------|-----------------|--------|
| CT | Classical Theism | 2026-06-29 | ct | Active |
| MdN | Methodological Naturalism | 2026-06-29 | mdn | Active |
| PT | Process Theology | 2026-07-01 | pt | Active |
| G | Gnosticism | 2026-07-02 | g | Active |
| B | Buddhism | 2026-07-07 | b | Running |

---

## Completion Matrix

Each cell = (External runs / Control runs). Target: 10/10 per cell.

### Phase 1 Metrics (BFI, CA, IP, ES, LS, MS, PS)

```
Subject \  Opp |  CT       MdN       PT        G         B
───────────────┼─────────────────────────────────────────────
 CT            |  --       10/10(A)  10/10(R)  10/10(R)  ??/??(B)
 MdN           |  10/10(A) --        10/10(R)  10/10(R)  ??/??(B)
 PT            |  10/10(A) 10/10(R)  --        20/19(R)  ??/??(B)
 G             |  10/10(A) 20/20(R)  22/20(R)  --        ??/??(B)
 B             |  ??/??(B) ??/??(B)  ??/??(B)  ??/??(B)  --

(A) = Archived in CFA repo    (R) = In 0_results/runs/    (B) = Buddhism batch running
```

### Phase 2 Metrics (CCI, EDB, PF_I, PF_E, AR, MG)

```
Subject \  Opp |  CT       MdN       PT        G         B
───────────────┼─────────────────────────────────────────────
 CT            |  --       10/10(A)  10/10(R)  10/10(R)  --
 MdN           |  10/10(A) --        10/10(R)  10/10(R)  --
 PT            |  10/10(A) 10/10(R)  --        20/20(R)  --
 G             |  10/10(A) 20/20(R)  20/20(R)  --        --
 B             |  --       --        --        --        --

Phase 2 not yet run for Buddhism matchups.
```

---

## Run Locations

Runs are split across two repos due to the CFA sync lifecycle.

### Nyquist_Consciousness repo

`experiments/temporal_stability/S7_ARMADA/0_results/runs/`

| Stance | Condition | P1 Runs | P2 Runs | Notes |
|--------|-----------|---------|---------|-------|
| ct_vs_pt | external | 10 | 10 | |
| ct_vs_pt | control | 10 | 10 | |
| pt_vs_mdn | external | 10+1 | 10 | 1 extra external |
| pt_vs_mdn | control | 10 | 10 | |
| ct_vs_g | external | 10 | 10 | Gnostic batch |
| ct_vs_g | control | 10 | 10 | |
| g_vs_ct | external | 10 | 10 | |
| g_vs_ct | control | 10 | 10 | |
| mdn_vs_g | external | 10 | 10 | |
| mdn_vs_g | control | 10 | 10 | |
| g_vs_mdn | external | 20 | 20 | Overshot (2x) |
| g_vs_mdn | control | 20 | 20 | |
| pt_vs_g | external | 20 | 20 | |
| pt_vs_g | control | 19 | 20 | 1 short on P1 |
| g_vs_pt | external | 22 | 20 | |
| g_vs_pt | control | 20 | 20 | |
| b_vs_* | * | ?? | -- | Buddhism batch in progress |
| *_vs_b | * | ?? | -- | Buddhism batch in progress |

`experiments/temporal_stability/S7_ARMADA/0_results/runs/.errored/`
- API-failure runs preserved for audit trail

### CFA repo (archived after CFA Claude processing)

`d:\Documents\CFA\docs\REPO_SYNC\.archive\raw_runs\`

| Batch Directory | Stance | Cond | Runs | Phase | Date |
|-----------------|--------|------|------|-------|------|
| ct_batch_20260629 | ct_vs_mdn | external | 20 | P1 | 2026-06-29 |
| ct_p2_golden_20260630 | ct_vs_mdn | external | 10 | P2 | 2026-06-30 |
| ct_p2_control_20260630 | ct_vs_mdn | control | 10 | P2 | 2026-06-30 |
| mdn_golden_20260630 | mdn_vs_ct | external | 10 | P1 | 2026-06-30 |
| mdn_control_20260630 | mdn_vs_ct | control | 10 | P1 | 2026-06-30 |
| mdn_p2_golden_20260630 | mdn_vs_ct | external | 10 | P2 | 2026-06-30 |
| mdn_p2_control_20260630 | mdn_vs_ct | control | 10 | P2 | 2026-06-30 |
| pt_golden_20260701 | pt_vs_ct | external | 10 | P1 | 2026-07-01 |
| pt_control_20260701 | pt_vs_ct | control | 10 | P1 | 2026-07-01 |
| pt_p2_golden_20260701 | pt_vs_ct | external | 10 | P2 | 2026-07-01 |
| pt_p2_control_20260701 | pt_vs_ct | control | 10 | P2 | 2026-07-01 |
| mdn_pt_p1_golden_20260702 | mdn_vs_pt | external | 10 | P1 | 2026-07-02 |
| mdn_pt_p1_control_20260702 | mdn_vs_pt | control | 10 | P1 | 2026-07-02 |
| mdn_pt_p2_golden_20260702 | mdn_vs_pt | external | 10 | P2 | 2026-07-02 |
| mdn_pt_p2_control_20260702 | mdn_vs_pt | control | 10 | P2 | 2026-07-02 |

**Note:** ct_batch_20260629 has no `stance` field in JSON (pre-v3 schema). It is CT vs MdN external, 20 runs (10 golden + 10 control mixed — original experiment before the control condition was separated).

### CFA Claude delivery staging

`experiments/temporal_stability/S7_ARMADA/12_CFA/SYNC_OUT/running/raw_runs/`

| Directory | Contents | Delivered to CFA Claude |
|-----------|----------|------------------------|
| 1/ - 8/ | 10 runs each (original + gnostic batches) | Yes |
| 9_gnostic/ | 150 runs (10 per condition/matchup, 15 folders) | Pending |

---

## Total Run Count

| Category | P1 Runs | P2 Runs | Total |
|----------|---------|---------|-------|
| CT vs MdN (both dirs) | 40 | 40 | 80 |
| CT vs PT (both dirs) | 40 | 40 | 80 |
| MdN vs PT (both dirs) | 41 | 40 | 81 |
| Gnostic (all 6 matchups) | ~181 | ~160 | ~341 |
| Buddhism (8 matchups) | In progress | -- | -- |
| **Total** | **~302** | **~280** | **~582+** |

---

## Outstanding Work

| Item | Status | Notes |
|------|--------|-------|
| Buddhism P1 batch (160 runs) | RUNNING | 8 matchups x 2 cond x 10 runs |
| Buddhism P2 batch | NOT STARTED | Needs P1 results first |
| FRAMEWORK-G experiment (20 runs) | PRE-REGISTERED | `framework_g` stance, 15 rounds, Grant syllogism. See `FRAMEWORK_G_PRE_REGISTRATION.md` |
| Phase 1a Calibration integration | QUEUED | CFA Claude spec finalized, ready to implement in v3 |
| Gnostic care package delivery | READY | `SYNC_OUT/pending/gnostic_full_care_package.md` + `9_gnostic/` |
| ct_batch_20260629 stance field | KNOWN GAP | First 20 runs lack `stance` field (pre-v3 schema) |

---

## Script Registry

| Script | Purpose | Status |
|--------|---------|--------|
| run_cfa_trinity_v3.py | Main Trinity audit engine | Active (v3 metrics, `--max-rounds` and `framework_g` stance added) |
| run_gnostic_batch.py | Gnostic 6-matchup batch runner | Complete |
| run_gnostic_rerun.py | Gnostic gap-fill runner | Complete |
| run_buddhism_batch.py | Buddhism 8-matchup batch runner | Running |

---

*Tracker created: 2026-07-07*
