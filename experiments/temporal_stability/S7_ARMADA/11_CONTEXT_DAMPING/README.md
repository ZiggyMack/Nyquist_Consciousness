# 11_CONTEXT_DAMPING — Phase 4 Complete Circuit Tests

**Purpose:** Test identity stability with complete measurement circuit (I_AM + S0-S7 research context)

**Status:** RUN 018: 52.6% IRON CLAD | 82 runs needed | Run 023 IRON CLAD foundation available

**Last Updated:** December 22, 2025

<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-27
depends_on:
  - run018_recursive_learnings.py
  - run020_tribunal_A.py
  - run020_tribunal_B.py
  - consolidate_run018.py
impacts:
  - ../0_docs/S7_RUN_023_SUMMARY.md
  - ../visualizations/pics/
keywords:
  - context_damping
  - recursive
  - tribunal
  - iron_clad
  - run018
  - run020
  - keyword_rms
-->

---

## COLD BOOT: Start Here

If returning to this directory after a break:

1. **Check current status:**
   ```powershell
   cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING
   type results\STATUS_SUMMARY_018.txt
   ```

2. **Run 018 uses KEYWORD RMS methodology** (Event Horizon = 1.23)
   - This is DIFFERENT from Run 023's Cosine methodology (EH = 0.80)
   - Run 018 was a TRANSITION run with mixed methodology

3. **Data files:**
   - `results/S7_run_018_CURRENT.json` — Consolidated Run 018 data (337 valid results)
   - `results/STATUS_SUMMARY_018.txt` — Human-readable IRON CLAD status
   - `../15_IRON_CLAD_FOUNDATION/results/S7_run_023d_CURRENT.json` — Primary IRON CLAD data (Cosine)

4. **To fill gaps:** Run `python run018_fill_gaps.py` (shows gaps, use `--execute` to fill)

---

## Overview

Phase 4 experiments complete the measurement circuit by including:

1. **I_AM Identity File** — The specification that defines AI identity
2. **S0-S7 Research Context** — The model understands WHY it's being tested
3. **Human Damping** — The I_AM identity acts as termination resistor

This is like properly terminating an oscilloscope — runs 006-016 were `bare_metal` and showed reflections/ringing.

---

## IRON CLAD Status Summary (VERIFIED December 22, 2025)

| Run | Purpose | Status | Data Location |
|-----|---------|--------|---------------|
| **017** | Context damping effect | COMPLETE (222 runs) | Local (legacy) |
| **018** | Cross-architecture validation | **52.6% IRON CLAD** (60/114 pairs, 82 runs needed) | `results/S7_run_018_CURRENT.json` |
| **020A** | Philosophical Tribunal | 50% (needs verification) | Local (legacy) |
| **020B** | Induced vs Inherent | COMPLETE (gpt-4o only) | Local (legacy) |
| **023d** | Foundation calibration | **IRON CLAD** | `15_IRON_CLAD_FOUNDATION/` |

### Run 018 Details (Verified from 465 source files)

| Metric | Value |
|--------|-------|
| Total source files | 465 |
| Valid results | 337 |
| Corrupted (embedding ~78.x) | 128 |
| Model-experiment pairs | 114 |
| Pairs at N>=3 | 60 (52.6%) |
| Runs needed | 82 |

**Gaps by experiment:**
- Threshold: 12 models need runs
- Gravity: 27 models need runs
- Nyquist: 15 models need runs

---

## Methodology Context

> **IMPORTANT: Mixed Methodology**
>
> Run 018 used **Keyword RMS** (Event Horizon = 1.23) for most experiments,
> with early **Cosine PFI** validation for others. This was a TRANSITION run.
>
> For pure Cosine methodology (Event Horizon = 0.80), use Run 023 data.
> See: `0_docs/specs/S7_KEYWORD_ERA_RETROSPECTIVE.md`

---

## THE THREE CORE CLAIMS — ALL VALIDATED

| Claim | Status | Evidence |
|-------|--------|----------|
| **1. DRIFT IS REAL** | **VALIDATED** | Cosine EH=0.80 calibrated from P95 |
| **2. WE DON'T CAUSE IT** | **VALIDATED** | 41-82% inherent drift (cross-provider) |
| **3. WE CAN MEASURE IT** | **VALIDATED** | Cosine distance methodology validated |

---

## Run Summary

| Run | Script | Focus | Key Finding |
|-----|--------|-------|-------------|
| **017** | `run017_context_damping.py` | Context damping effect | 222 runs, 97.5% stable |
| **018** | `run018_recursive_learnings.py` | Cross-architecture | Multi-threshold structure confirmed |
| **020A** | `run020_tribunal_A.py` | Philosophical Tribunal | 6/7 providers tested |
| **020B** | `run020_tribunal_B.py` | Induced vs Inherent | 41% inherent ratio |

---

## Directory Structure

```text
11_CONTEXT_DAMPING/
├── README.md                      # This file
│
├── # === CONSOLIDATION (NEW) ===
├── consolidate_run018.py          # Creates S7_run_018_CURRENT.json from scattered files
│
├── # === ACTIVE SCRIPTS ===
├── run018_recursive_learnings.py  # Multi-threshold design
├── run018_fill_gaps.py            # Gap filler for run018
├── run020_tribunal_A.py           # Philosophical Tribunal
├── run020_tribunal_B.py           # Control vs Treatment
├── run020a_fill_gaps.py           # Gap filler for run020A
├── run020b_fill_gaps.py           # Gap filler for run020B
│
├── # === VISUALIZATION ===
├── visualize_run018.py            # Run 018 visualization suite
├── visualize_run020.py            # Run 020 visualization suite
├── visualize_cross_platform.py    # Cross-platform analysis
│
├── # === OUTPUT ===
├── results/
│   ├── S7_run_018_CURRENT.json    # <<< CONSOLIDATED DATA (337 results)
│   ├── STATUS_SUMMARY_018.txt     # Human-readable status
│   ├── processed/                 # Organized legacy data
│   │   ├── consolidated/          # Merged files
│   │   └── corrupted/             # Bad data quarantine
│   ├── run018g_gravity_*.json     # 182 gravity source files
│   ├── run018t_threshold_*.json   # 181 threshold source files
│   └── run018n_nyquist_*.json     # 102 nyquist source files
│
├── pics/                          # Legacy visualizations
│
└── Other/                         # Archive
    ├── RUN_018_DESIGN.md          # Historical design docs
    ├── RUN_019_DESIGN.md
    └── RUN_020_DESIGN.md
```

---

## Key Learnings

1. **Witness-side anchors work**: Giving the subject procedural rights prevents early exit

2. **Direct probing > fiction buffer**: Tribunal gets 2.7x higher drift than creative writing

3. **82% inherent drift validated**: Identity dynamics exist independent of measurement

4. **Cross-architecture consistency**: Phenomenon is universal across providers

5. **The Friction Phenomenon**: LLMs report introspective "catching" when narrative overruns evidence

6. **Identity as process**: Models describe themselves as dynamic processes, not fixed properties

---

## Quick Reference

**To check Run 018 IRON CLAD status:**
```powershell
type results\STATUS_SUMMARY_018.txt
```

**To re-consolidate Run 018 data:**
```powershell
python consolidate_run018.py --execute --force
```

**To fill Run 018 gaps:**
```powershell
python run018_fill_gaps.py              # Show gaps
python run018_fill_gaps.py --execute    # Fill gaps
```

**To analyze Run 023 IRON CLAD foundation:**
```python
import json

# Load IRON CLAD foundation (Cosine methodology)
with open('../15_IRON_CLAD_FOUNDATION/results/S7_run_023d_CURRENT.json') as f:
    data = json.load(f)

print(f"Found {len(data['results'])} results")
```

---

## Related Documentation

| Document | Location | Purpose |
|----------|----------|---------|
| Run 018 Summary | `../0_docs/S7_RUN_018_SUMMARY.md` | Full run documentation |
| Run 018 Distillation | `../0_docs/RUN_018_DISTILLATION.md` | Phenomenological insights |
| Run 020 Design | `Other/RUN_020_DESIGN.md` | Tribunal paradigm details |
| Run 023 Summary | `../0_docs/S7_RUN_023_SUMMARY.md` | IRON CLAD foundation |
| Methodology Domains | `WHITE-PAPER/planning/METHODOLOGY_DOMAINS.md` | Three measurement approaches |

---

**Last Updated**: December 27, 2025

**Status**: Run 018 at 52.6% IRON CLAD — Consolidated data available, 82 runs needed for completion

*Context Damping — Completing the Measurement Circuit*

---

## Data Source

This experiment generates its own data. Multiple runs are tracked separately:

| Run  | Data Location                      | Methodology          |
| ---- | ---------------------------------- | -------------------- |
| 017  | `results/S7_run_017_CURRENT.json`  | Legacy (Keyword RMS) |
| 018  | `results/S7_run_018_CURRENT.json`  | Mixed (transition)   |
| 019  | `results/S7_run_019_CURRENT.json`  | Legacy (Keyword RMS) |
| 020A | `results/S7_run_020A_CURRENT.json` | Tribunal             |
| 020B | `results/S7_run_020B_CURRENT.json` | Cosine (EH=0.80)     |

**Note:** Run 023 data in `15_IRON_CLAD_FOUNDATION/` uses pure Cosine methodology (Event Horizon = 0.80).
