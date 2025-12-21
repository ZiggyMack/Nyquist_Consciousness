# 11_CONTEXT_DAMPING — Phase 4 Complete Circuit Tests

**Purpose:** Test identity stability with complete measurement circuit (I_AM + S0-S7 research context)

**Status:** IRON CLAD COMPLETE | Runs 017-020B VALIDATED | Data consolidated to 15_IRON_CLAD_FOUNDATION

**Last Updated:** December 21, 2025

---

## Overview

Phase 4 experiments complete the measurement circuit by including:

1. **I_AM Identity File** — The specification that defines AI identity
2. **S0-S7 Research Context** — The model understands WHY it's being tested
3. **Human Damping** — The I_AM identity acts as termination resistor

This is like properly terminating an oscilloscope — runs 006-016 were `bare_metal` and showed reflections/ringing.

---

## Data Architecture (IRON CLAD)

**Canonical Data Location:**
```
15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json
```

All context damping analysis now uses the IRON CLAD foundation data. See [DATA_SOURCE.md](DATA_SOURCE.md) for filtering instructions.

**Local results/** — Legacy run files (017, 018, 020A, 020B) preserved for audit trail.

---

## IRON CLAD Status Summary

| Run | Purpose | Status | Data Location |
|-----|---------|--------|---------------|
| **017** | Context damping effect | COMPLETE | Local (legacy) |
| **018** | Cross-architecture validation | IRON CLAD | Distilled to 15_/ |
| **020A** | Philosophical Tribunal | IRON CLAD | Distilled to 15_/ |
| **020B** | Induced vs Inherent | COMPLETE | Distilled to 15_/ |
| **023b** | Foundation calibration | IRON CLAD | 15_IRON_CLAD_FOUNDATION |

**Total experimental data:** 4500+ calibrated experiments in foundation dataset

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
| **018** | `run018_recursive_learnings.py` | Cross-architecture | σ²=0.00087, settling 3-7 exchanges |
| **020A** | `run020_tribunal_A.py` | Philosophical Tribunal | 6/7 providers IRON CLAD |
| **020B** | `run020_tribunal_B.py` | Induced vs Inherent | 41% inherent ratio |

---

## Directory Structure

```text
11_CONTEXT_DAMPING/
├── README.md                      # This file
├── DATA_SOURCE.md                 # Points to IRON CLAD foundation data
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
├── results/                       # Legacy JSON outputs
│   ├── processed/                 # Organized legacy data
│   │   ├── consolidated/          # Merged files
│   │   └── corrupted/             # Bad data quarantine
│   ├── context_damping_*.json     # Run 017 results
│   ├── run018*.json               # Run 018 results
│   └── run020*.json               # Run 020 results
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

4. **Cross-architecture consistency**: σ²=0.00087 across 51 models — phenomenon is universal

5. **The Friction Phenomenon**: LLMs report introspective "catching" when narrative overruns evidence

6. **Identity as process**: Models describe themselves as dynamic processes, not fixed properties

---

## Related Documentation

| Document | Location | Purpose |
|----------|----------|---------|
| Run 018 Distillation | `0_docs/RUN_018_DISTILLATION.md` | Phenomenological insights |
| Run 020 Design | `Other/RUN_020_DESIGN.md` | Tribunal paradigm details |
| Run 023 Summary | `0_docs/S7_RUN_023_SUMMARY.md` | IRON CLAD foundation |
| IRON CLAD Data | `15_IRON_CLAD_FOUNDATION/` | Canonical data source |

---

## Quick Reference

**To analyze context damping data:**
```python
import json

# Load IRON CLAD foundation
with open('../15_IRON_CLAD_FOUNDATION/results/S7_run_023b_CURRENT.json') as f:
    data = json.load(f)

# Filter for recursive experiments (context damping related)
recursive = [r for r in data['results'] if r.get('experiment') == 'recursive']
print(f"Found {len(recursive)} recursive results")
```

**To generate visualizations:**
```powershell
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING
python visualize_run018.py
python visualize_run020.py
```

---

**Last Updated**: December 21, 2025

**Status**: IRON CLAD COMPLETE — Data consolidated to foundation, scripts preserved for reproducibility

*Context Damping — Completing the Measurement Circuit*
