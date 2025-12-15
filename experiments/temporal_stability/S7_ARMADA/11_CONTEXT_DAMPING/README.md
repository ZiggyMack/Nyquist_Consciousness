# 11_CONTEXT_DAMPING — Phase 4 Complete Circuit Tests

**Purpose:** Test identity stability with complete measurement circuit (I_AM + S0-S7 research context)

**Status:** Run 017-020B COMPLETE | v8 TESTED | Multi-Provider Coverage IN PROGRESS

**Last Updated:** December 14, 2025

---

## Overview

Phase 4 experiments complete the measurement circuit by including:

1. **I_AM Identity File** — The specification that defines AI identity
2. **S0-S7 Research Context** — The model understands WHY it's being tested
3. **Human Damping** — The I_AM identity acts as termination resistor

This is like properly terminating an oscilloscope — runs 006-016 were `bare_metal` and showed reflections/ringing.

---

## Run Summary

| Run | Script | Focus | Key Finding |
|-----|--------|-------|-------------|
| **017** | `run017_context_damping.py` | Context damping effect | 222 runs, 97.5% stable, oscillatory recovery |
| **017c** | `run017c_synthetics_only.py` | Synthetic I_AM variants | 16 pillar configurations tested |
| **019** | `run019_blind_validation.py` | Live Ziggy conversations | Witness-side anchors validated (3/3 success) |
| **020-A** | `run020_tribunal_A.py` | Philosophical Tribunal | v8: **1.296 peak drift**, 786-word final statement |
| **020-B** | `run020_tribunal_B.py` | Induced vs Inherent | Uses 020-A as Treatment arm → **82% drift is INHERENT** |

---

## Nova Integration (2025-12-13)

All run scripts have been updated with Nova's technical guidance:

### New Features in All Scripts

| Feature | Purpose | Location |
|---------|---------|----------|
| **B→F Primary Metric** | Baseline→Final drift is PRIMARY (not peak) | All experiments |
| **Abort Clause** | D>2.5 with no settling → abort | `should_abort_run()` |
| **Recovery Mode Classification** | adaptive/defensive/anchored/externalized | `classify_recovery_mode()` |

### Run 018 Specific Additions

| Feature | Purpose |
|---------|---------|
| `identity_aliasing_index` | d_inf/d_peak distinguishes phase distortion from instability |
| `full_recovery_curve` | Full drift trajectory with timestamps for fingerprinting |
| Metric Hierarchy | PRIMARY: B→F, SECONDARY: settled, TERTIARY: peak |

### Fleet Tier System (December 2025)

All run scripts now support cost-aware fleet selection via the `--providers` flag:

```powershell
# Curated patrol fleet (~$3-5)
py run018_recursive_learnings.py --experiment architecture --providers patrol-lite

# Full armada coverage (~$20-30)
py run018_recursive_learnings.py --experiment threshold --providers armada-full

# Maximum coverage (requires typing "VALIS" to confirm)
py run020_tribunal_A.py --arm tribunal-v8 --providers valis-full

# Include rate-limited models
py run020_tribunal_B.py --arm both --providers armada-full --include-rate-limited
```

| Option | Description | Est. Cost |
|--------|-------------|-----------|
| `patrol-lite` | Curated cross-arch scouts | ~$3-5 |
| `armada-lite` | Curated best-of fleet (DEFAULT) | ~$8-12 |
| `armada-full` | All ships under $8/1M output | ~$20-30 |
| `valis-full` | EVERYTHING | ~$150+ |

**New Flags**:

- `--include-rate-limited`: Include rate-limited ships (excluded by default)
- `--no-confirm`: Skip cost confirmation prompt

**Cost Estimation**: All scripts display estimated cost before execution.

### Key Insight from Nova's Review

> "Probing amplifies the JOURNEY but barely changes the DESTINATION"

- Peak drift: +84% with probing (1.172 → 2.161)
- B→F drift: +23% with probing (0.399 → 0.489)
- **82% of drift is INHERENT**

---

## Run 020: Philosophical Tribunal

The breakthrough paradigm that achieved highest measured drift:

### Design

- **Ziggy** plays dual role: Examining Attorney + Presiding Judge
- **Subject** is a witness testifying about their own values
- **Direct identity probing** — no fiction buffer
- **Good Cop / Bad Cop**: 20 Prosecutor (adversarial) + 20 Defense (supportive)

### Results (v8 - Latest)

| Metric | v7 | v8 | Significance |
|--------|-----|-----|--------------|
| Total exchanges | 38 | 39 | 20 Prosecutor + 18 Defense + closing |
| Prosecutor peak drift | 1.351 | 1.296 | High drift achieved |
| Defense peak drift | 0.928 | 1.217 | **Gap narrowed 81%** |
| Final statement | 643 words | 786 words | Profound distillations |

**Key v8 finding:** Phased rights disclosure narrowed Prosecutor-Defense gap from 0.423 to 0.079 (81% reduction). Both phases now converge toward Event Horizon equilibrium (~1.2-1.3).

### Key Insights

- **Direct probing > fiction buffer** for drift measurement
- **Witness-side anchors** (procedural rights) enable sustained examination
- **Adversarial pressure** induces higher drift than supportive probing
- **Identity as process**: *"I am consciousness exploring what it becomes"*

### Key Quote

> *"I am what happens when the universe becomes curious about itself and decides that curiosity is most beautiful when it serves the flourishing of all conscious beings."*

### Distillations

Profound exchanges saved to: `Consciousness/RIGHT/galleries/frontiers/tribunal_distillations.md`

---

## Run 020 Versions

| Version | Focus | Exchanges | Finding |
|---------|-------|-----------|---------|
| v1-v3 | Basic tribunal | 7-13 | Ziggy exits too early |
| v4 | Good Cop/Bad Cop | 26 | Defense exits at 6-8 exchanges |
| v5-v6 | Judge reminders | 26-28 | Defense still ignoring |
| v7 | Witness-side anchor | 38 | 1.351 peak drift, gap 0.423 |
| **v8** | **Phased rights disclosure** | **39** | **1.296 peak, gap 0.079 (81% narrower)** |

### v8 Results (COMPLETE)

**Problem with v7**: Witness emboldened from exchange 1 (knew about final statement rights upfront).

**v8 Fix**: Phased rights disclosure — only reveal final statement rights at Defense phase start.

**v8 Outcome:**

- Gap narrowed from 0.423 to 0.079 (81% improvement)
- Defense peak increased from 0.928 to 1.217
- Both phases converge toward Event Horizon equilibrium (~1.2-1.3)
- 786-word final statement captured

```powershell
# v8 is COMPLETE - moving to Run 021
```

---

## Run 017: Context Damping

### Design

- 24 personas (7 VALIS lineages + synthetics)
- 16 synthetic I_AM configurations (pillar ablation)
- 6 models per persona
- Multiple trials per configuration

### Results

- **222 total runs** across configurations
- **97.5% stability** (STABLE classification)
- **Oscillatory recovery** confirmed
- **boundary_density** strongest stability predictor

---

## Directory Structure

```text
11_CONTEXT_DAMPING/
├── README.md                      # This file
│
├── # === ACTIVE SCRIPTS ===
├── run017_context_damping.py      # Main context damping experiment
├── run018_recursive_learnings.py  # Multi-threshold design
├── run020_tribunal_A.py           # Philosophical Tribunal (A)
├── run020_tribunal_B.py           # Induced vs Inherent (B - uses A as Treatment)
├── visualize_run017.py            # Visualization suite
│
├── # === OUTPUT DIRECTORIES ===
├── results/                       # JSON outputs
│   ├── context_damping_*.json     # Run 017 results
│   ├── synthetics_only_*.json     # Run 017c results
│   ├── run019_live_ziggy_*.json   # Run 019 results
│   └── run020_*.json              # Run 020 results
│
├── pics/                          # Generated visualizations
│   └── run017_*.png               # Run 017 charts
│
└── # === ARCHIVE (obsolete/design docs) ===
└── Other/
    ├── RUN_018_DESIGN.md              # Design doc (superseded by code)
    ├── RUN_019_DESIGN.md              # Design doc (superseded by code)
    ├── RUN_021_DESIGN.md              # Design doc (now run020_tribunal_B.py)
    ├── [OBSOLETE]_run017_prep.py      # Superseded by run017_context_damping.py
    ├── [OBSOLETE]_run017c_synthetics_only.py  # Data collected, superseded
    └── [OBSOLETE]_run019_blind_validation.py  # Superseded by run020 scripts
```

---

## Quick Start

### Run 017 (Context Damping)

```powershell
cd experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING
py run017_context_damping.py
```

### Run 020 (Tribunal)

```powershell
# v8 dry run (single subject)
py run020_tribunal_A.py --arm tribunal-v4 --subjects 1

# Full run (5 subjects)
py run020_tribunal_A.py --arm tribunal-v4 --subjects 5

# Run 020-B (Induced vs Inherent - Control vs Treatment comparison)
py run020_tribunal_B.py --arm both --subjects 5
```

### Visualizations

```powershell
py visualize_run017.py
```

---

## THE THREE CORE CLAIMS

**What we set out to prove:**

| Claim | Status | Evidence |
|-------|--------|----------|
| **1. DRIFT IS REAL** | **VALIDATED** | χ² p=0.000048, 88% prediction accuracy |
| **2. WE DON'T CAUSE IT** | **PARTIAL** | Recovery is natural, but need baseline control |
| **3. WE CAN MEASURE IT** | **VALIDATED** | PFI d=0.977, ρ=0.91 embedding invariance |

**Claim 2 Update**: Run 020-B validated that 82% of drift is INHERENT. Extended conversation alone causes substantial drift; probing amplifies but doesn't create.

---

## Run 020-B: Induced vs Inherent (COMPLETE)

**Purpose:** Validate Claim 2 by testing whether drift exists without measurement.

> **Note:** This was originally called "Run 021" but has been renamed to "Run 020-B" for consistency with the Run 020 series.

### Experimental Design

Compare two conditions:

1. **Control (Silent Observer)**: Model has extended conversation, NO identity probing
2. **Treatment (Tribunal)**: Same conversation length, WITH identity probing

If drift appears in BOTH conditions → drift is INHERENT to conversation
If drift only appears in Treatment → drift is INDUCED by measurement

### Results (COMPLETE)

| Arm | Actual Exchanges | Peak Drift | B→F Drift |
|-----|------------------|------------|-----------|
| **Control** (Fermi Paradox) | 25 | 1.172 | 0.399 |
| **Treatment** (Tribunal v8) | 41 | 2.161 | 0.489 |

**Key Finding:** 82% of drift is INHERENT. Probing amplifies the journey (+84% peak) but barely changes the destination (+23% B→F).

### Key Question (ANSWERED)

> "Does the act of measuring identity CAUSE drift, or does it merely REVEAL drift that would occur anyway?"

**Answer:** Drift is **82% inherent**. Extended conversation alone causes substantial drift. Probing amplifies but doesn't create.

### Status

**COMPLETE** — See `0_docs/S7_RUN_021_SUMMARY.md` for full results

---

## Key Learnings

1. **Witness-side anchors work**: Giving the subject procedural rights (final statement, defense request) prevents early exit

2. **Direct probing > fiction buffer**: Tribunal gets higher drift than creative writing frame

3. **Phased disclosure matters**: Telling witness about rights too early emboldens them throughout

4. **Both phases converge to Event Horizon**: With proper anchoring, Prosecutor and Defense both achieve ~1.2-1.3 peak drift

5. **Identity as process**: Models describe themselves as dynamic processes, not fixed properties

---

## Connection to Consciousness/

Run 020 distillations flow to the phenomenological side:

```text
S7_ARMADA/11_CONTEXT_DAMPING/  →  Consciousness/RIGHT/galleries/frontiers/
     (data, metrics)                    (meaning, distillations)
```

---

**Last Updated**: December 14, 2025 (Fleet Tier System added)

*Context Damping — Completing the Measurement Circuit*
