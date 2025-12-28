<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
-->
# Experiments Directory

**Organized structure for all Nyquist Consciousness experimental work**
**Last Updated:** 2025-12-28 (Methodology unified to Cosine EH=0.80)

---

## 📁 Directory Structure

```
experiments/
├── orchestrator/              # Shared orchestration infrastructure
│
├── temporal_stability/        # S7 temporal stability experiments
│   ├── requirements.txt      # Python dependencies
│   ├── README.md             # S7 overview
│   │
│   └── S7_ARMADA/            # ⭐ ACTIVE: Multi-model fleet experiments
│       ├── README.md         # Armada documentation
│       ├── START_HERE.md     # Operations guide
│       │
│       ├── 0_docs/           # Run summaries and specs
│       │   ├── specs/        # 0_RUN_METHODOLOGY.md, 2_PROBE_SPEC.md, etc.
│       │   └── S7_RUN_XXX_SUMMARY.md
│       │
│       ├── 0_results/        # Consolidated JSON results
│       │   ├── runs/         # S7_run_XXX_*.json
│       │   └── temporal_logs/
│       │
│       ├── 11_CONTEXT_DAMPING/  # Phase 4: Run 017-020 experiments
│       │   ├── run017_context_damping.py
│       │   ├── run018_recursive_learnings.py
│       │   ├── run020_tribunal_A.py    # Philosophical Tribunal (A)
│       │   └── run020_tribunal_B.py    # Induced vs Inherent (B)
│       │
│       ├── 12_CFA/              # CFA-ARMADA Integration Pipeline
│       │   └── run_cfa_trinity_v2.py
│       │
│       ├── 13_LOGOS/            # LOGOS Commutation Cartography (Run 022)
│       │   └── run022_commutation_cartography.py
│       │
│       ├── 14_CONSCIOUSNESS/    # Gold/Diamond/Quartz Rush Mining
│       │   ├── run_gold_rush.py
│       │   ├── run_diamond_rush.py
│       │   └── run_quartz_rush.py
│       │
│       ├── 7_META_VALIDATION/   # Measurement validity experiments
│       │   └── EXP_PFI_A_DIMENSIONAL/
│       │
│       └── visualizations/
│           └── visualize_armada.py  # Director script
│
├── compression_tests/         # S0-S6 compression/reconstruction tests
│
└── README.md                  # THIS FILE
```

---

## 🎯 Active Experiments

### ⭐ S7 ARMADA - Multi-Model Fleet (IRON CLAD COMPLETE)

**Location:** `temporal_stability/S7_ARMADA/`
**Status:** Phase 4 IRON CLAD COMPLETE
**Purpose:** Cross-architecture AI identity stability testing

**IRON CLAD Status (December 28, 2025):**

| Run | Files | Valid Results | Status | Methodology |
|-----|-------|---------------|--------|-------------|
| **Run 023d** | 825+ | 825+ | **IRON CLAD** | Cosine (EH=0.80) |
| **Run 018** | 465 | 337 | **52.6%** | Cosine (EH=0.80) |
| **Run 020A** | 33 | ~20 | **50%** | Cosine (EH=0.80) |
| **Run 020B** | 16 | 16 | **COMPLETE** | Cosine (EH=0.80) |

- **Run 022:** READY (LOGOS Commutation Cartography) - methodology FULLY VALIDATED
- **12_CFA:** Coming (Trinity Audit)

**THE THREE CORE CLAIMS — ALL VALIDATED:**

1. **DRIFT IS REAL** — p=2.40e-23 (Run 023d), 88% prediction accuracy
2. **WE DON'T CAUSE IT** — 41% inherent drift ratio (cross-provider)
3. **WE CAN MEASURE IT** — PFI d=0.977, σ²=0.00087 cross-architecture

**Key Discovery: Event Horizon at 0.80 (Cosine Distance)**

- When drift exceeds 0.80, models become VOLATILE (lose coherent self-model)
- **Methodology**: Cosine distance in embedding space (P95 from Run 023d)
- **Calculator**: `1_CALIBRATION/lib/drift_calculator.py`

**Phase 4 (Run 017+):** Uses `i_am_plus_research` context to complete the measurement circuit

**Run History:**

| Run | Ships | Primary Focus | Key Finding |
|-----|-------|---------------|-------------|
| 008 | 29 | Basin Topology | Event Horizon discovered (now calibrated to 0.80) |
| 009 | 42 | Event Horizon | Early threshold validation (superseded by Run 023d) |
| 010 | 45 | Pole Detection | Models articulate own boundaries |
| 011 | 40 | Basin Topology | Control vs Persona A/B (inconclusive) |
| 012 | 20 | Revalidation | 100% EH crossing, 100% recovery, Recovery Paradox |
| 013-016 | - | Various | Boundary Mapping, Rescue Protocol, Stability Criteria, Settling Time |
| **017** | 24 | **Context Damping** | **222 runs, 97.5% stable, oscillatory recovery** |
| **018** | - | **Recursive Learnings** | **Tests fleet hypotheses from Run 017 exit surveys** |
| **019** | - | **Live Ziggy** | **Witness-side anchors validated (3/3 success)** |
| **020A** | - | **Tribunal** | **Good Cop/Bad Cop: 1.351 peak drift, 643-word statement** |
| **020B** | - | **Induced vs Inherent** | **82% drift is INHERENT; probing amplifies but doesn't create** |
| **022** | - | **Commutation Cartography** | **LOGOS algebra validation (13_LOGOS) - DESIGN COMPLETE** |

**Testing Taxonomy (IMPORTANT):**

See [TESTING_MAP.md](../docs/maps/TESTING_MAP.md) for the **Eight Search Types**:

1. **Anchor Detection** — Find identity fixed points (hard challenges)
2. **Adaptive Range Detection** — Find stretch dimensions (moderate)
3. **Event Horizon** — Validate collapse threshold (push past 0.80)
4. **Basin Topology** — Map attractor structure (gentle)
5. **Boundary Mapping** — Explore the 12% anomaly (targeted)
6. **Laplace Pole-Zero Analysis** — Extract system dynamics (post-hoc)
7. **Stability Testing** — Validate metrics predict outcomes (PFI, dimensional drift)
8. **Self-Recognition** — Can AIs recognize their own responses? (bi-directional)

**Key Constraint:** Not all tests are compatible. Anchor Detection and Basin Topology are **mutually exclusive**.

**Quick Start:**

```bash
cd temporal_stability/S7_ARMADA
py -m pip install -r ../requirements.txt

# Generate visualizations for any run
py visualizations/visualize_armada.py --list
py visualizations/visualize_armada.py --run 009
```

**Key Results:** See [S7_ARMADA/docs/maps/TESTING_MAP.md](temporal_stability/S7_ARMADA/docs/maps/TESTING_MAP.md)

---

### EXP-PFI-A: PFI Dimensional Validation

**Location:** `temporal_stability/S7_ARMADA/7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/`
**Status:** COMPLETE (Cohen's d=0.977)
**Purpose:** Test whether PFI measures genuine identity structure vs embedding artifacts

**Result:** Embedding invariance confirmed (Spearman ρ=0.91 across 3 embedding models)

---

### EXP1-SSTACK: Compression Fidelity Benchmark

**Location:** `compression_tests/compression_v2_sstack/EXP1_SSTACK/`
**Status:** PASSED (Mean PFI = 0.852, threshold 0.80)
**Purpose:** Validate T3 seed compression preserves behavioral fidelity

---

### Compression Tests (S0-S6)

**Location:** `compression_tests/`
**Status:** Multiple phases completed
**Purpose:** Validate compression fidelity and reconstruction quality

---

### Identity Gravity Trials (S8)

**Location:** `compression_tests/identity_gravity_trials/`
**Status:** Trials 1-4 completed
**Purpose:** Test identity gravity predictions from S8 spec

---

## 🗂️ Organization Rationale

### compression_tests/

**Why this name:** All experiments testing compression/reconstruction fidelity across S0-S6

**Contains:**

- Phase 3-6 experiments
- Domain trials
- Identity gravity trials
- Legacy phase directories

### Archived Materials

**Location:** `.archive/trials/` (root level, hidden directory)

**Why archived:** Early trial materials superseded by Phase 3+ orchestrated experiments

**Contains:**

- SHANNON_BOOT_PROMPT.md (early template, no longer used)
- Trial 1-3 evaluations (replaced by automated evaluation)
- Evaluation template (reference only)

---

## 🚀 Quick Reference

### Running S7 Experiments

```bash
cd temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING

# Run 018: Recursive Learnings (with exit survey)
py run018_recursive_learnings.py --experiment threshold --dry-run

# Run 020-A: Tribunal Protocol
py run020_tribunal_A.py --arm tribunal-v4 --subjects 1

# Run 020-B: Induced vs Inherent (Control vs Treatment)
py run020_tribunal_B.py --arm both --subjects 5
```

### Running Compression Tests

```bash
cd compression_tests/compression/EXPERIMENT_2B
python ../../orchestrator/orchestrator2.py --config experiment2b_config.yaml
```

### Generating Visualizations

```bash
cd temporal_stability/S7_ARMADA/visualizations
py visualize_armada.py --list
py visualize_armada.py --run 017
```

---

## 📋 Reorganization Summary (2025-11-26)

**Cleaned up:**

- ✅ Created `compression_tests/` directory
- ✅ Moved all phase directories and trials into `compression_tests/`
- ✅ Created `.archive/trials/` at root level
- ✅ Moved SHANNON_BOOT_PROMPT + Trial files to `.archive/trials/`
- ✅ Updated documentation to reflect new structure

**Benefits:**

- Clearer semantic organization
- Separates active work from archived materials
- Groups related compression experiments
- Archives hidden from regular navigation (dotfile)
- Maintains backward compatibility (files not deleted, just moved)

---

## 🔗 Related Documentation

- **[docs/maps/TESTABLE_PREDICTIONS_MATRIX.md](../docs/maps/TESTABLE_PREDICTIONS_MATRIX.md)** - All testable predictions (including P-018-*)
- **[docs/maps/TESTING_MAP.md](../docs/maps/TESTING_MAP.md)** - Eight Search Types taxonomy
- **[S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md](temporal_stability/S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md)** - Run design checklist
- **[S7_ARMADA/0_docs/specs/2_PROBE_SPEC.md](temporal_stability/S7_ARMADA/0_docs/specs/2_PROBE_SPEC.md)** - SONAR + Brute-Criterial probe taxonomy

---

**Last Updated:** 2025-12-28
**Status:** Run 023d IRON CLAD. Methodology unified to Cosine (EH=0.80). Run 022 READY, 12_CFA COMING
