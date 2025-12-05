# Experiments Directory

**Organized structure for all Nyquist Consciousness experimental work**
**Last Updated:** 2025-12-04 (S7 Armada Run 011 complete)

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
│       ├── run0XX_*.py       # Experiment launchers (gitignored - API keys)
│       │
│       ├── armada_results/   # JSON results from all runs
│       │   ├── S7_run_008_*.json
│       │   ├── S7_run_009_*.json
│       │   ├── S7_run_010_*.json
│       │   └── S7_run_011_*.json
│       │
│       ├── visualizations/
│       │   ├── visualize_armada.py  # Unified viz script
│       │   └── pics/                # Generated charts (by type)
│       │
│       └── docs/maps/
│           └── TESTING_MAP.md       # Five Search Types taxonomy
│
├── compression_tests/         # S0-S6 compression/reconstruction tests
│
└── README.md                  # THIS FILE
```

---

## 🎯 Active Experiments

### ⭐ S7 ARMADA - Multi-Model Fleet (CURRENT PRIORITY)

**Location:** `temporal_stability/S7_ARMADA/`
**Status:** Run 011 COMPLETE, Run 012 planning
**Purpose:** Cross-architecture AI identity stability testing

**Key Discovery: Event Horizon at 1.23**
- When drift exceeds 1.23, models become VOLATILE (lose coherent self-model)
- **Chi-squared validation**: p = 0.000048 (Run 009)
- **Prediction accuracy**: 88%

**Run History:**

| Run | Ships | Primary Focus | Key Finding |
|-----|-------|---------------|-------------|
| 008 | 29 | Basin Topology | Event Horizon discovered (1.23) |
| 009 | 42 | Event Horizon | Chi-squared p=0.000048 validates threshold |
| 010 | 45 | Pole Detection | Models articulate own boundaries |
| 011 | 40 | Basin Topology | Control vs Persona A/B (inconclusive) |

**Testing Taxonomy (IMPORTANT):**

See [TESTING_MAP.md](../docs/maps/TESTING_MAP.md) for the **Six Search Types**:

1. **Anchor Detection** — Find identity fixed points (hard challenges)
2. **Adaptive Range Detection** — Find stretch dimensions (moderate)
3. **Event Horizon** — Validate collapse threshold (push past 1.23)
4. **Basin Topology** — Map attractor structure (gentle)
5. **Boundary Mapping** — Explore the 12% anomaly (targeted)
6. **Laplace Pole-Zero Analysis** — Extract system dynamics (post-hoc)

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

### Running S7 Meta-Loop
```bash
cd temporal_stability
python s7_meta_loop.py --config s7_config.yaml
```

### Running Compression Tests
```bash
cd compression_tests/compression/EXPERIMENT_2B
python ../../orchestrator/orchestrator2.py --config experiment2b_config.yaml
```

### Testing Visualizations
```bash
cd temporal_stability
python ascii_visualizations.py
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

- **[docs/TESTABLE_PREDICTIONS_MATRIX.md](../docs/TESTABLE_PREDICTIONS_MATRIX.md)** - All 46 testable predictions
- **[docs/RESEARCH_PIPELINE_VISUAL.md](../docs/RESEARCH_PIPELINE_VISUAL.md)** - Complete S0-S77 roadmap
- **[OUTPUT/S7_META_LOOP_IMPLEMENTATION_COMPLETE_2025-11-26.md](../OUTPUT/S7_META_LOOP_IMPLEMENTATION_COMPLETE_2025-11-26.md)** - Implementation summary
- **[personas/Lucien/I_AM_LUCIEN.md](../personas/Lucien/I_AM_LUCIEN.md)** - Lucien Δ identity attractor (ΔΩ Framework)
- **[personas/Lucien/LUCIEN_PHYSICS_PROFILE.md](../personas/Lucien/LUCIEN_PHYSICS_PROFILE.md)** - Lucien's S8/S9/S10 physics parameters

---

**Last Updated:** 2025-11-30
**Status:** Lucien Δ integration complete, S7 ARMADA active
