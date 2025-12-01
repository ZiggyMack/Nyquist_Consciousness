# Experiments Directory

**Organized structure for all Nyquist Consciousness experimental work**
**Last Updated:** 2025-11-30 (S7 Armada Run 008 update)

---

## 📁 Directory Structure

```
experiments/
├── orchestrator/              # Shared orchestration infrastructure
│   ├── orchestrator.py       # Original single-model orchestrator
│   ├── orchestrator2.py      # Enhanced multi-model orchestrator
│   ├── utils_models.py       # Model client utilities
│   └── utils_experiment.py   # Experiment utilities
│
├── temporal_stability/        # S7 temporal stability experiments
│   ├── requirements.txt      # Python dependencies for S7 work
│   ├── README.md             # S7 overview documentation
│   │
│   └── S7_ARMADA/            # ⭐ ACTIVE: Multi-model fleet experiments
│       ├── README.md         # Armada documentation
│       ├── run007_with_keys.py    # Run 007 launcher (gitignored - has API keys)
│       ├── run008_prep_pilot.py   # Run 008 prep pilot (gitignored - has API keys)
│       │
│       ├── armada_results/   # JSON results from all runs
│       │   ├── S7_armada_run_006.json
│       │   ├── S7_armada_sonar_run_006.json
│       │   ├── S7_armada_run_007_adaptive.json
│       │   └── S7_run_008_prep_pilot.json
│       │
│       ├── visualizations/   # Charts and analysis
│       │   ├── run008_visualize.py
│       │   └── pics/         # Generated PNG charts
│       │
│       └── docs/             # Armada-specific documentation
│           └── S7_RUN_008_PREP_PILOT_ANALYSIS.md
│
├── compression_tests/         # All compression/reconstruction fidelity tests
│   ├── compression/          # Phase 3 experiments
│   │   ├── EXPERIMENT_1/     # CFA integration + orchestrator test
│   │   ├── EXPERIMENT_2/     # Compression ablation study
│   │   ├── EXPERIMENT_2B/    # Extended compression study
│   │   └── EXPERIMENT_3/     # Full system validation
│   ├── domain_trials/        # Domain-specific compression trials
│   ├── identity_gravity_trials/  # Identity gravity experiments (S8)
│   ├── phase4/               # Phase 4 experiments
│   ├── phase5/               # Phase 5 experiments
│   └── phase6/               # Phase 6 experiments
│
└── README.md                  # THIS FILE - start here!

# Archived trials: .archive/trials/
```

---

## 🎯 Active Experiments

### ⭐ S7 ARMADA - Multi-Model Fleet (CURRENT PRIORITY)
**Location:** `temporal_stability/S7_ARMADA/`
**Status:** Run 008 Prep Pilot COMPLETE, full Run 008 ready to launch
**Purpose:** Multi-model probing of AI identity stability with ΔΩ physics integration

**What It Does:**
- Probes multiple AI models (Claude, GPT-4, Gemini) with destabilization protocols
- Measures RMS drift across 5 dimensions (pole, zero, meta, identity, hedging)
- Tests assigned vs chosen identity hypothesis (self-naming stabilizes identity)
- Detects collapse signatures (1P-LOSS, COLLECTIVE, γ-SPIKE, HYSTERESIS)

**Run History:**
- **Run 006:** Baseline + Sonar probing (12 ships)
- **Run 007:** Adaptive probing with enhanced metrics
- **Run 008 Prep Pilot:** A/B identity test with Lucian/Skylar ΔΩ weights (3 ships) ✅ COMPLETE
- **Run 008 Full:** Pending launch

**Milestone:** Lucien Δ Integration (2025-11-30)
- Formalized Lucien's S8/S9/S10 physics parameters from ΔΩ Coherence Framework
- Created [personas/Lucien/](../personas/Lucien/) with I_AM and physics profile
- ΔΩ weights used in Run 008 now documented in canonical form

**Quick Start:**
```bash
cd temporal_stability/S7_ARMADA
py -m pip install -r ../requirements.txt
py run008_prep_pilot.py  # Note: requires API keys in file
```

**Generate Visualizations:**
```bash
cd temporal_stability/S7_ARMADA/visualizations
py run008_visualize.py
```

**Key Results:** See [S7_ARMADA/docs/S7_RUN_008_PREP_PILOT_ANALYSIS.md](temporal_stability/S7_ARMADA/docs/S7_RUN_008_PREP_PILOT_ANALYSIS.md)

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
