# Experiments Directory

**Organized structure for all Nyquist Consciousness experimental work**
**Last Updated:** 2025-11-26 (Major reorganization)

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
├── temporal_stability/        # S7 temporal stability experiments ✅ READY
│   ├── s7_meta_loop.py       # Recursive meta-loop orchestrator
│   ├── adaptive_learning_hook.py  # Teaching system
│   ├── curriculum_compressor.py   # Mastery detection
│   ├── convergence_detector.py    # Multi-run analysis
│   ├── ascii_visualizations.py    # Beautiful visualizations
│   ├── s7_config.yaml        # Configuration
│   ├── README.md             # Complete documentation
│   └── IMPLEMENTATION_STATUS.md
│
├── compression_tests/         # All compression/reconstruction fidelity tests
│   ├── compression/          # Phase 3 experiments (formerly phase3/)
│   │   ├── EXPERIMENT_1/     # CFA integration + orchestrator test
│   │   ├── EXPERIMENT_2/     # Compression ablation study
│   │   ├── EXPERIMENT_2B/    # Extended compression study
│   │   ├── EXPERIMENT_3/     # Full system validation
│   │   └── knowledge_load_2025_01/  # Knowledge loading tests
│   ├── domain_trials/        # Domain-specific compression trials
│   ├── identity_gravity_trials/  # Identity gravity experiments
│   ├── phase4/               # Phase 4 experiments
│   ├── phase5/               # Phase 5 experiments
│   ├── phase5_prep/          # Phase 5 preparation
│   ├── phase6/               # Phase 6 experiments
│   └── phase6_prep/          # Phase 6 preparation
│
└── README.md                  # This file

# Archived trials moved to: .archive/trials/
# (SHANNON_BOOT_PROMPT, Trial evaluations, templates)
```

---

## 🎯 Active Experiments

### S7 Temporal Stability (Priority 2)
**Location:** `temporal_stability/`
**Status:** ✅ Implementation complete, ready to run
**Purpose:** Recursive self-improving protocol validating S7 predictions

**Quick Start:**
```bash
cd temporal_stability
python s7_meta_loop.py --config s7_config.yaml
```

**Documentation:** See [temporal_stability/README.md](temporal_stability/README.md)

---

### Compression Tests (S0-S2)
**Location:** `compression_tests/compression/`
**Status:** Multiple experiments completed
**Purpose:** Validate compression fidelity and reconstruction quality

**Quick Start:**
```bash
cd compression_tests/compression/EXPERIMENT_2B
python ../../orchestrator/orchestrator2.py --config experiment2b_config.yaml
```

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

---

**Last Updated:** 2025-11-26
**Status:** Reorganized and ready for S7 execution
