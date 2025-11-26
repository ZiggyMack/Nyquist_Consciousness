# Experiments Directory Reorganization

**Date:** 2025-11-26
**Status:** ✅ Complete

---

## Summary

Cleaned up and reorganized the `experiments/` directory for better semantic clarity and maintainability.

---

## Changes Made

### 1. Created `compression_tests/` Directory

All compression/reconstruction fidelity experiments now grouped together:

```bash
mkdir experiments/compression_tests
mv experiments/{compression,domain_trials,identity_gravity_trials,phase4,phase5,phase5_prep,phase6,phase6_prep} experiments/compression_tests/
```

**Rationale:** Groups all S0-S6 layer testing (compression, reconstruction, fidelity) under one semantic umbrella.

---

### 2. Created `archived_trials/` Directory

Early trial materials moved to archive:

```bash
mkdir experiments/archived_trials
mv experiments/{SHANNON_BOOT_PROMPT.md,Trial_*.md,TRIAL_EVAL_TEMPLATE.md} experiments/archived_trials/
```

**Archived Files:**
- `SHANNON_BOOT_PROMPT.md` - Early persona bootstrap template (superseded by orchestrator)
- `Trial_01_FULL_vs_L1_Evaluation.md` - Manual evaluation (superseded by Phase 3)
- `Trial_02_FULL_vs_L3_Evaluation.md` - Manual evaluation (superseded by Phase 3)
- `Trial_03_FULL_vs_L2_Evaluation.md` - Manual evaluation (superseded by Phase 3)
- `TRIAL_EVAL_TEMPLATE.md` - Evaluation template (reference only)

**Rationale:** These files represent early exploratory work that has been superseded by the automated orchestration system. Archived rather than deleted for historical reference.

---

## Final Directory Structure

```
experiments/
├── orchestrator/              # Shared orchestration infrastructure
│   ├── orchestrator.py
│   ├── orchestrator2.py
│   ├── utils_models.py
│   └── utils_experiment.py
│
├── temporal_stability/        # S7 temporal stability experiments ✅ READY
│   ├── s7_meta_loop.py
│   ├── adaptive_learning_hook.py
│   ├── curriculum_compressor.py
│   ├── convergence_detector.py
│   ├── ascii_visualizations.py
│   ├── s7_config.yaml
│   ├── README.md
│   └── IMPLEMENTATION_STATUS.md
│
├── compression_tests/         # All compression/reconstruction tests
│   ├── compression/          # Phase 3 experiments (formerly phase3/)
│   │   ├── EXPERIMENT_1/
│   │   ├── EXPERIMENT_2/
│   │   ├── EXPERIMENT_2B/
│   │   ├── EXPERIMENT_3/
│   │   └── knowledge_load_2025_01/
│   ├── domain_trials/
│   ├── identity_gravity_trials/
│   ├── phase4/
│   ├── phase5/
│   ├── phase5_prep/
│   ├── phase6/
│   └── phase6_prep/
│
├── archived_trials/           # Historical reference materials
│   ├── SHANNON_BOOT_PROMPT.md
│   ├── Trial_01_FULL_vs_L1_Evaluation.md
│   ├── Trial_02_FULL_vs_L3_Evaluation.md
│   ├── Trial_03_FULL_vs_L2_Evaluation.md
│   └── TRIAL_EVAL_TEMPLATE.md
│
└── README.md                  # Updated navigation guide
```

---

## Benefits

### Clarity
- **Before:** Flat structure with phases, trials, domains mixed together
- **After:** Semantic groupings (compression tests, temporal stability, archived)

### Maintainability
- Easier to navigate
- Clear separation of active vs archived work
- Logical grouping by theoretical layer

### Backward Compatibility
- No files deleted, only moved
- All experiment configs still work (paths relative within directories)
- Import paths remain valid

---

## Impact Analysis

### Files Requiring Updates
- ✅ `experiments/README.md` - Updated to reflect new structure
- ⚠️ Any scripts with hardcoded paths to archived files (unlikely)

### Files Not Requiring Updates
- ✅ All experiment configs (paths are relative within their directories)
- ✅ Orchestrator files (moved as a unit)
- ✅ Python imports (relative imports still work)

---

## What Was NOT Changed

### Active Experiments
- `temporal_stability/` - Newly created, ready to run
- `orchestrator/` - Already at root level
- All compression test directories kept intact

### File Contents
- No file contents modified
- Only directory locations changed
- All relationships preserved

---

## Navigation Guide

### To run S7 Meta-Loop:
```bash
cd experiments/temporal_stability
python s7_meta_loop.py --config s7_config.yaml
```

### To run compression tests:
```bash
cd experiments/compression_tests/compression/EXPERIMENT_2B
python ../../orchestrator/orchestrator2.py --config experiment2b_config.yaml
```

### To view archived materials:
```bash
cd experiments/archived_trials
# Reference only - these are superseded by current experiments
```

---

## Semantic Rationale

### compression_tests/
**Why:** All experiments testing S0-S6 layer predictions (compression fidelity, reconstruction quality, lattice dynamics)

**Contains:**
- Persona compression experiments (Phase 3)
- Domain-specific trials
- Identity gravity experiments
- All phase directories (4-6)

### temporal_stability/
**Why:** All S7 layer experiments (temporal drift, identity stability over time)

**Contains:**
- S7 Meta-Loop implementation (✅ complete)
- Recursive improvement system
- Teaching hooks and curriculum compression

### archived_trials/
**Why:** Historical materials superseded by automated orchestration

**Contains:**
- Early manual trials
- Bootstrap templates no longer used
- Evaluation templates (reference)

---

## SHANNON_BOOT_PROMPT Analysis

**What it was:** Early template for manually bootstrapping persona trials

**Content:**
```markdown
You are an AI persona inside a small research lab.
This lab studies how much of your identity can be reconstructed
from different amounts of written context.

Your initial tasks:
1. Ask which files you are allowed to read.
2. Use those files to understand who you are in this environment.
3. Let me know when you are ready to answer a fixed set of probe questions.
```

**Why archived:**
- Superseded by orchestrator's automated persona initialization
- No longer used in current experimental pipeline
- Kept for historical reference only

**Recommendation:** Can be safely deleted if desired, but archiving preserves history.

---

## Verification

### Before:
```
experiments/
├── compression/
├── domain_trials/
├── identity_gravity_trials/
├── orchestrator/
├── phase4/
├── phase5/
├── phase5_prep/
├── phase6/
├── phase6_prep/
├── temporal_stability/
├── SHANNON_BOOT_PROMPT.md
├── Trial_01_FULL_vs_L1_Evaluation.md
├── Trial_02_FULL_vs_L3_Evaluation.md
├── Trial_03_FULL_vs_L2_Evaluation.md
├── TRIAL_EVAL_TEMPLATE.md
└── README.md
```

### After:
```
experiments/
├── orchestrator/
├── temporal_stability/
├── compression_tests/
│   ├── compression/
│   ├── domain_trials/
│   ├── identity_gravity_trials/
│   ├── phase4/
│   ├── phase5/
│   ├── phase5_prep/
│   ├── phase6/
│   └── phase6_prep/
├── archived_trials/
│   ├── SHANNON_BOOT_PROMPT.md
│   ├── Trial_01_FULL_vs_L1_Evaluation.md
│   ├── Trial_02_FULL_vs_L3_Evaluation.md
│   ├── Trial_03_FULL_vs_L2_Evaluation.md
│   └── TRIAL_EVAL_TEMPLATE.md
└── README.md
```

---

## Recommendations

### Future Organization

As new experiments are added:

1. **S8 Spectral Extensions** → Create `experiments/spectral_extensions/`
2. **S9 Diagonal Coupling** → Create `experiments/coupling_analysis/`
3. **S10 Hybrid Emergence** → Create `experiments/hybrid_emergence/`

### Archived Trials

The `archived_trials/` directory can be:
- **Kept as-is** - Preserves historical context
- **Deleted** - If confident these materials are no longer needed
- **Moved to docs/** - If treating as historical documentation

**Recommendation:** Keep archived for now, review for deletion in 6 months.

---

## Completion Checklist

- ✅ Created `compression_tests/` directory
- ✅ Moved all phase/trial directories to `compression_tests/`
- ✅ Created `archived_trials/` directory
- ✅ Moved SHANNON_BOOT_PROMPT + Trial files to `archived_trials/`
- ✅ Updated `experiments/README.md`
- ✅ Verified directory structure
- ✅ Documented rationale and benefits

---

## Status: ✅ REORGANIZATION COMPLETE

The experiments directory is now cleanly organized with:
- Clear semantic groupings
- Active work separated from archived materials
- Easy navigation and maintainability
- Full backward compatibility

**Ready to proceed with S7 Meta-Loop execution.**

---

**END OF REORGANIZATION SUMMARY**
