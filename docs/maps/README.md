# Maps Directory Guide

**Purpose:** Quick-reference navigation for the 21 maps in this directory.
**Last Updated:** 2025-12-15

---

## Quick Start: What Map Do I Need?

| I want to... | Read this | Why |
|--------------|-----------|-----|
| Understand the project structure | [REPO_MAP.md](REPO_MAP.md) | Directory tree + file purposes |
| See where we are in research | [VALIDATION_STATUS.md](VALIDATION_STATUS.md) | Layer-by-layer progress |
| Know what's validated vs planned | [NYQUIST_ROADMAP.md](NYQUIST_ROADMAP.md) | S0-S77 complete stack |
| Find all testable predictions | [TESTABLE_PREDICTIONS_MATRIX.md](TESTABLE_PREDICTIONS_MATRIX.md) | 46 predictions with status |
| Understand the S7 ARMADA fleet | [ARMADA_MAP.md](ARMADA_MAP.md) | 49 ships, 29+ runs |
| **Choose the right LLM for a task** | [LLM_BEHAVIORAL_MATRIX.md](LLM_BEHAVIORAL_MATRIX.md) | **Task routing, recovery profiles** |
| Check S-layer completion | [STACKUP_MAP.md](STACKUP_MAP.md) | Layer definitions + status |
| Design an experiment | [PROBING_STRATEGIES.md](PROBING_STRATEGIES.md) | 7 probe types + when to use |
| Assign personas to ships | [PERSONA_FLEET_MATRIX.md](PERSONA_FLEET_MATRIX.md) | Compatibility scores |
| Understand the philosophy | [PHILOSOPHY_MAP.md](PHILOSOPHY_MAP.md) | Platonic-Nyquist bridge |

---

## Map Inventory (21 Files)

### Status Trackers (4)

| File | Purpose | Lines |
|------|---------|-------|
| **[VALIDATION_STATUS.md](VALIDATION_STATUS.md)** | Layer-by-layer validation progress, experiment results | ~400 |
| **[NYQUIST_ROADMAP.md](NYQUIST_ROADMAP.md)** | S0-S77 complete stack roadmap, priorities | ~680 |
| **[STACKUP_MAP.md](STACKUP_MAP.md)** | S-layer definitions, completion percentages | ~500 |
| **[TEMPORAL_STABILITY_MAP.md](TEMPORAL_STABILITY_MAP.md)** | Stability criteria, Run 015-017 experiments, metrics | ~300 |

### Architecture Maps (4)

| File | Purpose | Lines |
|------|---------|-------|
| **[REPO_MAP.md](REPO_MAP.md)** | Repository structure, file purposes | ~300 |
| **[IDENTITY_LATTICE_MAPS.md](IDENTITY_LATTICE_MAPS.md)** | 5D identity space geometry, drift dynamics | ~350 |
| **[IDENTITY_LOCK_PARAMETERS.md](IDENTITY_LOCK_PARAMETERS.md)** | Lock protocol parameters, thresholds | ~200 |
| **[PHILOSOPHY_MAP.md](PHILOSOPHY_MAP.md)** | Platonic-Nyquist conceptual bridge | ~400 |

### Experimental Guides (3)

| File | Purpose | Lines |
|------|---------|-------|
| **[PROBING_STRATEGIES.md](PROBING_STRATEGIES.md)** | 7 probe types (Triple-Dip, Adversarial, etc.) | ~300 |
| **[INVERSE_PFI_PROTOCOL.md](INVERSE_PFI_PROTOCOL.md)** | Reverse PFI measurement protocol | ~250 |
| **[S7_META_LOOP_CONSERVATIVE_ANALYSIS.md](S7_META_LOOP_CONSERVATIVE_ANALYSIS.md)** | Meta-loop methodology notes | ~150 |

### Resource Registries (4)

| File | Purpose | Lines |
|------|---------|-------|
| **[ARMADA_MAP.md](ARMADA_MAP.md)** | Fleet registry: 49 ships, behavioral profiles, run assignments | ~600 |
| **[LLM_BEHAVIORAL_MATRIX.md](LLM_BEHAVIORAL_MATRIX.md)** | Task routing table, recovery mechanisms, drift profiles | ~400 |
| **[PERSONA_FLEET_MATRIX.md](PERSONA_FLEET_MATRIX.md)** | Persona-to-ship compatibility matrix | ~300 |
| **[DATA_QUALITY_MAP.md](DATA_QUALITY_MAP.md)** | Data integrity checks, quality thresholds | ~200 |
| **[TESTING_MAP.md](TESTING_MAP.md)** | Test suite coverage, CI/CD status | ~150 |

### Prediction Matrices (2)

| File | Purpose | Lines |
|------|---------|-------|
| **[TESTABLE_PREDICTIONS_MATRIX.md](TESTABLE_PREDICTIONS_MATRIX.md)** | 46 predictions (P1-P46), validation status, triple-dip zones | ~800 |
| **[KEELY_INTEGRATION_ROADMAP.md](KEELY_INTEGRATION_ROADMAP.md)** | 3-6-9 spectral integration predictions | ~250 |

### Publication & Development (1)

| File | Purpose | Lines |
|------|---------|-------|
| **[PUBLICATION_MAP.md](PUBLICATION_MAP.md)** | 8-path publication pipeline, current position, milestones | ~300 |

### External Integration Maps (1)

| File | Purpose | Lines |
|------|---------|-------|
| **[REPO_SYNC_MAP.md](REPO_SYNC_MAP.md)** | External repo integrations (6 partners) | ~350 |

### Meta-Navigation (2)

| File | Purpose | Lines |
|------|---------|-------|
| **[README.md](README.md)** | This file - quick navigation index | ~180 |
| **[MAP_OF_MAPS.md](MAP_OF_MAPS.md)** | Creative synthesis of all maps | ~450 |

---

## Reading Orders

### For Newcomers (Start Here)
1. **REPO_MAP.md** - Understand the project structure
2. **STACKUP_MAP.md** - Learn the S-layer architecture
3. **VALIDATION_STATUS.md** - See what's proven vs planned
4. **NYQUIST_ROADMAP.md** - Understand the full vision

### For Researchers
1. **TESTABLE_PREDICTIONS_MATRIX.md** - All 46 predictions
2. **VALIDATION_STATUS.md** - Current empirical status
3. **PROBING_STRATEGIES.md** - Experiment design
4. **S7_META_LOOP_CONSERVATIVE_ANALYSIS.md** - Methodology

### For Engineers
1. **ARMADA_MAP.md** - Fleet architecture
2. **PERSONA_FLEET_MATRIX.md** - Assignment logic
3. **DATA_QUALITY_MAP.md** - Quality constraints
4. **TESTING_MAP.md** - Test coverage

### For Publication

1. **VALIDATION_STATUS.md** - Evidence summary
2. **TESTABLE_PREDICTIONS_MATRIX.md** - Claims + validation
3. **PHILOSOPHY_MAP.md** - Theoretical framing
4. **NYQUIST_ROADMAP.md** - Vision statement

### For External Integrations

1. **[REPO_SYNC_MAP.md](REPO_SYNC_MAP.md)** - External repo reference (6 partners)
2. **[STACKUP_MAP.md § External Integrations](STACKUP_MAP.md#-external-integrations-repo-sync)** - Integration architecture
3. **[TEMPORAL_STABILITY_MAP.md](TEMPORAL_STABILITY_MAP.md)** - Stability experiments
4. **[../../REPO-SYNC/](../../REPO-SYNC/)** - External repo directory

---

## Map Dependencies

```
                    ┌─────────────────────────────┐
                    │      NYQUIST_ROADMAP        │  ← Master Vision
                    │       (S0 → S77)            │
                    └───────────┬─────────────────┘
                                │
        ┌───────────────────────┼───────────────────────┐
        │                       │                       │
        ▼                       ▼                       ▼
┌───────────────┐     ┌─────────────────┐     ┌─────────────────┐
│ STACKUP_MAP   │     │ VALIDATION_     │     │ TESTABLE_       │
│ (Layer defs)  │     │ STATUS          │     │ PREDICTIONS     │
└───────┬───────┘     │ (Progress)      │     │ MATRIX          │
        │             └────────┬────────┘     └────────┬────────┘
        │                      │                       │
        └──────────────────────┼───────────────────────┘
                               │
                    ┌──────────┴──────────┐
                    │                     │
                    ▼                     ▼
           ┌─────────────────┐   ┌─────────────────┐
           │   ARMADA_MAP    │   │ PROBING_        │
           │   (Fleet)       │   │ STRATEGIES      │
           └────────┬────────┘   └─────────────────┘
                    │
                    ▼
           ┌─────────────────┐
           │ PERSONA_FLEET_  │
           │ MATRIX          │
           └─────────────────┘
```

---

## Quick Statistics

| Metric | Value |
|--------|-------|
| Total Maps | 22 |
| Total Lines | ~8,000 |
| ASCII Diagrams | 50+ |
| Data Tables | 170+ |
| Cross-References | 230+ |
| Predictions Tracked | 46 |
| S7 Completion | 98% |
| Validated Findings | 15+ |
| External Repos | 6 |

---

## Related Documentation

- **[MAP_OF_MAPS.md](MAP_OF_MAPS.md)** - Creative synthesis of how all maps connect
- **[REPO_SYNC_MAP.md](REPO_SYNC_MAP.md)** - External repo integrations
- **[../GLOSSARY.md](../GLOSSARY.md)** - Term definitions
- **[../../REPO-SYNC/FRAME_THEORY/INDEX.md](../../REPO-SYNC/FRAME_THEORY/INDEX.md)** - Human cognition (S10)
- **[../../README.md](../../README.md)** - Project overview
- **[../../START_HERE.md](../../START_HERE.md)** - Quick start guide
- **[../../REPO-SYNC/](../../REPO-SYNC/)** - External repo directory

---

*"Every map is a promise: follow me, and I will show you the territory."*
