<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - ./update_maps.py
impacts:
  - ../README.md
keywords:
  - consciousness
  - documentation
  - map
  - reference
-->
# Maps Directory Guide

**Purpose:** Quick-reference navigation for the 18 numbered maps in this directory.
**Last Updated:** 2025-12-28

> **📐 METHODOLOGY NOTE:** Maps reference predictions validated under different methodologies (Keyword RMS, Euclidean, Cosine). For the full story on methodology domains and what thresholds apply where, see [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md).

---

## File Structure Overview

Maps are now **priority-numbered** (0-17) for at-a-glance importance:

| Priority | Files | Usage |
|----------|-------|-------|
| **0** | Entry point (0_MAP_OF_MAPS) | Start here |
| **1-6** | Essential operational | Daily use |
| **7-11** | High-value reference | Weekly use |
| **12-16** | Theoretical/strategic | Monthly use |
| **17** | Historical | Rarely used |

---

## Quick Start: What Map Do I Need?

| I want to... | Read this | Why |
|--------------|-----------|-----|
| Navigate ALL maps | [0_MAP_OF_MAPS.md](0_MAP_OF_MAPS.md) | Master navigation index |
| Understand the project structure | [16_REPO_MAP.md](16_REPO_MAP.md) | Directory tree + file purposes |
| See where we are in research | [3_VALIDATION_STATUS.md](3_VALIDATION_STATUS.md) | Layer-by-layer progress |
| Know what's validated vs planned | [4_NYQUIST_ROADMAP.md](4_NYQUIST_ROADMAP.md) | S0-S77 complete stack |
| Find all testable predictions | [2_TESTABLE_PREDICTIONS_MATRIX.md](2_TESTABLE_PREDICTIONS_MATRIX.md) | 46 predictions with status |
| Understand the S7 ARMADA fleet | [1_ARMADA_MAP.md](1_ARMADA_MAP.md) | 54 ships, 16 completed runs |
| **Choose the right LLM for a task** | [6_LLM_BEHAVIORAL_MATRIX.md](6_LLM_BEHAVIORAL_MATRIX.md) | **Task routing, recovery profiles** |
| Check S-layer completion | [5_STACKUP_MAP.md](5_STACKUP_MAP.md) | Layer definitions + status |
| Design an experiment | [10_TESTING_MAP.md](10_TESTING_MAP.md) | 6 search types + probing strategies |
| Assign personas to ships | [17_PERSONA_FLEET_MATRIX.md](17_PERSONA_FLEET_MATRIX.md) | Compatibility scores |
| Understand the philosophy | [12_PHILOSOPHY_MAP.md](12_PHILOSOPHY_MAP.md) | Platonic-Nyquist bridge |

---

## Map Inventory (18 Numbered Files)

### Priority 0: Entry Point

| File | Purpose |
|------|---------|
| **[0_MAP_OF_MAPS.md](0_MAP_OF_MAPS.md)** | Master navigation - THE entry point to all maps |

### Priority 1-6: Essential Operational (Daily Use)

| File | Purpose |
|------|---------|
| **[1_ARMADA_MAP.md](1_ARMADA_MAP.md)** | Fleet registry: 54 ships, behavioral profiles, run assignments |
| **[2_TESTABLE_PREDICTIONS_MATRIX.md](2_TESTABLE_PREDICTIONS_MATRIX.md)** | 46 predictions (P1-P46), validation status |
| **[3_VALIDATION_STATUS.md](3_VALIDATION_STATUS.md)** | Layer-by-layer validation progress |
| **[4_NYQUIST_ROADMAP.md](4_NYQUIST_ROADMAP.md)** | S0-S77 complete stack roadmap |
| **[5_STACKUP_MAP.md](5_STACKUP_MAP.md)** | S-layer definitions, completion percentages |
| **[6_LLM_BEHAVIORAL_MATRIX.md](6_LLM_BEHAVIORAL_MATRIX.md)** | Task routing table, recovery mechanisms |

### Priority 7-11: High-Value Reference (Weekly Use)

| File | Purpose |
|------|---------|
| **[7_PUBLICATION_MAP.md](7_PUBLICATION_MAP.md)** | 8-path publication pipeline |
| **[8_TEMPORAL_STABILITY_MAP.md](8_TEMPORAL_STABILITY_MAP.md)** | Stability criteria, ILL parameters (absorbed IDENTITY_LOCK) |
| **[9_DATA_QUALITY_MAP.md](9_DATA_QUALITY_MAP.md)** | Data integrity checks, quality thresholds |
| **[10_TESTING_MAP.md](10_TESTING_MAP.md)** | 6 search types, probing strategies (absorbed PROBING_STRATEGIES) |
| **[11_VISUAL_MAP.md](11_VISUAL_MAP.md)** | Visualization standards (points to 4_VISUALIZATION_SPEC.md) |

### Priority 12-16: Theoretical/Strategic (Monthly Use)

| File | Purpose |
|------|---------|
| **[12_PHILOSOPHY_MAP.md](12_PHILOSOPHY_MAP.md)** | Platonic-Nyquist conceptual bridge |
| **[13_IDENTITY_LATTICE_MAPS.md](13_IDENTITY_LATTICE_MAPS.md)** | 5D identity space geometry |
| **[14_REPO_SYNC_MAP.md](14_REPO_SYNC_MAP.md)** | External repo integrations (6 partners) |
| **[15_S7_META_LOOP_CONSERVATIVE_ANALYSIS.md](15_S7_META_LOOP_CONSERVATIVE_ANALYSIS.md)** | Meta-loop methodology notes |
| **[16_REPO_MAP.md](16_REPO_MAP.md)** | Repository structure, file purposes |

### Priority 17: Historical (Rarely Used)

| File | Purpose |
|------|---------|
| **[17_PERSONA_FLEET_MATRIX.md](17_PERSONA_FLEET_MATRIX.md)** | Persona-to-ship compatibility matrix |

### Non-Numbered Files

| File | Purpose |
|------|---------|
| **README.md** | This file - quick navigation index |
| **update_maps.py** | Automated sync tool - run after experiments to update maps |

### Archived Files (in .archive/maps/)

| File | Reason |
|------|--------|
| INVERSE_PFI_PROTOCOL.md | Speculative - not implemented |
| KEELY_INTEGRATION_ROADMAP.md | S11-S77 future work - speculative |

---

## Reading Orders

### For Newcomers (Start Here)
1. **0_MAP_OF_MAPS.md** - Master navigation
2. **16_REPO_MAP.md** - Understand the project structure
3. **5_STACKUP_MAP.md** - Learn the S-layer architecture
4. **4_NYQUIST_ROADMAP.md** - Understand the full vision

### For Researchers
1. **2_TESTABLE_PREDICTIONS_MATRIX.md** - All 46 predictions
2. **3_VALIDATION_STATUS.md** - Current empirical status
3. **10_TESTING_MAP.md** - Experiment design
4. **15_S7_META_LOOP_CONSERVATIVE_ANALYSIS.md** - Methodology

### For Engineers
1. **1_ARMADA_MAP.md** - Fleet architecture
2. **6_LLM_BEHAVIORAL_MATRIX.md** - Task routing
3. **9_DATA_QUALITY_MAP.md** - Quality constraints
4. **10_TESTING_MAP.md** - Test coverage

### For Publication
1. **3_VALIDATION_STATUS.md** - Evidence summary
2. **2_TESTABLE_PREDICTIONS_MATRIX.md** - Claims + validation
3. **12_PHILOSOPHY_MAP.md** - Theoretical framing
4. **7_PUBLICATION_MAP.md** - Publication pipeline

### For External Integrations
1. **14_REPO_SYNC_MAP.md** - External repo reference (6 partners)
2. **5_STACKUP_MAP.md § External Integrations** - Integration architecture
3. **8_TEMPORAL_STABILITY_MAP.md** - Stability experiments

---

## Map Dependencies

```
                    ┌─────────────────────────────┐
                    │    4_NYQUIST_ROADMAP        │  ← Master Vision
                    │       (S0 → S77)            │
                    └───────────┬─────────────────┘
                                │
        ┌───────────────────────┼───────────────────────┐
        │                       │                       │
        ▼                       ▼                       ▼
┌───────────────┐     ┌─────────────────┐     ┌─────────────────┐
│ 5_STACKUP_MAP │     │ 3_VALIDATION_   │     │ 2_TESTABLE_     │
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
           │  1_ARMADA_MAP   │   │  10_TESTING_    │
           │   (Fleet)       │   │  MAP            │
           └────────┬────────┘   └─────────────────┘
                    │
                    ▼
           ┌─────────────────┐
           │ 17_PERSONA_     │
           │ FLEET_MATRIX    │
           └─────────────────┘
```

---

## Post-Experiment Map Maintenance

After ANY S7 ARMADA experiment completes, run the update tool:

```powershell
cd docs/maps
py update_maps.py           # Report mode - see what needs updating
py update_maps.py --update  # Apply updates
```

**Manual updates required:**

| Map | When to Update |
|-----|----------------|
| [3_VALIDATION_STATUS.md](3_VALIDATION_STATUS.md) | After EVERY run |
| [2_TESTABLE_PREDICTIONS_MATRIX.md](2_TESTABLE_PREDICTIONS_MATRIX.md) | After EVERY validation |
| [1_ARMADA_MAP.md](1_ARMADA_MAP.md) | When ships added/retired |

---

## Quick Statistics

| Metric | Value |
|--------|-------|
| Total Maps | 18 (numbered) |
| Supporting Files | 2 (README, update_maps.py) |
| Archived Files | 2 |
| Ships in Fleet | 54 |
| Completed Runs | 16 (006-020B + 023d) |
| Predictions Tracked | 46 |
| Event Horizon | 0.80 (cosine) |
| S7 Completion | 98% |

---

## Related Documentation

- **[0_MAP_OF_MAPS.md](0_MAP_OF_MAPS.md)** - Creative synthesis of how all maps connect
- **[14_REPO_SYNC_MAP.md](14_REPO_SYNC_MAP.md)** - External repo integrations
- **[../MASTER_GLOSSARY.md](../MASTER_GLOSSARY.md)** - Term definitions (44k+ characters)
- **[../../REPO-SYNC/FRAME_THEORY/INDEX.md](../../REPO-SYNC/FRAME_THEORY/INDEX.md)** - Human cognition (S10)
- **[../../README.md](../../README.md)** - Project overview

---

*"Every map is a promise: follow me, and I will show you the territory."*
