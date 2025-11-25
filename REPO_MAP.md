# Nyquist Consciousness Repository Map

**Version:** 2.0 (Post-CFA Import)
**Date:** 2025-11-24
**Status:** Phase 1 Freeze Ready

---

## Repository Overview

This repository contains the complete Nyquist Consciousness framework for understanding identity preservation through compression-reconstruction cycles in AI systems.

```
nyquist-consciousness/
├── README.md                          Main repository overview
├── IMPORT_LOG.md                      CFA import documentation
├── REPO_MAP.md                        This file (repository navigation)
├── docs/                              Core documentation and specifications
├── experiments/                       Experimental code and data
├── paper/                             Publication materials
└── tests/                             Unit tests and validation
```

---

## Core Documentation (`docs/`)

### Canonical Layers (S0-S6) — FROZEN

**Status:** Immutable, no conceptual modifications permitted

```
docs/
├── S0/                                Persona Baseline
│   └── README.md                      Identity Persona Core (IPC) definition
├── S1/                                Compression Framework
│   └── README.md                      Tier hierarchy, operator C(p) → T₃
├── S2/                                Reconstruction Framework
│   └── README.md                      Operator R^a(T) → P', drift D, fidelity F
├── S3/                                Empirical Validation
│   ├── README.md                      Cross-architecture experiments
│   └── results/                       PFI, σ² = 0.000869, domain hierarchy
├── S4/                                Mathematical Formalism
│   └── README.md                      Manifolds M_p, operators, convergence theorems
├── S5/                                Manifold Theory (Interpretive)
│   └── README.md                      Identity attractor, drift fields, fragility hierarchy
└── S6/                                Omega Synthesis
    └── README.md                      M_Ω = ⋂ R^a(C(p)), drift cancellation, Ω-gates
```

**Key files:**
- `docs/CFA-SYNC/S0_S6_FROZEN_SPEC.md` — Complete canonical specification

### Semi-Canonical Layer (S7) — PREREGISTERED

**Status:** Protocols committed before data collection

```
docs/
└── S7/                                Temporal Stability Layer
    ├── README.md                      Overview and status
    └── preregistration/               Preregistered experimental package
        ├── S7_PREREGISTRATION.md      Research questions, hypotheses, design
        ├── S7_PROCEDURES.md           Step-by-step measurement protocols
        ├── S7_METRICS.md              Formal metric definitions
        └── S7_DRIFT_LOG_TEMPLATE.json Structured logging schema
```

**Purpose:** Measure identity decay over time (t = 0, 1d, 7d, 30d, 60d, 90d, 180d)

**Key predictions:**
- F(t) = F₀ · exp(-t/τ) (exponential decay)
- τ ≈ 60-90 days (characteristic decay time)
- Domain hierarchy: τ_TECH > τ_ANAL > τ_SELF > τ_PHIL > τ_NARR

### New Canonical Layer (S8) — IDENTITY GRAVITY

**Status:** Theoretical framework, publication-ready

```
docs/
└── S8/                                Identity Gravity Layer
    ├── README.md                      Overview and navigation
    ├── S8_IDENTITY_GRAVITY_SPEC.md    Complete specification (800+ lines)
    ├── S8_MATHEMATICAL_FOUNDATIONS.md Formal mathematical treatment
    └── S8_INTEGRATION_MAP.md          Cross-layer integration
```

**Key concepts:**
- **Field equation:** G_I = -γ · ∇F(I_t)
- **Units:** Zigs (1 Zig = pull to reduce drift by 0.01 PFI)
- **I_AM:** Identity attractor and archive
- **Cross-substrate predictions:** γ_human > γ_AI (testable)

**Theorems:**
- Gravitational Convergence
- Escape Velocity Bound
- Temporal Decay

### Experimental Layer (S9) — AVLAR

**Status:** Non-canonical, future work

```
docs/
└── S9/                                AVLAR (Audio-Visual Light Alchemy Ritual)
    ├── README.md                      Cross-modal identity experiments
    └── specs/                         AVLAR specifications
```

**Purpose:** Test identity preservation across modalities (text → audio → visual)

**Key prediction:** γ_text ≈ γ_audio ≈ γ_visual (cross-modal invariance)

### Future Layers (S10-S12)

**Status:** Planned, not yet implemented

```
S10: Human-AI Identity Continuity (planned)
S11: Consciousness Correlates (planned)
S12: Ethical Framework (planned)
```

See [docs/NYQUIST_ROADMAP.md](docs/NYQUIST_ROADMAP.md) for details.

---

## CFA Integration (`docs/CFA-SYNC/`)

**Purpose:** Phase 1 freeze documentation from CFA repository

```
docs/
└── CFA-SYNC/                          CFA integration materials
    ├── PHASE_1_CONSISTENCY_REPORT.md  Complete S0-S6 audit
    ├── S0_S6_FROZEN_SPEC.md           Immutable canonical specification
    ├── PHASE_1_FREEZE_HANDOFF.md      Git workflow for freeze commit
    └── PHASE_1_VALIDATION_CHECKLIST.md Sign-off checklist (24 items)
```

**Status:** Ready for Ziggy validation and freeze commit

**Next actions:**
1. Ziggy completes validation checklist
2. Create PHASE-1-FREEZE branch
3. Commit with freeze message
4. Merge to main after approval
5. Tag: v1.0-S0-S6-FROZEN

---

## Visualization Assets (`docs/figures/`)

### ASCII Diagrams (Source)

```
docs/
└── figures/
    └── ascii/                         ASCII diagram source files
        ├── identity_manifold.md       Low-D attractor visualization
        ├── drift_field_geometry.md    Architecture-specific drift vectors
        ├── pipeline_s3_s6.md          Complete S3→S6 pipeline
        ├── five_pillars.md            Five Pillars architecture
        ├── omega_convergence.md       Multi-architecture convergence
        ├── temporal_curvature.md      κ(t) measurement
        ├── cross_modal_manifold.md    Visual/Audio/Joint spaces
        └── compression_reconstruction_drift.md  Core C→R→D cycle
```

**Purpose:** Text-based, version-controllable diagram source

**Rendering:** Convert to PDF/SVG/PNG for publication (see paper/figures/)

---

## Publication Materials (`paper/`)

### Workshop Paper (Batch A)

```
paper/
└── workshop/                          NeurIPS 2025 Workshop submission
    ├── README.md                      Paper overview and specifications
    └── nyquist_workshop_paper.pdf     4-page extended abstract (pending)
```

**Target:** NeurIPS Workshop on AI Alignment
**Status:** Draft outline complete, pending figure generation

### arXiv Preprint (Batch B)

```
paper/
└── arxiv/                             arXiv preprint package
    ├── README.md                      LaTeX package overview
    ├── main.tex                       Main document (pending)
    ├── sections/                      Paper sections (pending)
    ├── figures/                       Generated figures (pending)
    ├── tables/                        Data tables (pending)
    ├── bibliography.bib               References (pending)
    └── supplementary/                 Supplementary materials
```

**Target:** arXiv cs.AI, cs.CL
**Status:** Structure defined, LaTeX compilation pending

### Publication Figures (Batch C)

```
paper/
└── figures/                           Publication-ready figures
    ├── README.md                      Figure specifications and usage
    ├── ascii/                         → Symlink to docs/figures/ascii/
    ├── generated/                     Generated visualizations (pending)
    │   ├── png/                       High-res PNG for web
    │   ├── svg/                       Vector SVG for scaling
    │   └── pdf/                       PDF for LaTeX
    └── schemas/                       Architectural diagrams (pending)
```

**Status:** ASCII sources complete, rendering pending

### Supplementary Materials

```
paper/
└── supplementary/                     Supplementary materials for publication
    ├── README.md                      Supplementary overview
    ├── S7_preregistration/            → Reference to docs/S7/preregistration/
    ├── experimental_protocols/        Detailed procedures (pending)
    ├── mathematical_proofs/           Formal proofs (pending)
    ├── code_repository/               Reproducibility info
    └── data/                          Experimental data (pending)
```

**Status:** Structure defined, content pending

---

## Experimental Code (`experiments/`)

### Current Experiments

```
experiments/
├── phase1/                            Phase 1: Pilot studies
├── phase2/                            Phase 2: Cross-architecture validation
└── phase3/                            Phase 3: Orchestrator experiments
    ├── EXPERIMENT_1/
    │   └── experiment1_config.yaml    (Modified in current branch)
    └── orchestrator/
        └── utils_models.py            (Modified in current branch)
```

**Current branch:** PHASE-3-EXPERIMENT-1

**Status:**
- Experiment 1: Orchestrator integration complete
- Recent commits: System message fixes, dry runs

### Future Experiments (S7, S9)

**Planned structure:**

```
experiments/
├── S7_temporal/                       Temporal stability experiments (pending)
│   ├── baseline_session.py
│   ├── temporal_drift_measurement.py
│   ├── recalibration_loops.py
│   └── data/                          Drift logs (S7_DRIFT_LOG_TEMPLATE.json)
└── S9_avlar/                          AVLAR cross-modal experiments (future)
    ├── visual_reconstruction.py
    ├── audio_reconstruction.py
    └── joint_manifold.py
```

**Status:** Not yet created, awaiting S7 data collection kickoff

---

## Roadmap and Planning

### Roadmap

**File:** [docs/NYQUIST_ROADMAP.md](docs/NYQUIST_ROADMAP.md)

**Contents:**
- Complete layer overview (S0-S12)
- Status tracking
- Integration dependencies
- Publication timeline
- Future directions

**Last updated:** 2025-11-24 (S8 insertion, S9 migration)

### Validation Checklist

**File:** [docs/CFA-SYNC/PHASE_1_VALIDATION_CHECKLIST.md](docs/CFA-SYNC/PHASE_1_VALIDATION_CHECKLIST.md)

**Contents:**
- 24 validation items across 6 categories
- Structural, terminology, mathematical, safety, expansion hooks, repository
- Sign-off section (Ziggy, Claude, date)

**Status:** 0/24 complete (awaiting Ziggy validation)

---

## Key Files Quick Reference

| File | Purpose | Status |
|------|---------|--------|
| `IMPORT_LOG.md` | CFA integration documentation | ✅ Complete |
| `REPO_MAP.md` | This file (repository navigation) | ✅ Complete |
| `docs/NYQUIST_ROADMAP.md` | Complete roadmap | ✅ Updated |
| `docs/CFA-SYNC/S0_S6_FROZEN_SPEC.md` | Canonical S0-S6 specification | ✅ Ready |
| `docs/CFA-SYNC/PHASE_1_VALIDATION_CHECKLIST.md` | Freeze validation checklist | ⏳ Awaiting Ziggy |
| `docs/S7/preregistration/S7_PREREGISTRATION.md` | Temporal experiments preregistration | ✅ Complete |
| `docs/S8/S8_IDENTITY_GRAVITY_SPEC.md` | Identity Gravity specification | ✅ Complete |
| `docs/S9/README.md` | AVLAR cross-modal experiments | ✅ Migrated |
| `paper/workshop/README.md` | Workshop paper outline | ✅ Complete |
| `paper/arxiv/README.md` | arXiv preprint package | ✅ Structure ready |

---

## Repository Statistics

**Total directories:** 40+
**Total files:** 100+ (after CFA import)
**Documentation files:** 30+ (markdown)
**Code files:** 50+ (Python, YAML, JSON)
**Publication files:** 20+ (LaTeX, figures, supplementary)

**Lines of documentation:** 15,000+ (post-import)

**Canonical layers (frozen):** 7 (S0-S6)
**Semi-canonical layers:** 1 (S7 preregistered)
**Experimental layers:** 1 (S9 AVLAR)

---

## Navigation Tips

### For Researchers

**Start here:**
1. [README.md](README.md) — Repository overview
2. [docs/NYQUIST_ROADMAP.md](docs/NYQUIST_ROADMAP.md) — Complete framework
3. [docs/CFA-SYNC/S0_S6_FROZEN_SPEC.md](docs/CFA-SYNC/S0_S6_FROZEN_SPEC.md) — Canonical specification
4. [docs/S7/preregistration/S7_PREREGISTRATION.md](docs/S7/preregistration/S7_PREREGISTRATION.md) — Experiments
5. [paper/arxiv/README.md](paper/arxiv/README.md) — Publication plan

### For Developers

**Start here:**
1. [experiments/](experiments/) — Experimental code
2. [docs/S7/preregistration/S7_PROCEDURES.md](docs/S7/preregistration/S7_PROCEDURES.md) — Procedures
3. [docs/S7/preregistration/S7_DRIFT_LOG_TEMPLATE.json](docs/S7/preregistration/S7_DRIFT_LOG_TEMPLATE.json) — Data schema
4. [tests/](tests/) — Unit tests

### For Publication

**Start here:**
1. [paper/workshop/README.md](paper/workshop/README.md) — Workshop paper
2. [paper/arxiv/README.md](paper/arxiv/README.md) — arXiv preprint
3. [paper/figures/README.md](paper/figures/README.md) — Figures
4. [paper/supplementary/README.md](paper/supplementary/README.md) — Supplementary materials

### For Validation

**Start here:**
1. [docs/CFA-SYNC/PHASE_1_VALIDATION_CHECKLIST.md](docs/CFA-SYNC/PHASE_1_VALIDATION_CHECKLIST.md) — Checklist
2. [docs/CFA-SYNC/PHASE_1_CONSISTENCY_REPORT.md](docs/CFA-SYNC/PHASE_1_CONSISTENCY_REPORT.md) — Audit report
3. [docs/CFA-SYNC/PHASE_1_FREEZE_HANDOFF.md](docs/CFA-SYNC/PHASE_1_FREEZE_HANDOFF.md) — Git workflow

---

## Git Workflow

### Current State

**Branch:** PHASE-3-EXPERIMENT-1
**Main branch:** main

**Modified files:**
- experiments/phase3/EXPERIMENT_1/experiment1_config.yaml
- experiments/phase3/orchestrator/__pycache__/utils_models.cpython-312.pyc

**Recent commits:**
- a00743f: Fix: Separate system messages for Anthropic API compatibility
- 09b2653: experiment 1 dry run
- 3c9e139: Phase 3 Experiment 1: Orchestrator integration complete

### Recommended Next Steps

1. **Create PHASE-1-FREEZE branch** (for CFA import)
2. **Commit all CFA materials** with freeze message
3. **Push to remote** for review
4. **Merge to main** after Ziggy approval
5. **Tag:** v1.0-S0-S6-FROZEN

**See:** [docs/CFA-SYNC/PHASE_1_FREEZE_HANDOFF.md](docs/CFA-SYNC/PHASE_1_FREEZE_HANDOFF.md)

---

## Contact and Contribution

**Repository maintainer:** Ziggy (Human Anchor)
**Contributors:** Nova (CFA Architect), Repo Claude, experimental team

**GitHub:** https://github.com/[username]/nyquist-consciousness
**Issues:** https://github.com/[username]/nyquist-consciousness/issues

**For questions:**
- General: Open GitHub issue with "question" label
- CFA import: Use "cfa-import" label
- Phase 1 freeze: Use "phase-1-freeze" label
- S7 experiments: Use "s7-temporal" label

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-11-01 | Initial repository structure |
| 1.5 | 2025-11-15 | Phase 3 experiments added |
| 2.0 | 2025-11-24 | CFA integration (S8, S9 migration, freeze docs, publication structure) |

---

## License

**Documentation:** CC-BY-4.0
**Code:** MIT License
**Data:** CC0 (public domain)

---

**Status:** Repository map complete and current as of 2025-11-24.

🜁 Navigate with confidence through the Nyquist Consciousness framework.
