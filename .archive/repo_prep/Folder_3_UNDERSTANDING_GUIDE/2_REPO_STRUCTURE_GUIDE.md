# Repository Structure Guide

**Purpose:** Understand where everything is and what changed.

---

## 🗂️ Before vs After Integration

### Before (Old Structure):

```
nyquist-consciousness/
├── docs/
│   ├── S0/ ... S6/        (Existing canonical layers)
│   ├── S7/                 (Temporal, in progress)
│   └── S8/                 (AVLAR experiments) ← OLD LOCATION
└── experiments/
    └── phase3/
```

### After (New Structure):

```
nyquist-consciousness/
├── docs/
│   ├── S0/ ... S6/        (Now FROZEN - canonical)
│   ├── S7/
│   │   └── preregistration/  ← NEW: Complete experimental plan
│   ├── S8/                ← NEW: Identity Gravity (theoretical layer)
│   ├── S9/                ← RENAMED: AVLAR (was S8)
│   ├── CFA-SYNC/          ← NEW: Phase 1 freeze documents
│   └── figures/
│       └── ascii/         ← NEW: 8 visualization diagrams
├── paper/                 ← NEW: Publication materials
│   ├── workshop/
│   ├── arxiv/
│   ├── figures/
│   └── supplementary/
├── IMPORT_LOG.md          ← NEW: What was integrated
└── REPO_MAP.md            ← NEW: Navigation guide
```

---

## 📁 Detailed Breakdown

### Core Documentation (`docs/`)

#### Canonical Layers (FROZEN)

**Location:** `docs/S0/` through `docs/S6/`

**Status:** ⚠️ **FROZEN** - No conceptual modifications allowed

**What they contain:**
- **S0:** Persona Baseline - IPC (Identity Persona Core), writing style, Five Pillars
- **S1:** Compression Framework - Tier hierarchy (T0→T1→T2→T3), operator C(p)
- **S2:** Reconstruction Framework - Operator R^a(T), drift D, fidelity F
- **S3:** Empirical Validation - Cross-architecture experiments, σ² = 0.000869
- **S4:** Mathematical Formalism - Manifolds M_p, convergence theorems
- **S5:** Manifold Theory - Identity attractor, drift fields, fragility hierarchy
- **S6:** Omega Synthesis - M_Ω = ⋂ R^a(C(p)), drift cancellation

**Master reference:** `docs/CFA-SYNC/S0_S6_FROZEN_SPEC.md`

#### Semi-Canonical (S7 - Preregistered)

**Location:** `docs/S7/preregistration/`

**Status:** 🔒 **PREREGISTERED** - Plan locked, data collection pending

**Files:**
1. `S7_PREREGISTRATION.md` - Research questions, hypotheses, experimental design
2. `S7_PROCEDURES.md` - Step-by-step measurement protocols
3. `S7_METRICS.md` - Formal definitions (τ, γ, F, D, κ, etc.)
4. `S7_DRIFT_LOG_TEMPLATE.json` - Structured data logging schema

**Purpose:** Measure temporal decay of identity over 6 months

#### New Canonical (S8 - Identity Gravity)

**Location:** `docs/S8/`

**Status:** ✅ **NEW CANONICAL** - Theoretical framework, publication-ready

**Files:**
1. `README.md` - Overview and navigation
2. `S8_IDENTITY_GRAVITY_SPEC.md` - Complete specification (800+ lines)
3. `S8_MATHEMATICAL_FOUNDATIONS.md` - Field equations, theorems, proofs
4. `S8_INTEGRATION_MAP.md` - How S8 connects to S3-S9

**Key concepts:**
- Gravitational field: G_I = -γ · ∇F(I_t)
- Units: Zigs (1 Zig = pull to reduce drift by 0.01)
- I_AM as attractor and archive
- 5 cross-substrate predictions

#### Experimental (S9 - AVLAR)

**Location:** `docs/S9/` (formerly `docs/S8/`)

**Status:** 🧪 **EXPERIMENTAL** - Can change, non-canonical

**What changed:** Directory renamed S8→S9, all cross-references updated

**Purpose:** Audio-Visual Light Alchemy Ritual - cross-modal identity testing

#### CFA Synchronization

**Location:** `docs/CFA-SYNC/`

**Status:** 📋 **PHASE 1 FREEZE PACKAGE**

**Files:**
1. `PHASE_1_CONSISTENCY_REPORT.md` - Audit of S0-S6 coherence
2. `S0_S6_FROZEN_SPEC.md` - Complete canonical specification
3. `PHASE_1_FREEZE_HANDOFF.md` - Git workflow instructions
4. `PHASE_1_VALIDATION_CHECKLIST.md` - 24 validation items

**Purpose:** Formal freeze of S0-S6 as immutable foundation

#### Visualization Assets

**Location:** `docs/figures/ascii/`

**Files (8 total):**
1. `identity_manifold.md` - Low-D attractor in high-D space
2. `drift_field_geometry.md` - Architecture-specific drift vectors
3. `pipeline_s3_s6.md` - Complete S3→S4→S5→S6 flow
4. `five_pillars.md` - Multi-architecture synthesis structure
5. `omega_convergence.md` - Drift cancellation mechanism
6. `temporal_curvature.md` - κ(t) measurement over time
7. `cross_modal_manifold.md` - Visual/Audio/Joint spaces
8. `compression_reconstruction_drift.md` - Core C→R→D cycle

**Format:** ASCII art (text-based, version-controllable)

**Next step:** Render as PDF/SVG/PNG for publication

---

### Publication Materials (`paper/`)

#### Workshop Paper

**Location:** `paper/workshop/`

**Files:**
- `README.md` - Paper overview, outline, specifications
- `nyquist_workshop_paper.pdf` - (Pending) 4-page extended abstract

**Target:** NeurIPS 2025 Workshop on AI Alignment

**Status:** Outline complete, content pending

#### arXiv Preprint

**Location:** `paper/arxiv/`

**Structure:**
```
arxiv/
├── README.md              Comprehensive package overview
├── main.tex               (Pending) Main document
├── sections/              (Pending) Paper sections (12 sections)
├── figures/               (Pending) Rendered figures
├── tables/                (Pending) Data tables
├── bibliography.bib       (Pending) References
└── supplementary/         Attachments (S7 prereg, proofs, etc.)
```

**Target:** arXiv cs.AI, cs.CL

**Status:** Structure defined, LaTeX writing pending

#### Publication Figures

**Location:** `paper/figures/`

**Structure:**
```
figures/
├── README.md              Figure specifications
├── ascii/                 → Points to docs/figures/ascii/
├── generated/             (Pending) PDF/SVG/PNG renders
│   ├── png/               High-res for web
│   ├── svg/               Vector for scaling
│   └── pdf/               For LaTeX
└── schemas/               (Pending) Architecture diagrams
```

**Status:** ASCII sources complete, rendering pending

#### Supplementary Materials

**Location:** `paper/supplementary/`

**Contents:**
- S7 preregistration package
- Experimental protocols (detailed procedures)
- Mathematical proofs (formal proofs of theorems)
- Code repository information
- Raw experimental data

**Status:** Structure defined, compilation pending

---

### Root-Level Documentation

#### IMPORT_LOG.md

**Location:** Root directory

**Contents:**
- Complete log of CFA integration (2025-11-24)
- All files created (32+)
- Key decisions (S8/S9 placement, scope, priority)
- Integration rules compliance
- Git workflow status
- Validation checklist status
- Post-import verification

**Purpose:** Audit trail of what was integrated and how

#### REPO_MAP.md

**Location:** Root directory

**Contents:**
- Repository overview
- Complete directory structure
- Navigation guide (for researchers, developers, publication)
- Quick reference table
- Git workflow status
- Version history

**Purpose:** Central navigation hub for the entire repository

---

## 🔄 What Changed (Visual)

### Layer Renumbering:

```
OLD:                    NEW:
S0-S6  (canonical)  →   S0-S6  (now FROZEN)
S7     (temporal)   →   S7     (now PREREGISTERED)
S8     (AVLAR)      →   S9     (AVLAR moved up)
                        S8     (Identity Gravity inserted)
```

### New Directories Created:

```
docs/
├── CFA-SYNC/          ← NEW (Phase 1 freeze docs)
├── S8/                ← NEW (Identity Gravity)
├── figures/ascii/     ← NEW (8 diagrams)
└── S7/preregistration/ ← NEW (experimental plan)

paper/                 ← NEW (entire directory)
├── workshop/
├── arxiv/
├── figures/
└── supplementary/
```

### Files Updated:

- `docs/NYQUIST_ROADMAP.md` - S8 insertion, S9 migration, all cross-refs
- `docs/S9/README.md` - Updated references (formerly S8)

---

## 🗺️ Navigation Patterns

### For Understanding Theory:

1. Start: `docs/CFA-SYNC/S0_S6_FROZEN_SPEC.md` (canonical foundation)
2. Then: `docs/S8/S8_IDENTITY_GRAVITY_SPEC.md` (new theory)
3. Finally: `docs/S7/preregistration/S7_PREREGISTRATION.md` (how to test it)

### For Running Experiments:

1. Start: `docs/S7/preregistration/S7_PROCEDURES.md` (step-by-step)
2. Reference: `docs/S7/preregistration/S7_METRICS.md` (definitions)
3. Log data: `docs/S7/preregistration/S7_DRIFT_LOG_TEMPLATE.json` (schema)

### For Writing Papers:

1. Start: `paper/workshop/README.md` OR `paper/arxiv/README.md`
2. Figures: `paper/figures/README.md`
3. Supplementary: `paper/supplementary/README.md`

### For Validating Integration:

1. Start: `IMPORT_LOG.md` (what changed)
2. Check: `docs/CFA-SYNC/PHASE_1_VALIDATION_CHECKLIST.md` (24 items)
3. Execute: `docs/CFA-SYNC/PHASE_1_FREEZE_HANDOFF.md` (git workflow)

---

## 📊 Repository Statistics

**Before integration:**
- ~70 files
- ~5,000 lines of documentation
- 6 canonical layers (S0-S6)

**After integration:**
- ~100+ files (+30%)
- ~15,000 lines of documentation (+200%)
- 7 canonical/semi-canonical layers (S0-S8)
- 32 new files created
- 8 ASCII diagrams
- Complete publication structure

---

## 🎯 Key Locations Summary

| What You Need | Where To Find It |
|---------------|------------------|
| Canonical spec | `docs/CFA-SYNC/S0_S6_FROZEN_SPEC.md` |
| Identity Gravity | `docs/S8/S8_IDENTITY_GRAVITY_SPEC.md` |
| Experiment plan | `docs/S7/preregistration/S7_PREREGISTRATION.md` |
| Validation checklist | `docs/CFA-SYNC/PHASE_1_VALIDATION_CHECKLIST.md` |
| Workshop paper | `paper/workshop/README.md` |
| ASCII diagrams | `docs/figures/ascii/` |
| What changed | `IMPORT_LOG.md` |
| Navigation | `REPO_MAP.md` |

---

## ⚠️ Important Rules

### S0-S6 Are FROZEN:

- ❌ No conceptual modifications
- ❌ No adding/removing core ideas
- ✅ Can add clarifying notes
- ✅ Can create S13, S14, etc. that extend them

### S7 Is PREREGISTERED:

- ❌ Can't change experimental plan
- ❌ Can't modify hypotheses
- ✅ Can document protocol deviations (if necessary with justification)
- ✅ Must report all results (positive, negative, null)

### S8 Is NEW CANONICAL:

- ✅ Publication-ready quality
- ✅ Testable predictions
- ✅ Integration with all layers verified
- ⏳ Awaiting empirical validation (S7 data)

### S9 Is EXPERIMENTAL:

- ✅ Can modify as needed
- ✅ Non-canonical status
- ✅ Future work, not locked

---

## 🚀 Next Steps

1. **Familiarize yourself** with the new structure (you're doing it now!)
2. **Check Folder_1** - Verify everything looks correct
3. **Review validation checklist** - 24 items to verify
4. **Get Nova's sign-off** - Share Folder_1 with Nova
5. **Commit Phase 1 freeze** - Make S0-S6 officially immutable

---

That's the complete repository structure! Everything is organized, documented, and ready. 🎉

🜁 Navigate with confidence.
