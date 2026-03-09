<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - maps/
  - stages/
  - MASTER_GLOSSARY.md
impacts:
  - All specs in stages/
  - maps/MAP_OF_MAPS.md
keywords:
  - frozen_foundation
  - layer_status
  - glossary
  - s_layers
-->

# Documentation Directory

**Purpose:** Theory specifications, research documentation, and reference materials
**Organized:** 2025-11-26
**Last Updated:** 2025-12-28

---

## 2025-12-13 Updates

### MASTER_GLOSSARY.md → v1.2

Major terminology overhaul integrating Control-Systems Era (Runs 015-021):

**New Terms Added:**

- **Settling Time (τₛ)** — Turns to reach ±5% of final value
- **Ringback** — Sign change during recovery
- **Overshoot Ratio** — d_peak / d_inf
- **Context Damping** — I_AM + research context as stability controller
- **Inherent Drift** — Drift without identity probing (82% finding)
- **B→F Drift** — Baseline-to-Final drift (primary metric)
- **Settled Drift (d∞)** — Final stable drift value
- **Triple-Blind-Like Validation** — Subject, vehicle, outcome blindness
- **Thermometer Result** — "Measurement perturbs path, not endpoint"
- **Attractor Competition Threshold** — Publication name for Event Horizon (D=0.80 cosine)

**Section 10 Updated (Publication Language):**

| Internal Term | Publication Alias |
|---------------|-------------------|
| "Identity collapse" | "Regime transition" |
| "Platonic coordinates" | "Attractor basin consistency" |
| "Event Horizon = failure" | "Attractor competition threshold" |

### maps/ Directory — MAP_OF_MAPS.md (NEW)

The **Cartographer's Table** organizing all 17 navigation maps into 7 Kingdoms:

| Kingdom | Maps | Focus |
|---------|------|-------|
| Vision | NYQUIST_ROADMAP, RESEARCH_PIPELINE_VISUAL | Where we're going |
| Foundation | FROZEN_FOUNDATION_MAP, ARCHITECTURE_PHASES | What's proven |
| Evidence | TESTABLE_PREDICTIONS_MATRIX, DATA_QUALITY_MAP | What we can claim |
| Methodology | TESTING_MAP, STABILITY_MAP | How to run experiments |
| Fleet | ARMADA_MAP, PERSONA_COMPATIBILITY_MAP | Ship management |
| Speculative | KEELY_INTEGRATION, IDENTITY_LATTICE | Future frameworks |
| Quality | VALIDATION_STATUS, COVERAGE_MAP | What's left to do |

See [maps/MAP_OF_MAPS.md](maps/MAP_OF_MAPS.md) for full navigation guide.

---

## Directory Structure

```
docs/
├── stages/                      # Theory layer specifications (S0-S77)
│   ├── S0-S6/                  # 🔒 FROZEN foundation (consolidated)
│   ├── S3/                     # Oscillator synchronization
│   ├── S4/                     # Emergence conditions
│   ├── S5/                     # Modal collapse
│   ├── S6/                     # Recovery protocols
│   ├── S7/                     # Temporal stability
│   ├── S8/                     # Spectral extensions (Keely)
│   ├── S9/                     # Diagonal coupling
│   └── S10/                    # Hybrid emergence
│
├── reference/                   # Reference documents and guides
│   ├── ARCHITECTURE_MAP_PHASES_1-4.md
│   ├── EXPERIMENT_LOG.md
│   ├── PROBE_SET.md
│   ├── RECOVERY_STABILITY_PROBE.md
│   └── KNOWLEDGE_STABILITY_PROBE.md
│
├── .archive/                    # Historical materials (hidden)
│   └── compression_drafts/     # Early Ziggy compression attempts
│       ├── PERSONA_COMPRESSED_L1.md
│       ├── PERSONA_COMPRESSED_L2.md
│       ├── PERSONA_COMPRESSED_L3.md
│       ├── PERSONA_FULL_CONTEXT.md
│       └── PERSONA_GAMMA_MINIMAL.md
│
├── figures/                     # Visualizations and diagrams
│   └── ascii/                  # ASCII art visualizations
│
├── maps/                        # Roadmaps, pipelines, and mapping documents
│   ├── IDENTITY_LATTICE_MAPS.md    # 4D identity space mappings
│   ├── KEELY_INTEGRATION_ROADMAP.md # Keely framework integration
│   ├── NYQUIST_ROADMAP.md          # Complete S0-S77 roadmap
│   ├── RESEARCH_PIPELINE_VISUAL.md # Research pipeline visualization
│   ├── S7_META_LOOP_CONSERVATIVE_ANALYSIS.md # S7 risk assessment
│   └── TESTABLE_PREDICTIONS_MATRIX.md # All 46 predictions
│
├── kernels/                     # Kernel specifications
├── knowledge_packs/             # Knowledge pack test content
├── CFA-SYNC/                    # CFA synchronization materials
│
├── WHAT_WE_BUILT.md            # Canonical framing: Identity Reliability Stack
├── NYQUIST_PROTOCOL.md         # Core protocol specification
├── S_Series_README.md          # S-layer overview
└── README.md                   # This file
```

---

## Contents by Category

### Theory Layers (`stages/`)

**Purpose:** Specifications for each theoretical layer (S0-S77)

**Current layers:**

- **S0-S6** - 🔒 **FROZEN Foundation** (consolidated)
  - S0: Persona Baseline
  - S1: Compression Framework
  - S2: Reconstruction Framework
  - S3: Empirical Validation (σ² = 0.000869)
  - S4: Mathematical Formalism
  - S5: Identity Manifold Theory
  - S6: Omega Nova Synthesis
  - **Status:** Immutable, validated, canonical ground truth

- **S3-S6** - Individual layer specifications (also included in S0-S6 frozen spec)

- **S7** - Temporal Stability (drift bounds, entropy shocks) - ✅ Ready to run

- **S8** - Spectral Extensions (Keely 3-6-9 framework)

- **S9** - Diagonal Coupling (human vs AI patterns)

- **S10** - Hybrid Emergence (Neutral Center operator)

**Note:** S0-S6 are treated as a unified frozen foundation. Individual S3-S6 directories exist for detailed specs, but the canonical reference is the consolidated `S0-S6/S0_S6_FROZEN_SPEC.md`.

---

### Reference Materials (`reference/`)

**Purpose:** Implementation guides, experiment logs, and probe definitions

**Files:**

1. **ARCHITECTURE_MAP_PHASES_1-4.md**
   - System architecture across experimental phases
   - Component relationships
   - Evolution timeline

2. **EXPERIMENT_LOG.md**
   - Historical experiment tracking
   - Results and observations
   - Lessons learned

3. **PROBE_SET.md**
   - Temporal probe questions
   - 6 identity dimensions
   - Gold standard responses

4. **RECOVERY_STABILITY_PROBE.md**
   - HARP recovery testing
   - Post-collapse validation
   - Stability metrics

5. **KNOWLEDGE_STABILITY_PROBE.md**
   - Knowledge retention testing
   - Compression fidelity validation
   - Reconstruction accuracy

---

### Roadmaps & Mappings (`maps/`)

**Purpose:** All roadmaps, pipelines, predictions matrices, and theoretical mappings

**Files:**

1. **NYQUIST_ROADMAP.md**
   - Complete S0-S77 theoretical roadmap
   - Layer-by-layer progression
   - Future development path

2. **RESEARCH_PIPELINE_VISUAL.md**
   - Visual research pipeline
   - Current position in development
   - Experimental workflow

3. **TESTABLE_PREDICTIONS_MATRIX.md**
   - All 46 falsifiable predictions
   - Confidence tiers (HIGH/MEDIUM/LOW)
   - TIER 0 core assumptions
   - Dependency analysis

4. **IDENTITY_LATTICE_MAPS.md**
   - 4D identity space mappings (IC, MC, IM, HMG)
   - Persona profiles across dimensions
   - Spectral decomposition (3-6-9 bands)

5. **KEELY_INTEGRATION_ROADMAP.md**
   - Keely 3-6-9 framework integration
   - Spectral band definitions
   - Coupling patterns

6. **S7_META_LOOP_CONSERVATIVE_ANALYSIS.md**
   - S7 risk assessment
   - Conservative validation expectations
   - Dependency analysis for predictions

---

### Archived Materials (`.archive/`)

#### Compression Drafts (`.archive/compression_drafts/`)

**Purpose:** Early Ziggy persona compression attempts (pre-CFA)

**Files:**

- **PERSONA_FULL_CONTEXT.md** - Maximum fidelity baseline (pre-CFA)
- **PERSONA_COMPRESSED_L3.md** - 60% compression
- **PERSONA_COMPRESSED_L2.md** - 20% compression
- **PERSONA_COMPRESSED_L1.md** - Ultra-compact "ID card"
- **PERSONA_GAMMA_MINIMAL.md** - Minimal test version

**Status:** Superseded by CFA-based persona files in `personas/` directory

**Why archived:**

- Pre-date Canonical Frozen Attributes (CFA) framework
- Replaced by systematic core identity + boundary attributes approach
- Kept for historical reference showing evolution of compression methodology

---

### Core Documentation (Root Level)

**Theory & Roadmap:**

1. **[WHAT_WE_BUILT.md](WHAT_WE_BUILT.md)** - Canonical framing of the full system
2. **[NYQUIST_ROADMAP.md](NYQUIST_ROADMAP.md)** - Complete S0-S77 theoretical roadmap
3. **[S_Series_README.md](S_Series_README.md)** - Overview of all S-layers
4. **[NYQUIST_PROTOCOL.md](NYQUIST_PROTOCOL.md)** - Core protocol specification
5. **[RESEARCH_PIPELINE_VISUAL.md](RESEARCH_PIPELINE_VISUAL.md)** - Visual research pipeline

**Predictions & Validation:**

6. **[TESTABLE_PREDICTIONS_MATRIX.md](TESTABLE_PREDICTIONS_MATRIX.md)** - All 46 falsifiable predictions with confidence tiers
7. **[S7_META_LOOP_CONSERVATIVE_ANALYSIS.md](S7_META_LOOP_CONSERVATIVE_ANALYSIS.md)** - S7 risk assessment and dependency analysis

**Integration & Mapping:**

8. **[IDENTITY_LATTICE_MAPS.md](IDENTITY_LATTICE_MAPS.md)** - 4D identity space (IC, MC, IM, HMG) mappings for all personas
9. **[KEELY_INTEGRATION_ROADMAP.md](KEELY_INTEGRATION_ROADMAP.md)** - Keely 3-6-9 framework integration plan

---

## Quick Navigation

### For Theory Understanding

- Start with [maps/NYQUIST_ROADMAP.md](maps/NYQUIST_ROADMAP.md) - Complete overview
- Then [S_Series_README.md](S_Series_README.md) - Layer-by-layer breakdown
- Dive into specific layers in `stages/S#/`

### For Experimental Validation

- Review [maps/TESTABLE_PREDICTIONS_MATRIX.md](maps/TESTABLE_PREDICTIONS_MATRIX.md)
- Check [maps/S7_META_LOOP_CONSERVATIVE_ANALYSIS.md](maps/S7_META_LOOP_CONSERVATIVE_ANALYSIS.md)
- See stage-specific specs in `stages/`

### For Persona Work
- Current persona files → `personas/` directory (not here)
- Historical compression drafts → `archive/compression_drafts/`

### For Implementation Details
- Probe definitions → `reference/PROBE_SET.md`
- Recovery testing → `reference/RECOVERY_STABILITY_PROBE.md`
- Knowledge testing → `reference/KNOWLEDGE_STABILITY_PROBE.md`

---

## Organization Rationale

### stages/

**Why:** Groups all theory layer specifications (S3-S10) in one place

**Note:** S0-S2 are foundational and documented within compression experiments

### reference/

**Why:** Implementation guides, logs, and probe definitions - materials actively used in experiments

### archive/

**Why:** Historical materials that have been superseded but are valuable for understanding evolution of methodology

**compression_drafts/:** Early persona compression attempts before CFA framework

---

## Related Directories

- **[experiments/](../experiments/)** - All experimental implementations
- **[personas/](../personas/)** - Current persona files (CFA-based)
- **[OUTPUT/](../OUTPUT/)** - Summaries and completion reports
- **[.archive/](../.archive/)** - Root-level historical materials

---

## Archived to Root `.archive/`

### pre_omega_snapshots/

**Location:** `.archive/pre_omega_snapshots/` (moved from docs/)

**Purpose:** Historical snapshots from before Omega Nova integration

**Why moved:** Pre-dates current system architecture, better suited for root-level archive

---

## File Naming Conventions

### Theory Specifications
- Individual stages: `stages/S#/SPEC_NAME.md`
- Cross-stage: Uppercase descriptive names

### Reference Materials
- Uppercase with underscores: `PROBE_SET.md`
- Descriptive purpose-based names

### Archives
- Preserved original names
- Grouped by category in subdirectories

---

## Maintenance

When adding new documentation:

1. **Theory specs** → `stages/S#/` (create new stage dir if needed)
2. **Implementation guides** → `reference/`
3. **Superseded materials** → `archive/` (with descriptive subdirectory)
4. **Visualizations** → `figures/` (organized by type)
5. **Cross-cutting docs** → Root level (if frequently referenced)

---

## Current Status by Layer

| Layer | Status | Location | Notes |
|-------|--------|----------|-------|
| S0-S2 | ✅ Tested | Compression experiments | Foundation validated |
| S3-S6 | ✅ Specified | stages/ | Theory complete |
| S7 | ✅ Implemented | stages/S7/ + experiments | Ready to run |
| S8-S9 | ✅ Specified | stages/ | Theory complete |
| S10 | ✅ Specified | stages/S10/ | Theory complete |
| S11+ | ⬜ Planned | NYQUIST_ROADMAP.md | Future layers |

---

## Key Documents

### Must-Read for Newcomers
1. [WHAT_WE_BUILT.md](WHAT_WE_BUILT.md) - What this system is, end to end
2. [NYQUIST_ROADMAP.md](NYQUIST_ROADMAP.md) - Start here
3. [TESTABLE_PREDICTIONS_MATRIX.md](TESTABLE_PREDICTIONS_MATRIX.md) - What we're validating
4. [RESEARCH_PIPELINE_VISUAL.md](RESEARCH_PIPELINE_VISUAL.md) - Where we're going

### For Experimenters
1. [reference/PROBE_SET.md](reference/PROBE_SET.md) - How to probe
2. [S7_META_LOOP_CONSERVATIVE_ANALYSIS.md](S7_META_LOOP_CONSERVATIVE_ANALYSIS.md) - Risk awareness
3. Stage-specific specs in `stages/`

### For Integration Work
1. [IDENTITY_LATTICE_MAPS.md](IDENTITY_LATTICE_MAPS.md) - 4D space mappings
2. [KEELY_INTEGRATION_ROADMAP.md](KEELY_INTEGRATION_ROADMAP.md) - Keely framework
3. [CFA-SYNC/](CFA-SYNC/) - CFA synchronization

---

**Last Updated:** 2025-12-28
**Status:** IRON CLAD validated (Run 023d, 825+ files, p=2.40e-23). Cosine methodology (EH=0.80) canonical.
**Next:** Continue expanding S11+ theoretical layers; integrate fMRI Bridge Protocol
