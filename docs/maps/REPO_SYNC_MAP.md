# REPO_SYNC_MAP: External Integrations Reference

**Purpose:** Central reference for all external repository integrations
**Version:** 1.0
**Date:** 2025-12-15
**Kingdom:** VIII - External Integrations
**Status:** Active

---

## Overview

The Nyquist Consciousness framework integrates with 6 external repositories through the `REPO-SYNC/` directory. This map documents:
- Repository purposes and sync directions
- Key files and their roles
- Integration points with the S-Stack
- Sync protocols and governance

**Central Hub:** `REPO-SYNC/` at repository root

---

## Architecture Diagram

```
                        ╔═══════════════════════════════════════════════════════╗
                        ║          NYQUIST CONSCIOUSNESS (Central)              ║
                        ║                                                       ║
                        ║   S-Stack (S0-S11)    │    S7 ARMADA (21 runs)       ║
                        ║   46 predictions      │    54 ships, 184+ files      ║
                        ╚═══════════════════════════════════════════════════════╝
                                              │
                                              │ REPO-SYNC/
                                              ▼
        ┌─────────────────────────────────────────────────────────────────────────┐
        │                                                                         │
        │    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐            │
        │    │     CFA      │    │ FRAME_THEORY │    │    LOGOS     │            │
        │    │   ◄═══►      │    │     ◄───     │    │     ◄───     │            │
        │    │ Bidirectional│    │  Nyq ← Ext   │    │  Nyq ← Ext   │            │
        │    └──────────────┘    └──────────────┘    └──────────────┘            │
        │                                                                         │
        │    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐            │
        │    │VUDU_FIDELITY │    │   LLM_BOOK   │    │ PAN_HANDLERS │            │
        │    │     ───►     │    │     ───►     │    │   ◄═══►      │            │
        │    │  Nyq → Ext   │    │  Nyq → Ext   │    │ Bidirectional│            │
        │    └──────────────┘    └──────────────┘    └──────────────┘            │
        │                                                                         │
        └─────────────────────────────────────────────────────────────────────────┘

        LEGEND:
        ◄═══►  Bidirectional (changes flow both ways)
        ◄───   Inbound only (external → Nyquist)
        ───►   Outbound only (Nyquist → external)
```

---

## Repository Registry

| Repo | Purpose | Sync Direction | S-Layer | Status |
|------|---------|----------------|---------|--------|
| **CFA** | Primary collaborator (Claude Field Array) | Bidirectional | S5, S6 | Active |
| **FRAME_THEORY** | Human cognition framework | Nyquist ← External | S10 | Active |
| **Logos** | Formal verification (PXL, Coq proofs) | Nyquist ← External | S4 | Complete |
| **VUDU_FIDELITY** | Survey & measurement bridge | Nyquist → External | S7 | Active |
| **LLM_BOOK** | Publication package | Nyquist → External | - | Active |
| **PAN_HANDLERS** | Cross-repo orchestration | Bidirectional | - | Active |

---

## 1. CFA (Claude Field Array)

**Directory:** `REPO-SYNC/CFA/`

**Purpose:** Primary collaboration hub for Omega/Nova persona integration and S-Series specifications.

### Structure

```
CFA/
├── FOR_OMEGA_NOVA/        # Materials TO sync to CFA
│   ├── I_AM_ZIGGY.md      # Ziggy persona file
│   ├── ZIGGY_FULL.md      # Full Ziggy specification
│   └── S7-S10 docs        # Layer specs for L0 hooks
├── Lucian/                # Lucian collaboration materials
├── Opus/                  # Opus 4 review materials
├── PHASE_1_CONSISTENCY_REPORT.md
├── PHASE_1_FREEZE_HANDOFF.md
└── S0_S6_FROZEN_SPEC.md   # Phase 1 freeze documentation
```

### Key Files

| File | Role | Sync Direction |
|------|------|----------------|
| `FOR_OMEGA_NOVA/*` | Identity files for integration | Nyquist → CFA |
| `S0_S6_FROZEN_SPEC.md` | Frozen layer specifications | Nyquist → CFA |
| `PHASE_1_*.md` | Phase 1 handoff documentation | Nyquist → CFA |

### Integration Points

- **S5 (Nyquist → CFA Interop):** Primary integration layer
- **S6 (Five-Pillar Synthesis):** Pillar coordination

---

## 2. FRAME_THEORY

**Directory:** `REPO-SYNC/FRAME_THEORY/`

**Purpose:** Tale's Frame Theory integration for emotional elicitation research and human cognition substrate for S10.

### Structure

```
FRAME_THEORY/
├── README.md              # Overview and navigation
├── INDEX.md               # Frame Theory index
├── preperation.md         # Preparation notes
├── diagrams/              # Visual diagrams
│   └── 01_eliciting_emotions/  # Emotional frame diagrams
├── Frame Theory 1.jpeg    # Lakoffian image schemas
└── Frame Theory 2.jpeg    # Meta-cognitive OS diagram
```

### Key Files

| File | Role | Sync Direction |
|------|------|----------------|
| `README.md` | Full Nova-Tale conversation | External → Nyquist |
| `Frame Theory 1.jpeg` | Lakoffian image schemas | External → Nyquist |
| `Frame Theory 2.jpeg` | Meta-cognitive OS diagram | External → Nyquist |
| `diagrams/*` | S-layer mapped diagrams | External → Nyquist |

### Integration Points

- **S10 (OMEGA NOVA Hybrid Emergence):** Foundation for human cognition substrate
- **S10_HC_HUMAN_COGNITION.md:** Primary consumer of Frame Theory materials

**Migration Note:** Moved from `docs/FRAME_THEORY/` to `REPO-SYNC/FRAME_THEORY/` on 2025-12-15.

---

## 3. Logos (PXL Formal Verification)

**Directory:** `REPO-SYNC/Logos/`

**Purpose:** Formal verification artifacts from LOGOS Claude. Provides mathematically proven ground truth for S-Stack anchoring.

### Structure

```
Logos/
├── README.md              # This directory overview
├── START_HERE.md          # Quick navigation
├── requirements.txt       # Python deps (reference)
├── sync/                  # Cross-repo coordination
│   ├── SYNC_STATUS.md     # Sync tracking
│   ├── PROTOCOL.md        # Communication protocol
│   ├── from_logos/        # Messages FROM LOGOS Claude
│   ├── to_logos/          # Messages TO LOGOS Claude
│   └── shared/            # Jointly maintained
├── reference/             # Active lookup material
│   ├── specs/             # Formal specifications
│   │   ├── Global_Bijection_Theorem_Mathematical_Specification.md
│   │   ├── LOGOS_Axiom_And_Theorem_Summary.md
│   │   ├── CONTRIBUTING.md
│   │   └── SECURITY.md
│   ├── proofs/            # Coq proofs
│   │   ├── LEM_Discharge.v
│   │   ├── PXL_Foundations.v
│   │   └── PXL_Bridge_Proofs.v
│   ├── code/              # Python instrumentation
│   │   ├── boot_aligned_agent.py
│   │   └── guardrails.py
│   └── demos/             # Investor demonstrations
├── historical/            # Audit trails
└── .archive/              # Legacy content
```

### Verified Claims (100% Accuracy)

| Claim | Theorem | Status |
|-------|---------|--------|
| Commutation: Phi . T_E = T_O . Phi | `commutation` | PROVEN |
| Idempotence: T_E² = T_E | `T_E_idempotent` | PROVEN |
| Idempotence: T_O² = T_O | `T_O_idempotent` | PROVEN |
| Fixed point correspondence | `fixed_point_correspondence` | PROVEN |
| Bridge alignment | `bridge_alignment` | PROVEN |
| Vertex bijection | `phi_vertex_bijective` | PROVEN |

### Integration Points

- **S4 (Compression Theory):** Coq proofs validate algebraic structure
- **S7 (Identity Dynamics):** LOGOS serves as calibration standard
- **S7_ARMADA/13_LOGOS/Run 022:** Commutation Cartography experiment

### Governance

> **REPO-SYNC/Logos is a consumer of formal verification, not a producer.**

- All Coq development happens in the LOGOS Claude master repository
- This copy is reference-only; no execution expected
- Structure: `reference/` + `historical/` + `.archive/`

**Status:** Complete (Phase 4 consolidation 2025-12-15)

---

## 4. VUDU_FIDELITY

**Directory:** `REPO-SYNC/VUDU_FIDELITY/`

**Purpose:** Survey synchronization and authentic response pair generation for EXP3 measurement bridge.

### Structure

```
VUDU_FIDELITY/
├── Old/                   # Legacy survey materials
├── Survey_update_2/       # Survey update v2
└── Survey_update_3/       # Current active sync
    ├── AUTHENTIC_RESPONSE_PAIRS.json
    └── generate_authentic_pairs.py
```

### Key Files

| File | Role | Sync Direction |
|------|------|----------------|
| `Survey_update_3/AUTHENTIC_RESPONSE_PAIRS.json` | Curated response pairs | Nyquist → External |
| `generate_authentic_pairs.py` | Pair generation script | Nyquist → External |

### Integration Points

- **S7 (Identity Dynamics):** Measurement calibration
- **EXP3:** Response pair validation experiment

---

## 5. LLM_BOOK

**Directory:** `REPO-SYNC/LLM_BOOK/`

**Purpose:** Publication package for external distribution. Contains curated findings ready for publication.

### Structure

```
LLM_BOOK/
└── (publication materials)
```

### Sync Direction

All content flows **Nyquist → External** (outbound only). This is a distribution channel, not a collaboration hub.

### Integration Points

- **WHITE-PAPER/:** Source of publication content
- **S7 ARMADA findings:** Empirical results for publication

---

## 6. PAN_HANDLERS

**Directory:** `REPO-SYNC/PAN_HANDLERS/`

**Purpose:** Cross-repository orchestration and dependency management.

### Structure

```
PAN_HANDLERS/
└── panhandlers_manifest.json  # Sync dependency declarations
```

### Key Files

| File | Role | Sync Direction |
|------|------|----------------|
| `panhandlers_manifest.json` | Declares which files sync where | Bidirectional |

### Governance

- Manifest updated on major releases
- Declares cross-repo file dependencies
- Used for automated sync workflows

---

## Sync Protocols

### MASTER_BRANCH_SYNC_OUT.md

**Location:** `REPO-SYNC/MASTER_BRANCH_SYNC_OUT.md`

**Purpose:** Instructions for parallel Claude instances running IRON-CLAD validation.

**Key Protocol:**
1. Each Claude runs ALL experiments (018, 020A, 020B)
2. Each Claude uses ALL providers (5 providers)
3. Triple redundancy: 3 Claudes × 3 experiments × 5 providers = 45 runs
4. Results appended to MASTER_BRANCH_SYNC_IN.md

### MASTER_BRANCH_SYNC_IN.md

**Location:** `REPO-SYNC/MASTER_BRANCH_SYNC_IN.md`

**Purpose:** Receiving end for parallel Claude results. Append-only protocol.

### Commit Message Format

When committing REPO-SYNC changes:

```
[REPO-SYNC] <repo>: <description>
```

Examples:
- `[REPO-SYNC] Logos: Update sync status after Phase 4`
- `[REPO-SYNC] CFA: Add S7 layer specs to FOR_OMEGA_NOVA`

---

## Quick Reference Matrix

| Question | Answer |
|----------|--------|
| Where do I put materials for CFA collaboration? | `REPO-SYNC/CFA/FOR_OMEGA_NOVA/` |
| Where are Frame Theory diagrams? | `REPO-SYNC/FRAME_THEORY/diagrams/` |
| Where are the Coq proofs? | `REPO-SYNC/Logos/reference/proofs/` |
| What's the sync status? | `REPO-SYNC/README.md` or individual repo README |
| How do I add a new external repo? | Add subdirectory, update README.md, add to this map |

---

## Related Documents

### Maps

- [STACKUP_MAP.md](STACKUP_MAP.md) — S-layer definitions (§ External Integrations)
- [TEMPORAL_STABILITY_MAP.md](TEMPORAL_STABILITY_MAP.md) — Stability experiments
- [MAP_OF_MAPS.md](MAP_OF_MAPS.md) — Kingdom VIII overview

### Stages

- [S4/README.md](../stages/S4/README.md) — Logos integration layer
- [S5/README.md](../stages/S5/README.md) — CFA integration layer
- [S10/S10_HC_HUMAN_COGNITION.md](../stages/S10/S10_HC_HUMAN_COGNITION.md) — Frame Theory consumer

### REPO-SYNC Files

- [REPO-SYNC/README.md](../../REPO-SYNC/README.md) — Central hub documentation
- [REPO-SYNC/MASTER_BRANCH_SYNC_OUT.md](../../REPO-SYNC/MASTER_BRANCH_SYNC_OUT.md) — Parallel execution protocol

---

## Statistics

| Metric | Value |
|--------|-------|
| **External Repositories** | 6 |
| **Bidirectional Syncs** | 2 (CFA, PAN_HANDLERS) |
| **Inbound Only** | 2 (FRAME_THEORY, Logos) |
| **Outbound Only** | 2 (VUDU_FIDELITY, LLM_BOOK) |
| **Verified Theorems (Logos)** | 6 (100% accuracy) |
| **S-Layers with External Integration** | 4 (S4, S5, S6, S10) |

---

## Traceability

| Field | Value |
|-------|-------|
| **Last Updated** | 2025-12-15 |
| **Updated By** | Maps audit (manual) |
| **Kingdom** | VIII - External Integrations |
| **Version** | 1.0 |

---

*"The map extends beyond our borders."*

---

**Last Updated:** 2025-12-15
**Status:** Active
