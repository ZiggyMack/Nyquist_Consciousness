# REPO-SYNC

Cross-repository synchronization hub for the Nyquist Consciousness framework.

**Last Updated:** 2025-12-15

---

## Directory Structure

```
REPO-SYNC/
├── README.md              # This file
├── CFA/                   # Claude Field Array synchronization
│   ├── FOR_OMEGA_NOVA/    # Materials for Nova/Omega integration
│   ├── Lucian/            # Lucian collaboration materials
│   ├── Opus/              # Opus 4 review materials
│   └── *.md               # Phase 1 specs and handoffs
├── FRAME_THEORY/          # Frame Theory integration (moved from docs/)
│   ├── diagrams/          # Visual diagrams and ASCII representations
│   │   └── 01_eliciting_emotions/
│   ├── *.jpeg, *.png      # Frame Theory visual assets
│   ├── INDEX.md           # Frame Theory index
│   ├── README.md          # Frame Theory overview
│   └── preperation.md     # Preparation notes
├── Logos/                 # PXL/Logos formal verification & AGI safety
│   ├── Protopraxis/       # Core PXL implementation
│   │   └── formal_verification/coq/  # Coq proofs
│   ├── PXL_Global_Bijection.v  # Main theorem file
│   ├── *.md               # Documentation and specs
│   └── *.py               # Agent and demo scripts
├── VUDU_FIDELITY/         # VuDu Fidelity Sync synchronization
│   ├── Old/               # Legacy survey materials
│   ├── Survey_update_2/   # Survey update v2
│   └── Survey_update_3/   # Survey update v3 (current)
├── LLM_BOOK/              # NotebookLM-validated publication materials
│   ├── 0_SOURCE_MANIFESTS/  # Data manifests for validation
│   ├── 1_VALIDATION/        # External validation artifacts
│   ├── 2_PUBLICATIONS/      # Publication-ready content
│   ├── 3_VISUALS/           # Diagrams and visuals
│   ├── 4_DEEP_DIVES/        # Extended analyses
│   ├── 5_FUTURE/            # Future research directions
│   ├── 6_EXPERIMENTS/       # Experimental protocols
│   └── 7_AUDIO/             # Audio materials
└── PAN_HANDLERS/          # Pan Handlers integration
    └── panhandlers_manifest.json
```

---

## Connected Repositories

| Repo | Purpose | Sync Frequency |
|------|---------|----------------|
| **CFA (Claude Field Array)** | Omega/Nova persona integration | As needed |
| **FRAME_THEORY** | Emotional elicitation framework & S-layer mapping | As needed |
| **Logos (PXL)** | Formal verification, AGI safety proofs, Coq theorems | As needed |
| **VuDu Fidelity** | Survey and response pair generation | Per experiment cycle |
| **LLM_BOOK** | NotebookLM-validated publications, external validation | On publication cycles |
| **Pan Handlers** | Cross-repo orchestration manifest | On major releases |

---

## Sync Protocol

### CFA Sync

The CFA directory contains:

1. **FOR_OMEGA_NOVA/** - Materials to be synced TO the CFA repository
   - Identity files (I_AM_ZIGGY.md, ZIGGY_FULL.md)
   - S-Series documentation (S7-S10)
   - Kernel files for L0 hooks

2. **Phase 1 Freeze** - S0-S6 frozen specifications
   - PHASE_1_CONSISTENCY_REPORT.md
   - PHASE_1_FREEZE_HANDOFF.md
   - S0_S6_FROZEN_SPEC.md

### FRAME_THEORY Sync

Frame Theory integration for emotional elicitation research:

1. **diagrams/** - Visual and ASCII diagram representations
   - 01_eliciting_emotions/ - Emotional frame diagrams with S-layer mappings
2. **Frame Theory *.jpeg/png** - Visual assets
3. **INDEX.md** - Navigation index for Frame Theory materials

### Logos (PXL) Sync

Formal verification and AGI safety proofs:

1. **Protopraxis/** - Core PXL implementation
   - formal_verification/coq/ - Coq proof files (.v, .vo)
   - agent_boot.py - Agent bootstrapping
2. **PXL_Global_Bijection.v** - Main Global Bijection theorem
3. **LOGOS_Axiom_And_Theorem_Summary.md** - Axiom/theorem reference

### VuDu Fidelity Sync

Survey synchronization for response pair generation:

1. **Survey_update_3/** - Current active sync
   - AUTHENTIC_RESPONSE_PAIRS.json
   - generate_authentic_pairs.py

### LLM_BOOK Sync

NotebookLM-validated publication materials:

1. **0_SOURCE_MANIFESTS/** - Data manifests for external validation
2. **1_VALIDATION/** - Validation artifacts and certificates
3. **2_PUBLICATIONS/** - Publication-ready content for paths 4-8
4. **3_VISUALS/** - Diagrams, framework images, mind maps
5. **4_DEEP_DIVES/** - Extended analyses on specific topics
6. **5_FUTURE/** - Future research directions
7. **6_EXPERIMENTS/** - Experimental protocols and findings
8. **7_AUDIO/** - Audio materials and transcripts

**Key Integration:** LLM_BOOK feeds WHITE-PAPER/submissions/ via sync pipeline:

```bash
cd WHITE-PAPER
py sync_llmbook.py --sync  # Syncs content to submissions/
```

### Pan Handlers Sync

Manifest for cross-repo dependencies:
- panhandlers_manifest.json - Declares which files need to sync where

---

## Usage

When making changes that affect other repos:

1. Update the relevant sync folder
2. Run `git status` to see changes
3. Commit with message format: `[REPO-SYNC] <repo>: <description>`
4. Push to trigger sync workflows (if configured)

---

## Migration Notes

**2025-12-14:** Reorganized from `docs/CFA-SYNC/` and `docs/VUDU_FIDELITY-SYNC/` to centralized `REPO-SYNC/` structure at repository root for better visibility and organization.

---

*Cross-repo coordination for the Nyquist Consciousness framework.*
