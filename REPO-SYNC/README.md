# REPO-SYNC

Cross-repository synchronization hub for the Nyquist Consciousness framework.

**Last Updated:** 2026-01-10

---

## Operation Frosty (Documentation Health) — START HERE

**frosty.py** is the documentation automation tool for cold-boot Claudes. It audits documentation health, validates links, checks term consistency, and monitors Claude session status.

### Quick Commands

```bash
# Full audit (recommended for cold boot)
py REPO-SYNC/frosty.py --audit

# Individual checks
py REPO-SYNC/frosty.py --validate-links      # Find broken markdown links
py REPO-SYNC/frosty.py --check-consistency   # Verify key term usage
py REPO-SYNC/frosty.py --plan-registry       # See active Claude work plans
py REPO-SYNC/frosty.py --session-health      # Check Claude session JSONL files
```

### What `--audit` Reports

| Score | What It Measures |
|-------|------------------|
| **Documentation freshness** | FROSTY_MANIFEST `last_reviewed` dates |
| **Link validity** | Broken markdown links `[text](path)` |
| **Term consistency** | Key terms match canonical values |
| **Plan registry** | Status of Claude work plans |
| **Session health** | Claude session JSONL files (crashes, size) |

### FROSTY_MANIFEST Format

Every major documentation file should include a manifest:

```markdown
<!-- FROSTY_MANIFEST
last_reviewed: 2026-01-10
depends_on:
  - ../README.md
  - ./related_file.md
impacts:
  - ../other_file.md
keywords:
  - key_concept_1
  - key_concept_2
-->
```

### Key Terms Checked

| Term | Expected Values |
|------|-----------------|
| Event Horizon | 0.80, D=0.80 |
| IRON CLAD | N=3 |
| Inherent drift | ~93%, 93% |
| Experiments count | 4505, 825 |

---

## Directory Structure

```
REPO-SYNC/
├── START_HERE.md                # Cold Boot Protocol for new Claudes
├── README.md                    # This file (REPO-SYNC overview)
├── frosty.py                    # Documentation health tool (v2.0)
├── add_frosty_manifests.py      # Batch FROSTY manifest insertion
├── MASTER_BRANCH_SYNC_IN.md     # Staging: main → Consciousness
├── MASTER_BRANCH_SYNC_OUT.md    # Staging: Consciousness → main
│
├── CFA/                   # Claude Field Array synchronization
│   ├── FOR_OMEGA_NOVA/    # Materials for Nova/Omega integration
│   ├── Lucian/            # Lucian collaboration materials
│   ├── Opus/              # Opus 4 review materials
│   └── *.md               # Phase 1 specs and handoffs
│
├── LATEX/                 # LaTeX technical writing toolkit
│   └── README.md          # Git clone reference (latex3/latex2e)
│
├── LLM_BOOK/              # NotebookLM-validated publication materials
│   ├── 0_SOURCE_MANIFESTS/  # STAGING + ingest.py + digest.py
│   ├── 1_VALIDATION/        # Review notes + analysis subdirs
│   │   ├── REVIEW_NOTES_*.md  # Batch review notes
│   │   ├── 1_DEEP_DIVES/      # Technical deep dives (--full mode)
│   │   ├── 2_FUTURE/          # Future research (--full mode)
│   │   └── 3_EXPERIMENTS/     # Experiment ideas (--full mode)
│   ├── 2_PUBLICATIONS/      # Publication-ready content by audience
│   ├── 3_VISUALS/           # Diagrams and visuals
│   ├── 4_AUDIO/             # Audio materials
│   └── RnD/                 # Non-Nyquist R&D content
│
├── Logos/                 # PXL/Logos formal verification & AGI safety
│   ├── Protopraxis/       # Core PXL implementation
│   │   └── formal_verification/coq/  # Coq proofs
│   ├── PXL_Global_Bijection.v  # Main theorem file
│   ├── *.md               # Documentation and specs
│   └── *.py               # Agent and demo scripts
│
├── PAN_HANDLERS/          # Pan Handlers integration
│   └── panhandlers_manifest.json
│
└── VUDU_FIDELITY/         # VuDu Fidelity Sync synchronization
    ├── Old/               # Legacy survey materials
    ├── Survey_update_2/   # Survey update v2
    └── Survey_update_3/   # Survey update v3 (current)
```

---

## Connected Repositories

| Repo | Purpose | Sync Frequency |
|------|---------|----------------|
| **CFA (Claude Field Array)** | Omega/Nova persona integration | As needed |
| **LATEX** | Technical writing, reports, arXiv submissions | On publication cycles |
| **LLM_BOOK** | NotebookLM-validated publications, external validation | On publication cycles |
| **Logos (PXL)** | Formal verification, AGI safety proofs, Coq theorems | As needed |
| **Pan Handlers** | Cross-repo orchestration manifest | On major releases |
| **VuDu Fidelity** | Survey and response pair generation | Per experiment cycle |

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

### LATEX Sync

LaTeX technical writing toolkit for publication-quality documents:

1. **Reference:** `latex3/latex2e` - Core LaTeX engine
2. **Use Cases:**
   - arXiv preprint submissions
   - Technical reports and white papers
   - Publication-ready academic documents
3. **Integration:** Works with WHITE-PAPER/ for final publication formatting

### LLM_BOOK Sync

NotebookLM-validated publication materials with accumulative ingestion pipeline:

1. **0_SOURCE_MANIFESTS/** - STAGING folders + ingestion scripts
   - `ingest.py` - STAGING → REVIEW_NOTES (supports `--full`, `--force`, `--batch`)
   - `digest.py` - STAGING → LLM_BOOK categories
2. **1_VALIDATION/** - Review notes + analysis subdirectories
   - `REVIEW_NOTES_*.md` - Batch-level review notes
   - `1_DEEP_DIVES/` - Technical deep dives (--full mode)
   - `2_FUTURE/` - Future research directions (--full mode)
   - `3_EXPERIMENTS/` - Experiment ideas (--full mode)
3. **2_PUBLICATIONS/** - Publication-ready content by audience
4. **3_VISUALS/** - Diagrams, framework images, mind maps
5. **4_AUDIO/** - Audio materials and transcripts
6. **RnD/** - Non-Nyquist R&D content (Hoffman, Gnostic, RAG)

**Key Integration:** LLM_BOOK feeds WHITE-PAPER/reviewers/packages/ via sync pipeline (v2.3):

```bash
cd WHITE-PAPER/calibration
py 1_sync_llmbook.py                        # Report mode
py 1_sync_llmbook.py --sync                 # Sync publications + validation + analysis
py 1_sync_llmbook.py --sync --include-visuals  # Also sync 3_VISUALS/
```

**Sync Mappings:**
- `2_PUBLICATIONS/*` → `llmbook/{category}/` (with `LLM_` prefix)
- `1_VALIDATION/REVIEW_NOTES_*.md` → `llmbook/validation/`
- `1_VALIDATION/1_DEEP_DIVES/*.md` → `llmbook/analysis/deep_dives/`
- `1_VALIDATION/2_FUTURE/*.md` → `llmbook/analysis/future/`
- `1_VALIDATION/3_EXPERIMENTS/*.md` → `llmbook/analysis/experiments/`
- `3_VISUALS/*` → `figures/generated/llmbook/` (with `--include-visuals`)

### Logos (PXL) Sync

Formal verification and AGI safety proofs:

1. **Protopraxis/** - Core PXL implementation
   - formal_verification/coq/ - Coq proof files (.v, .vo)
   - agent_boot.py - Agent bootstrapping
2. **PXL_Global_Bijection.v** - Main Global Bijection theorem
3. **LOGOS_Axiom_And_Theorem_Summary.md** - Axiom/theorem reference

### Pan Handlers Sync

Manifest for cross-repo dependencies:

- panhandlers_manifest.json - Declares which files need to sync where

### VuDu Fidelity Sync

Survey synchronization for response pair generation:

1. **Survey_update_3/** - Current active sync
   - AUTHENTIC_RESPONSE_PAIRS.json
   - generate_authentic_pairs.py

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
