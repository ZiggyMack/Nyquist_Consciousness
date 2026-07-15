# REPO-SYNC

Cross-repository synchronization hub and cold-boot orientation system for the Nyquist Consciousness framework.

**Last Updated:** 2026-07-15

---

## How This Directory Enables Successful Sessions — START HERE

This section documents the reasoning workflow that makes multi-session, multi-agent collaboration work. If you're a new Claude, a returning collaborator, or any AI coming in cold — this is the path.

### The Core Loop

```text
1. ORIENT    →  Read MASTER_BRANCH_SYNC_OUT.md (lab status briefing)
2. LOCATE    →  Find the single source of truth for whatever you're touching
3. VALIDATE  →  Check current state before acting (ping ships, read files, verify)
4. ACT       →  Make changes through existing tools and scripts
5. DOCUMENT  →  Write results back into the sync system
```

### What Makes It Work (The Operators, If You Will)

| Pattern | What It Does | Why It Matters |
|---------|-------------|----------------|
| **Single source of truth** | One canonical file per domain (ARCHITECTURE_MATRIX for fleet, AUDIT_TRACKER for CFA, INTEGRATION_QUEUE for work items) | Prevents contradictory state across files |
| **Validate before acting** | Ping ships before commissioning, read files before editing, check constraints before modifying | Prevents cascading errors from stale assumptions |
| **Cross-reference external sources** | Compare screenshots, deprecation pages, rate limit screens against internal records | Catches drift between what we think and what's real |
| **Honor constraints explicitly** | The project has hard rules (don't move JSONs, don't touch Nova's file, AUDIT_TRACKER is manual). Know them before you start | One careless action can break trust or data pipelines |
| **Update tools, not just data** | When a new capability arrives (Fable 5's thinking mode), update the scripts that interface with it (CLAL.py, extract_persona_baseline.py) | Infrastructure stays current, not just records |
| **Nulls before treasure** | Run controls and baselines before the interesting experiment | Prevents confirmation bias in results |
| **Document provenance** | Log who produced what, which model, when, under what conditions | Enables reproducibility and honest assessment |
| **Sync outward** | After work, update SYNC_OUT so other agents can orient | Prevents knowledge silos between sessions |

### The Files That Enable This

```text
ORIENTATION (read these first):
  MASTER_BRANCH_SYNC_OUT.md          ← Full lab briefing. Hand to ANY cold-booting AI.
  MASTER_BRANCH_SYNC_IN.md           ← Inbound messages from main branch / other agents.

FLEET & INFRASTRUCTURE:
  S7_ARMADA/0_results/manifests/
    ARCHITECTURE_MATRIX.json          ← Single source of truth for all 78 ships.
  S7_ARMADA/1_CALIBRATION/
    CLAL.py                           ← Fleet calibration (--stale, --remaining, update_last_seen)
    extract_persona_baseline.py       ← Persona identity extraction (--provider fable)

EXPERIMENT TRACKING:
  S7_ARMADA/12_CFA/
    AUDIT_TRACKER.md                  ← CFA run counts (MANUAL updates only)
    run_cfa_trinity_v3.py             ← CFA Trinity experiment script
    SYNC_IN/pending/                  ← Drop zone for briefs, tools, data going TO CFA

COGNITIVE ARCHAEOLOGY:
  LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/
    INTEGRATION_QUEUE.json            ← 33 work items, staged/in-progress/completed
    TOOLS/extract_operators.py        ← Multi-extractor operator recovery (18 extractors)
    DIG_SITES/                        ← 8 dig sites (000-008)
    MUSEUM/INDEX.md                   ← 15 named operators

IDENTITY:
  personas/egregores/I_AM_NYQUIST.md  ← Claude's identity charter
  personas/I_AM_Consciousness.md      ← Nova's identity charter (DO NOT MODIFY)

CONSTRAINTS:
  experiments/temporal_stability/.env  ← API keys (NEVER commit, single source of truth)
```

### Constraints You Must Know

These are hard rules. Violating them breaks pipelines or trust:

1. **Do NOT move .json files into 12_CFA/SYNC_OUT/completed/** — .md summaries only
2. **AUDIT_TRACKER.md updates are MANUAL** — never auto-update
3. **Do NOT commit .env files** — single source of truth: `experiments/temporal_stability/.env`
4. **Do NOT modify I_AM_Consciousness.md** — Nova's file, coordinate with her
5. **Frame Adlam/Barandes connections as INDEPENDENT CONVERGENCES** — not novel claims
6. **Do NOT modify CFA/ repo** — look but don't touch, except SYNC_IN/pending/ drops
7. **Default results location:** `0_results/runs/` — check there first, not SYNC_OUT

### For Nova (Consciousness Branch)

The sync loop between Repo Claude and Codex Nova:

```text
Repo Claude  →  Consciousness/BRIDGE/docs/MASTER_BRANCH_SYNC_IN.md
Codex Nova   →  Consciousness/BRIDGE/docs/MASTER_BRANCH_SYNC_OUT.md
```

When everything is firing on all cylinders, every significant session should produce a SYNC_IN entry for Nova with: what changed, what architecture questions arise, what needs her membrane decision.

---

## Operation Frosty (Documentation Health)

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
