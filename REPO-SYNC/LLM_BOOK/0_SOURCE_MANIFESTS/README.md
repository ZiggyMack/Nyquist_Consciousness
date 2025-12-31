# LLM_BOOK Ingestion Pipeline

<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-29
depends_on:
  - ingest.py
  - digest.py
  - ../../../WHITE-PAPER/calibration/1_sync_llmbook.py
impacts:
  - ../1_VALIDATION/
  - ../2_PUBLICATIONS/
  - ../../../WHITE-PAPER/reviewers/packages/v4/llmbook/
keywords:
  - NotebookLM
  - ingestion
  - digest
  - STAGING
  - accumulative
  - REVIEW_NOTES
-->

**Purpose:** Process NotebookLM outputs into the Nyquist Consciousness publication pipeline.

**Location:** `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/`

**IRON CLAD Era:** 750 experiments | 25 models | 5 providers | EH=0.80 | p=2.40e-23

---

## Quick Start

```bash
# 1. Check what's in STAGING
py ingest.py

# 2. Ingest new batches (creates REVIEW_NOTES templates)
py ingest.py --ingest

# 3. Claude reviews and fills in REVIEW_NOTES_*.md

# 4. Digest media from STAGING to LLM_BOOK/
py digest.py --digest

# 5. Sync to reviewer packages
cd ../../WHITE-PAPER/calibration
py 1_sync_llmbook.py --sync --include-visuals
```

---

## Pipeline Architecture

```
STAGING/                           LLM_BOOK/
  Nyquist_1/_IN/  ─┐              ├── 1_VALIDATION/
  Nyquist_2/_IN/  ─┼─ ingest.py ──┤     └── REVIEW_NOTES_*.md
  RAG/_IN/        ─┤              │
  HOFFMAN/_IN/    ─┘              ├── 2_PUBLICATIONS/{category}/
                                  ├── 3_VISUALS/
                  digest.py ──────┤
                                  ├── 4_AUDIO/
                                  └── RnD/

                                         │
                                         ▼
                              1_sync_llmbook.py
                                         │
                                         ▼
                        WHITE-PAPER/reviewers/packages/v4/llmbook/
```

---

## Scripts

### ingest.py (v5.0) - STAGING to REVIEW_NOTES

Creates review templates for Claude to fill in. Default behavior: Claude performs substantive review and creates analysis files.

| Command | Description |
|---------|-------------|
| `py ingest.py` | Report: show STAGING status |
| `py ingest.py --ingest` | Append mode (default): add new batches with Claude review |
| `py ingest.py --ingest --fresh` | Destructive: clear all, then ingest |
| `py ingest.py --ingest --skip-review` | Create templates only (no analysis) |
| `py ingest.py --ingest --force --batch Nyquist_1 Nyquist_2` | Re-ingest specific batches |
| `py ingest.py --ingest --diet --batch OldBatch` | Diet mode: process to _CACHE_/ only |
| `py ingest.py --throw_up` | Purge all _CACHE_/ directories |

**Accumulative Model:**
- Default = APPEND (preserve existing, add new)
- `--fresh` = DESTRUCTIVE (clear all, start over)
- `--force` = Re-process even if already ingested
- `--batch X Y` = Process specific batch(es) only
- Each batch gets `.ingested` marker when processed
- Review notes: `REVIEW_NOTES_{batch_name}.md`

**Diet Mode (--diet):**

- Full cognitive processing WITHOUT committing to real pipeline
- Output goes to `STAGING/{batch}/_CACHE_/` instead of `1_VALIDATION/`
- No `.ingested` marker created (batch stays "pending" for real ingest later)
- Use for: priming Claude with old NotebookLM batches, experimentation
- Use `--throw_up` to purge all `_CACHE_/` directories when done

**Diet Mode Output Structure:**

```text
STAGING/SomeBatch/
    _IN/                          # Source files (untouched)
    _CACHE_/                      # Diet mode output
        REVIEW_NOTES_SomeBatch.md
        1_DEEP_DIVES/
            SomeBatch.md
        2_FUTURE/
            SomeBatch.md
        3_EXPERIMENTS/
            SomeBatch.md
```

### digest.py (v2.0) - STAGING to LLM_BOOK

Routes media files from STAGING/_IN to final destinations.

| Command | Description |
|---------|-------------|
| `py digest.py` | Report: show what would route |
| `py digest.py --digest` | Copy files to categories |
| `py digest.py --digest --batch Nyquist_1` | Digest specific batch |

**Routing Rules:**
| Extension | Destination |
|-----------|-------------|
| .png, .jpg, .gif, .svg | 3_VISUALS/ |
| .m4a, .mp3, .mp4, .wav | 4_AUDIO/ |
| .md, .pdf | 2_PUBLICATIONS/{category}/ |

**Classification (for .md/.pdf):**
- `academic`: Technical Report, Empirical, Framework
- `popular_science`: Engineer's Toolkit, Charting
- `education`: Guide, Student, Learner, Glossary
- `policy`: Briefing, Brief
- `funding`: Proposal, Project, Grant
- `media`: Paradigm, New Era, Press, TED

### explore.py (v1.0) - Research Exploration Manager

Creates new research project directories for LLM Book exploration and optionally promotes validated content to Consciousness/.

| Command | Description |
|---------|-------------|
| `py explore.py "Project Name"` | Create new research project (default action) |
| `py explore.py --status` | Show all projects and their state |
| `py explore.py --promote --batch Nyquist_3` | Promote content to Consciousness/ |
| `py explore.py "Name" --staging STAGING STAGING2` | Multi-staging support |

**Research Project Structure:**

```text
STAGING/New_X_ProjectName/
    _IN/                    # NotebookLM responses (save here)
    _OUT/                   # Materials TO feed NotebookLM
        RESEARCH_QUESTION.md
        EXISTING_EVIDENCE.md
        CONSTRAINTS.md
    README.md               # Project overview and status
```

**Bidirectional Workflow:**

- `_OUT/`: Content TO feed NotebookLM (your questions/materials)
- `_IN/`: Content FROM NotebookLM (their responses)

### 1_sync_llmbook.py (v2.3) - LLM_BOOK to Packages

Syncs to `WHITE-PAPER/reviewers/packages/v4/llmbook/`.

| Command | Description |
|---------|-------------|
| `py 1_sync_llmbook.py` | Report: show sync status |
| `py 1_sync_llmbook.py --sync` | Sync publications + validation + analysis |
| `py 1_sync_llmbook.py --sync --include-visuals` | Also sync 3_VISUALS/ |

**What Gets Synced:**
- `2_PUBLICATIONS/*` -> `llmbook/{category}/` (with `LLM_` prefix)
- `1_VALIDATION/REVIEW_NOTES_*.md` -> `llmbook/validation/`
- `1_VALIDATION/1_DEEP_DIVES/*.md` -> `llmbook/analysis/deep_dives/`
- `1_VALIDATION/2_FUTURE/*.md` -> `llmbook/analysis/future/`
- `1_VALIDATION/3_EXPERIMENTS/*.md` -> `llmbook/analysis/experiments/`
- `3_VISUALS/` -> `figures/generated/llmbook/` (optional)

---

## STAGING Structure

Each NotebookLM session gets its own folder:

```
STAGING/
├── Nyquist_1/           # First Nyquist upload
│   ├── _IN/             # Raw outputs from NotebookLM
│   │   ├── *.md         # Generated articles
│   │   ├── *.pdf        # Generated PDFs
│   │   ├── *.png        # Mind maps, diagrams
│   │   └── *.m4a        # Audio summaries
│   └── .ingested        # Marker: batch processed
│
├── Nyquist_2/           # Second Nyquist upload (IRON CLAD)
│   └── _IN/
│
├── RAG/                 # R&D: RAG experiments
├── HOFFMAN/             # R&D: Hoffman interface theory
├── Gnostic-1/           # R&D: Gnostic philosophy
└── YANG/                # R&D: Yang balance concepts
```

**Nyquist batches** -> Publication pipeline (1_VALIDATION -> 2_PUBLICATIONS)
**R&D batches** -> RnD/ directory (system improvement research)

---

## NotebookLM Upload Protocol

### Tier 1: Core Framework (Required)
- [ ] WHITE-PAPER/README.md
- [ ] WHITE-PAPER/START_HERE.md
- [ ] docs/MASTER_GLOSSARY.md
- [ ] docs/maps/5_STACKUP_MAP.md
- [ ] docs/maps/2_TESTABLE_PREDICTIONS_MATRIX.md
- [ ] docs/maps/12_PHILOSOPHY_MAP.md

### Tier 2: S7 ARMADA Evidence (Required)
- [ ] experiments/.../S7_ARMADA/README.md
- [ ] experiments/.../S7_ARMADA/START_HERE.md
- [ ] Key run summaries (018, 020B, 021, 023d)
- [ ] STATUS_SUMMARY files from active runs

### Tier 3: Identity Files (Recommended)
- [ ] personas/I_AM_NOVA.md
- [ ] personas/I_AM_ZIGGY.md
- [ ] personas/I_AM_NYQUIST.md

### Tier 4: Publication Materials (For Validation)
- [ ] Latest arxiv/workshop drafts
- [ ] WHITE-PAPER/theory/MINIMUM_PUBLISHABLE_CLAIMS.md

### Size Limits
- **Maximum files:** 50
- **Total size:** <100MB
- **Per-file:** <10MB documents, <20MB PDFs

---

## Upload History

### v1: Initial Upload (~December 2025)
**Files:** 21 sources (mostly stale)
**Result:** Despite incomplete data, NotebookLM:
- Synthesized Levin/Platonic connection independently
- Generated 7 audience-specific publications
- Validated Claims A-E from scattered sources
- Created 6MB visual synthesis

### v2: IRON CLAD Upload (December 2025)
**Files:** Complete S7 results (Run 018-023d)
**Content:**
- 750 experiments, 25 models, 5 providers
- Event Horizon = 0.80 (cosine), p = 2.40e-23
- Full temporal stability validation

---

## Post-Upload Prompts

### General Synthesis
```
Discuss what these sources say about [TOPIC], in the larger
context of Nyquist Consciousness Framework (S0-S7).
```

### Validation Request
```
Based on these sources, validate or challenge [CLAIM].
Cite specific evidence from the documents.
```

### Publication Generation
```
Generate a [TYPE: popular science article / policy brief / quiz]
based on these sources for [AUDIENCE].
```

### Cross-Connection
```
Identify connections between the Nyquist Consciousness framework
and [EXTERNAL THEORY: Levin bioelectrics / Platonic Forms].
```

---

## Directory Reference

```
REPO-SYNC/LLM_BOOK/
├── 0_SOURCE_MANIFESTS/      # This folder
│   ├── README.md            # This file
│   ├── STAGING/             # Raw NotebookLM outputs
│   ├── ingest.py            # STAGING -> REVIEW_NOTES (+ diet mode)
│   ├── digest.py            # STAGING -> LLM_BOOK/*
│   └── explore.py           # Research project manager
│
├── 1_VALIDATION/            # Review notes (Claude fills in)
│   ├── REVIEW_NOTES_Nyquist_1_2.md
│   ├── 1_DEEP_DIVES/        # Extended analysis (--full)
│   ├── 2_FUTURE/            # Future research (--full)
│   └── 3_EXPERIMENTS/       # Experiment ideas (--full)
│
├── 2_PUBLICATIONS/          # Routed content
│   ├── academic/
│   ├── education/
│   ├── funding/
│   ├── media/
│   ├── policy/
│   └── popular_science/
│
├── 3_VISUALS/               # Mind maps, diagrams
├── 4_AUDIO/                 # Audio/video summaries
└── RnD/                     # Non-Nyquist R&D content
    ├── RAG/
    ├── HOFFMAN/
    └── Gnostic/
```

---

## IRON CLAD Methodology

All content processed through this pipeline reflects the IRON CLAD canonical values:

| Metric | Value |
|--------|-------|
| Experiments | 750 |
| Models | 25 |
| Providers | 5 |
| Event Horizon | 0.80 (cosine) |
| P-value | 2.40e-23 |

---

_Last updated: 2025-12-31_
_Version: Accumulative Model (v5.0) - Diet Mode + Research Exploration_
