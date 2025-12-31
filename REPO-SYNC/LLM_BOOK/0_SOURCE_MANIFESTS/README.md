# LLM_BOOK Digestive Pipeline

<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-31
depends_on:
  - 0_chew.py
  - 1_ingest.py
  - 2_digest.py
  - ../../../WHITE-PAPER/calibration/1_sync_llmbook.py
impacts:
  - ../1_VALIDATION/
  - ../2_PUBLICATIONS/
  - ../RnD/
  - ../../../WHITE-PAPER/reviewers/packages/v4/llmbook/
keywords:
  - NotebookLM
  - ingestion
  - digest
  - chew
  - STAGING
  - pipeline
  - REVIEW_NOTES
-->

**Purpose:** Process NotebookLM outputs into the Nyquist Consciousness publication pipeline.

**Location:** `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/`

**IRON CLAD Era:** 750 experiments | 25 models | 5 providers | EH=0.80 | p=2.40e-23

---

## Quick Start

Everything starts with `0_chew.py`:

```bash
# Check pipeline status
py 0_chew.py

# Process a batch (auto-detects Nyquist vs R&D)
py 0_chew.py Nyquist_3

# Diet mode: process to _CACHE_/ only (for review before committing)
py 0_chew.py HOFFMAN --diet

# Create new research project
py 0_chew.py --baka "EEG Analog Study"

# See routing for a topic
py 0_chew.py --route HOFFMAN
```

---

## Pipeline Architecture

```
0_chew.py (unified entry point)
     │
     ├── BATCH              → 1_ingest.py → 2_digest.py
     ├── BATCH --new        → 1_ingest.py --fresh → 2_digest.py
     ├── BATCH --diet       → 1_ingest.py --diet (→ _CACHE_/)
     ├── --baka "Name"      → Create New_X/ research project
     ├── --promote BATCH    → Copy to Consciousness/
     ├── --reset            → Purge all _CACHE_/ directories
     ├── --route TOPIC      → Show Pan Handler routing
     └── --labs             → List Pan Handler labs
```

**Flow:**

```
STAGING/                           LLM_BOOK/
  Nyquist_1/_IN/  ─┐              ├── 1_VALIDATION/
  Nyquist_2/_IN/  ─┼─ 1_ingest ───┤     ├── REVIEW_NOTES_*.md
  HOFFMAN/        ─┤              │     ├── 1_DEEP_DIVES/
  RAG/            ─┘              │     ├── 2_FUTURE/
                                  │     └── 3_EXPERIMENTS/
                  2_digest ───────┤
                                  ├── 2_PUBLICATIONS/{category}/
                                  ├── 3_VISUALS/
                                  ├── 4_AUDIO/
                                  └── RnD/
                                        ├── {topic}/
                                        │   ├── REVIEW_NOTES_{batch}.md
                                        │   ├── INSIGHTS/
                                        │   ├── CONNECTIONS/
                                        │   └── EXPERIMENTS/
```

---

## Scripts

### 0_chew.py (v3.0) - Unified Entry Point

The single command for all pipeline operations. Everything starts with "chewing."

**Pipeline Operations:**

| Command | Description |
|---------|-------------|
| `py 0_chew.py BATCH` | Ingest + digest (append mode, auto-detects type) |
| `py 0_chew.py BATCH --new` | Fresh mode: clear + ingest + digest |
| `py 0_chew.py BATCH --diet` | Diet mode: process to `_CACHE_/` only |

**Project Management:**

| Command | Description |
|---------|-------------|
| `py 0_chew.py --baka "Name"` | Create new research project (R&D exploratory) |
| `py 0_chew.py --promote BATCH` | Promote to Consciousness/ |
| `py 0_chew.py --reset` | Purge all `_CACHE_/` directories |
| `py 0_chew.py --status` | Show full pipeline status |

**Routing Intelligence:**

| Command | Description |
|---------|-------------|
| `py 0_chew.py --route TOPIC` | Show where topic should go |
| `py 0_chew.py --route --all` | Show full routing map |
| `py 0_chew.py --labs` | List all Pan Handler labs |
| `py 0_chew.py --lab ID` | Show specific lab details |

**Content Type Auto-Detection:**

- Names containing `nyquist`, `infinity-nyquist`, or `white-paper` → IRON CLAD validation
- Everything else → R&D exploratory processing

### 1_ingest.py (v6.0) - STAGING to Cognitive Processing

Called by `0_chew.py`. Creates review notes and analysis stubs.

**Nyquist Content:**

- IRON CLAD validation (D=0.80, ~93%, p=2.40e-23, 750/25/5)
- `REVIEW_NOTES_{batch}.md` with quality grades
- `1_DEEP_DIVES/`, `2_FUTURE/`, `3_EXPERIMENTS/`

**R&D Content:**

- Open-ended exploratory processing (no IRON CLAD constraints)
- `REVIEW_NOTES_{batch}.md` with insights focus
- `INSIGHTS/`, `CONNECTIONS/`, `EXPERIMENTS/`

### 2_digest.py (v2.0) - File Routing

Called by `0_chew.py`. Routes files to final destinations.

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

---

## Diet Mode

Process content without committing to the pipeline:

```bash
py 0_chew.py HOFFMAN --diet
```

Output goes to `_CACHE_/` inside the batch folder:

```text
STAGING/HOFFMAN/
    _IN/                          # Source files (untouched)
    _CACHE_/                      # Diet mode output
        RnD/HOFFMAN/
            REVIEW_NOTES_HOFFMAN.md
            INSIGHTS/
                HOFFMAN.md
            CONNECTIONS/
                HOFFMAN.md
            EXPERIMENTS/
                HOFFMAN.md
```

To purge all caches:

```bash
py 0_chew.py --reset
```

---

## Research Projects (--baka)

Create exploratory research projects:

```bash
py 0_chew.py --baka "EEG Analog Study"
```

Creates:

```text
STAGING/New_4_EEG_Analog_Study/
    _IN/                    # NotebookLM responses
    _OUT/                   # Materials FOR NotebookLM
        RESEARCH_QUESTION.md
        EXISTING_EVIDENCE.md
        CONSTRAINTS.md
    README.md               # Project overview
```

All `--baka` projects use R&D exploratory structure (not IRON CLAD constrained).

---

## Pan Handler Routing

Route insights to appropriate labs:

```bash
py 0_chew.py --route HOFFMAN
# Output: Primary: New_3_Human_Validation, cfa | Secondary: avlar-studio

py 0_chew.py --labs
# Lists all 9 Pan Handler labs

py 0_chew.py --lab cfa
# Shows CFA details + what R&D topics feed it
```

Configuration files:

- `PAN_HANDLERS/1_Maps/research_to_labs.json` - Explicit topic mappings
- `PAN_HANDLERS/1_Maps/llm_book_routing.json` - Pattern-based rules

---

## Directory Reference

```
REPO-SYNC/LLM_BOOK/
├── 0_SOURCE_MANIFESTS/      # This folder
│   ├── README.md            # This file
│   ├── STAGING/             # Raw NotebookLM outputs
│   ├── 0_chew.py            # Unified entry point
│   ├── 1_ingest.py          # Cognitive processing
│   └── 2_digest.py          # File routing
│
├── 1_VALIDATION/            # Nyquist review notes
│   ├── REVIEW_NOTES_*.md
│   ├── 1_DEEP_DIVES/
│   ├── 2_FUTURE/
│   └── 3_EXPERIMENTS/
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
└── RnD/                     # R&D exploratory content
    ├── HOFFMAN/
    │   ├── REVIEW_NOTES_HOFFMAN.md
    │   ├── INSIGHTS/
    │   ├── CONNECTIONS/
    │   └── EXPERIMENTS/
    ├── RAG/
    └── Gnostic/
```

---

## IRON CLAD Methodology

Nyquist content validates against canonical values:

| Metric | Value |
|--------|-------|
| Experiments | 750 |
| Models | 25 |
| Providers | 5 |
| Event Horizon | 0.80 (cosine) |
| P-value | 2.40e-23 |

---

_Last updated: 2025-12-31_
_Version: Unified Pipeline (v3.0) - 0_chew.py Entry Point_
