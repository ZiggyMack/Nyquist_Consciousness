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

## Content Formatting (CRITICAL for Cold Boot)

The pipeline README (this file) covers **where files go**. For **how files should look**, you need the formatting specs in a separate location:

**Specs live at:** `Consciousness/RIGHT/distillations/llm_book/meta/`

| Spec | What It Tells You |
|------|-------------------|
| `WORKFLOW_SPEC.md` (Section 12) | `_ROUND_1/` folder structure, file list, round-based iteration |
| `HOLY_GRAIL.md` | Output specification template for `report.md` (Reports + Infographics + Slides + Audio + Video) |
| `PROMPT_ENGINEERING.md` | Ethos, lessons learned, prompt patterns |

### Reference Implementations (copy these formats)

| File | Template To Follow |
|------|-------------------|
| `report.md` | `STAGING/New_2_S_Parameters/report.md` — Full HOLY_GRAIL output spec with all 5 output types |
| `chat.md` | `STAGING/New_2_S_Parameters/chat.md` — Q1/Q2 numbering, blockquoted questions, `[Paste NotebookLM response here]` placeholders |

### _ROUND_1/ Expected File Structure

```
Project/_ROUND_1/
├── chat.md            # NotebookLM questions to ask (Q1, Q2... format)
├── report.md          # NotebookLM output specifications (HOLY_GRAIL template)
├── REVIEW_NOTES_*.md  # Key findings from initial digestion
├── INSIGHTS/          # Extracted insights
├── CONNECTIONS/       # Cross-project links
├── EXPERIMENTS/       # Experiments to run
├── QUESTIONS_OUT.md   # Questions asked TO other projects
└── routing.md         # Cross-pollination routing
```

### Quick Formatting Rules

- **report.md**: Header (Source/Date/Methodology) → Output Count Summary table → Reports (Focus/Should Cover/Target Audience) → Infographics (Settings + Description) → Slide Decks → Audio Guides → Videos → Footer
- **chat.md**: Header (Project/Created/Status) → `### QN: Title` → blockquoted question → `**Response:**` → `[Paste NotebookLM response here]` → `---` separator

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

## STAGING Deep Dive Index

All research projects in `STAGING/` — the source material for the chew pipeline.

| # | Directory | Subject | Status | Key Products |
|---|-----------|---------|--------|-------------|
| 1 | `New_1_EEG_Analog` | Spectral patterns in LLM identity drift | Complete | report.md, chat.md |
| 2 | `New_2_S_Parameters` | Signal/impedance framework | Complete | report.md (HOLY_GRAIL reference implementation), chat.md |
| 3 | `New_3_Human_Validation` | Human validation methodology | Complete | report.md, chat.md |
| 4 | *(archived)* | Golden Geometry — geometric bounds | Archived | Lives in `CHEWED/BURP/New_4_GOLDEN_GEOMETRY/pre-lim/` |
| 5 | `New_5_RAG_Geometry_Experiments` | Geometry of RAG systems | Complete | report.md |
| 6 | `New_6_GNOSTIC_AI` | Gnostic framework applied to AI | Complete | report.md |
| 7 | `New_7_KAYFABE` | Cultural model — 7-node mythic graph | Complete | report.md (HOLY_GRAIL specs), `_CACHE_/INSIGHTS/` |
| 8 | `New_8_Cognative_Physics` | Adlam/Barandes consciousness-physics dialogue | Complete (2 rounds) | 40 insights, 9+ experiments, ISP-CA mapping, 6 operators |
| 9 | `New_9_Cognitive_Archaeology` | Dig site excavation project | **Active** | 8 dig sites, 15 operators, LEDGER, MUSEUM, TOOLS |
| 10 | `New_10_TOE` | Curt Jaimungal "Reverse Elephant" | Complete (R1 + Audit) | Architecture F, Discovery Simplex, Relation Space |
| — | `Infinity-Nyquist` | Levin/Platonic hypothesis validation | Complete | Synthesis document |

> **Q50 Transition:** From Dig Site 003 (Dirac) onward, new thinker digs live as self-contained projects under `New_9_Cognitive_Archaeology/DIG_SITES/NNN_Thinker/` rather than as `New_N` projects in STAGING. The Q50 recursive queue drives selection.

---

## Structure Patterns

### Basic Pattern (New_1 through New_7)

```
Project/
├── _IN/          ← Input artifacts/sources
├── _OUT/         ← Materials FOR NotebookLM
├── chat.md       ← Q&A results
├── report.md     ← Synthesis/recommendations (HOLY_GRAIL format)
└── README.md     ← Project overview
```

### Advanced Pattern (New_8, New_10)

```
Project/
├── _IN/          ← Input artifacts/sources
├── _OUT/         ← Materials FOR NotebookLM
├── _ROUND_1/     ← Versioned mining rounds
│   ├── chat.md           ← Questions (Q1-QN numbered)
│   ├── report.md         ← HOLY_GRAIL output specifications
│   ├── routing.md        ← Cross-project connection matrix
│   ├── QUESTIONS_OUT.md  ← Follow-up questions for other projects
│   ├── REVIEW_NOTES_*.md ← Quality assessment
│   ├── CONNECTIONS/      ← Cross-dig-site links
│   ├── EXPERIMENTS/      ← Staged experiment designs
│   └── INSIGHTS/         ← Extracted findings
├── _ROUND_2/     ← Second round (if warranted)
└── README.md
```

> **Note:** New_9 (Cognitive Archaeology) is a self-contained project with its own architecture — see `New_9_Cognitive_Archaeology/README.md`.

---

## Chew Operation Checklist

What every deep dig should produce before it's considered "done." Use this to verify nothing was forgotten.

### Core outputs (every dig):

1. **`chat.md`** — All Q&A documented (Q1-QN format)
2. **`report.md`** — HOLY_GRAIL output specifications
3. **`INSIGHTS/`** — Extracted findings (the "what did we learn")
4. **`CONNECTIONS/`** — Cross-project links (what connects to what)
5. **`EXPERIMENTS/`** — Staged experiment designs (what to test next)
6. **`routing.md`** — Cross-pollination routing matrix
7. **`REVIEW_NOTES_*.md`** — Quality assessment
8. **Cross-pollination EXECUTED** — not just documented, actually update target projects
9. **Operator extraction attempted** — feed to New_9 pipeline if reasoning content exists

### For advanced digs (Round 2+):

10. **`QUESTIONS_OUT.md`** — Questions generated FOR other projects
11. **Second-round mining** — if Round 1 revealed enough depth to warrant it

### Integration Queue:

12. **Actionable items queued** — any new CFA questions, experiments, extraction prompts, or protocol changes discovered during the dig should be added to `New_9_Cognitive_Archaeology/INTEGRATION_QUEUE.json`

---

_Last updated: 2026-07-14_
_Version: Unified Pipeline (v3.0) - 0_chew.py Entry Point_
