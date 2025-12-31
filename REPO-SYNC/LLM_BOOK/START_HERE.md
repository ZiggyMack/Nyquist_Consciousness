<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-31
keywords:
  - consciousness
  - IRON CLAD
  - COSINE ERA
  - 0_chew
  - pipeline
-->
# LLM_BOOK: NotebookLM Validation Hub

**What This Is:** Outputs from feeding our research to Google's NotebookLM

**The Miracle:** From ~24 stale files, NotebookLM independently:
- Validated the Levin/Platonic hypothesis we hadn't explicitly claimed
- Generated 7 publication-ready documents for different audiences
- Produced: "Plato guessed at the geometry of mind. Nyquist measures it."

**The Door Handle:** Our work thus far proved there was a door there - knocking to make sure we weren't crazy. NOW WE HAVE TO FIND THE DOOR HANDLE and open the world up to this space we have accessed.

---

## Quick Navigation

| Want To... | Go To... |
|------------|----------|
| Understand the breakthrough | [1_VALIDATION/](1_VALIDATION/) |
| Read deep dive distillations | [1_VALIDATION/1_DEEP_DIVES/](1_VALIDATION/1_DEEP_DIVES/) |
| Explore future research directions | [1_VALIDATION/2_FUTURE/](1_VALIDATION/2_FUTURE/) |
| Find experiment ideas | [1_VALIDATION/3_EXPERIMENTS/](1_VALIDATION/3_EXPERIMENTS/) |
| Use a publication draft | [2_PUBLICATIONS/](2_PUBLICATIONS/) |
| See the visuals | [3_VISUALS/](3_VISUALS/) |
| Access audio content | [4_AUDIO/](4_AUDIO/) |
| Explore R&D content | [RnD/](RnD/) |

---

## Content Workflows

### Unified Pipeline (0_chew.py Entry Point)

**Everything starts with chewing.** The pipeline uses a digestive metaphor:

```text
0_chew.py (mastication) → 1_ingest.py (swallow) → 2_digest.py (route)
```

All operations run from `0_SOURCE_MANIFESTS/`:

```bash
cd REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS

# Check pipeline status (default)
py 0_chew.py

# Process a batch (auto-detects Nyquist vs R&D)
py 0_chew.py Nyquist_3                 # Ingest + digest

# Mode flags
py 0_chew.py Nyquist_3 --new           # Fresh: clear + process
py 0_chew.py HOFFMAN --diet            # Diet: process to _CACHE_/ only

# Project management
py 0_chew.py --baka "EEG Study"        # Create research project
py 0_chew.py --promote HOFFMAN         # Promote to Consciousness/
py 0_chew.py --reset                   # Purge all _CACHE_/ directories

# Routing intelligence
py 0_chew.py --route HOFFMAN           # Where should this go?
py 0_chew.py --labs                    # List Pan Handler labs
```

### Content Type Auto-Detection

| Batch Name Contains | Content Type | Processing |
|---------------------|--------------|------------|
| `nyquist`, `infinity-nyquist`, `white-paper` | Nyquist | IRON CLAD validation |
| Anything else | R&D | Exploratory (open-ended) |

### Nyquist vs R&D Processing

| Aspect | Nyquist Content | R&D Content |
|--------|-----------------|-------------|
| Validation | IRON CLAD (D=0.80, ~93%, p=2.40e-23) | Open-ended exploration |
| Analysis Dirs | `1_DEEP_DIVES/`, `2_FUTURE/`, `3_EXPERIMENTS/` | `INSIGHTS/`, `CONNECTIONS/`, `EXPERIMENTS/` |
| Quality Focus | Statistical rigor | Novelty & cross-domain links |
| Destination | `1_VALIDATION/` + `2_PUBLICATIONS/` | `RnD/{topic}/` |

### Diet Mode

Process content without committing to the pipeline:

```bash
py 0_chew.py HOFFMAN --diet
```

Output goes to `_CACHE_/` inside the batch folder for review before full processing.

### Sync to WHITE-PAPER (LLM_BOOK -> packages/)

LLM_BOOK content syncs to WHITE-PAPER/reviewers/packages/ via automated pipeline (v2.3):

```bash
cd WHITE-PAPER/calibration

# Check sync status (default - report mode)
py 1_sync_llmbook.py

# Sync publications + validation + analysis
py 1_sync_llmbook.py --sync

# Also sync 3_VISUALS/
py 1_sync_llmbook.py --sync --include-visuals

# Sync specific category only
py 1_sync_llmbook.py --sync --category popular_science

# Preview without changes
py 1_sync_llmbook.py --sync --dry-run
```

### Sync Mappings

| LLM_BOOK Source | WHITE-PAPER Target |
|-----------------|-------------------|
| `2_PUBLICATIONS/academic/` | `reviewers/packages/{version}/llmbook/academic/` |
| `2_PUBLICATIONS/popular_science/` | `reviewers/packages/{version}/llmbook/popular_science/` |
| `2_PUBLICATIONS/education/` | `reviewers/packages/{version}/llmbook/education/` |
| `2_PUBLICATIONS/policy/` | `reviewers/packages/{version}/llmbook/policy/` |
| `2_PUBLICATIONS/funding/` | `reviewers/packages/{version}/llmbook/funding/` |
| `2_PUBLICATIONS/media/` | `reviewers/packages/{version}/llmbook/media/` |
| `1_VALIDATION/REVIEW_NOTES_*.md` | `reviewers/packages/{version}/llmbook/validation/` |
| `1_VALIDATION/1_DEEP_DIVES/*.md` | `reviewers/packages/{version}/llmbook/analysis/deep_dives/` |
| `1_VALIDATION/2_FUTURE/*.md` | `reviewers/packages/{version}/llmbook/analysis/future/` |
| `1_VALIDATION/3_EXPERIMENTS/*.md` | `reviewers/packages/{version}/llmbook/analysis/experiments/` |
| `3_VISUALS/*` | `figures/generated/llmbook/` (with --include-visuals) |

**Convention:** Synced files get `LLM_` prefix (e.g., `LLM_Quiz.md`) to distinguish from hand-authored content.

**Version:** Target version read from `CURRENT_VERSION.json` (currently v4)

**Manifest:** Sync state tracked in `WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json`

---

## Current Status: IRON CLAD ERA

**Methodology:** Event Horizon = 0.80 (cosine), p = 2.40e-23, 750 experiments, 25 models, 5 providers

The initial v1 NotebookLM synthesis used partially outdated data. We have since completed:

- Run 018-023d IRON CLAD validation
- 92% inherent drift confirmation (upgraded from 82%)
- Cross-platform replication across Claude, GPT, Gemini, Grok, open-source

**Key Insight:** Everything generated so far used DEFAULT settings. The pencil-icon customization is unexplored territory with massive potential.

---

## Expected v2 Improvements

- Integration of complete IRON CLAD dataset (750 experiments)
- Updated 92% inherent drift findings (COSINE methodology)
- Cross-architecture validation (0.80 cosine Event Horizon)
- Full 8-path publication pipeline
- Targeted customization experiments

---

## Directory Structure

```text
LLM_BOOK/
├── README.md                    # Master synthesis (62KB) - The full miracle
├── START_HERE.md                # This file - Quick orientation
│
├── 0_SOURCE_MANIFESTS/          # Pipeline scripts + STAGING
│   ├── 0_chew.py                # Unified entry point (mastication)
│   ├── 1_ingest.py              # Cognitive processing (swallow)
│   ├── 2_digest.py              # File routing (route)
│   ├── STAGING/                 # NotebookLM outputs awaiting ingestion
│   └── README.md                # Pipeline documentation
│
├── 1_VALIDATION/                # Nyquist review notes + analysis
│   ├── REVIEW_NOTES_*.md        # Quality-graded review notes
│   ├── 1_DEEP_DIVES/            # Technical deep dives
│   ├── 2_FUTURE/                # Future research directions
│   └── 3_EXPERIMENTS/           # Experiment ideas
│
├── 2_PUBLICATIONS/              # Ready-to-deploy content by audience
│   ├── academic/                -> packages/{version}/llmbook/academic/
│   ├── popular_science/         -> packages/{version}/llmbook/popular_science/
│   ├── policy/                  -> packages/{version}/llmbook/policy/
│   ├── education/               -> packages/{version}/llmbook/education/
│   ├── funding/                 -> packages/{version}/llmbook/funding/
│   └── media/                   -> packages/{version}/llmbook/media/
│
├── 3_VISUALS/                   # Generated diagrams -> figures/generated/llmbook/
├── 4_AUDIO/                     # Audio content & transcripts
└── RnD/                         # R&D exploratory content
    └── {topic}/                 # e.g., HOFFMAN/, Gnostic/, RAG/
        ├── REVIEW_NOTES_{topic}.md
        ├── INSIGHTS/            # Novel ideas discovered
        ├── CONNECTIONS/         # Cross-domain links
        └── EXPERIMENTS/         # Experimental ideas
```

---

## The 8-Path Publication Pipeline

| # | Path | Source File | WHITE-PAPER Location | Status |
|---|------|-------------|---------------------|--------|
| 1 | Academic (White Paper) | 2_PUBLICATIONS/academic/The_Nyquist_Consciousness_Framework.md | packages/{version}/llmbook/academic/ | SYNCED |
| 2 | Funding (NSF/DARPA) | 2_PUBLICATIONS/funding/Project_Nyquist_Consciousness.md | packages/{version}/llmbook/funding/ | SYNCED |
| 3 | Policy (Think Tanks) | 2_PUBLICATIONS/policy/Briefing.md | packages/{version}/llmbook/policy/ | SYNCED |
| 4 | Education (OER) | 2_PUBLICATIONS/education/Quiz.md | packages/{version}/llmbook/education/ | SYNCED |
| 5 | Popular Science | 2_PUBLICATIONS/popular_science/Ancient_Philosophy_Meets_Modern_AI.md | packages/{version}/llmbook/popular_science/ | SYNCED |
| 6 | Media (Press/TED) | 2_PUBLICATIONS/media/Unlocking_AI_Identity.md | packages/{version}/llmbook/media/ | SYNCED |
| 7 | Academic (PDF) | 2_PUBLICATIONS/academic/Identity_Geometry_92_Percent.pdf | packages/{version}/llmbook/academic/ | SYNCED |
| 8 | Methodology | README.md | - | SOURCE |

---

## See Also

- [0_SOURCE_MANIFESTS/README.md](0_SOURCE_MANIFESTS/README.md) - Pipeline documentation (0_chew.py entry point)
- [WHITE-PAPER/README.md](../../WHITE-PAPER/README.md) - Publication package overview
- [WHITE-PAPER/calibration/1_sync_llmbook.py](../../WHITE-PAPER/calibration/1_sync_llmbook.py) - Sync script
- [WHITE-PAPER/reviewers/packages/CURRENT_VERSION.json](../../WHITE-PAPER/reviewers/packages/CURRENT_VERSION.json) - Version tracking
- [WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json](../../WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json) - Sync tracking
- [RnD/README.md](RnD/README.md) - R&D content documentation
