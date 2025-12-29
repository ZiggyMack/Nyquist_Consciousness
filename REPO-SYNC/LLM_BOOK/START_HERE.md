<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-29
keywords:
  - consciousness
  - IRON CLAD
  - COSINE ERA
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
| Use a publication draft | [2_PUBLICATIONS/](2_PUBLICATIONS/) |
| See the visuals | [3_VISUALS/](3_VISUALS/) |
| Deep dive on a topic | [4_DEEP_DIVES/](4_DEEP_DIVES/) |
| Plan for v2 refresh | [5_FUTURE/](5_FUTURE/) |
| Design NotebookLM experiments | [6_EXPERIMENTS/](6_EXPERIMENTS/) |
| Access audio content | [7_AUDIO/](7_AUDIO/) |
| Explore R&D content | [RnD/](RnD/) |

---

## Content Workflows

### Ingestion (STAGING -> LLM_BOOK)

New NotebookLM outputs are staged in `0_SOURCE_MANIFESTS/STAGING/` and ingested via:

```bash
cd REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS
py ingest.py                    # Report mode - show what would happen
py ingest.py --ingest           # Actually perform ingestion
py ingest.py --ingest --dry-run # Preview without changes
```

**Workflow:** Archives current state to `packages/v{n}/llmbook/` before clearing and rebuilding.

### Sync to WHITE-PAPER (LLM_BOOK -> packages/)

LLM_BOOK content syncs to WHITE-PAPER/reviewers/packages/ via automated pipeline:

```bash
# Check sync status (default - report mode)
cd WHITE-PAPER/calibration
py 1_sync_llmbook.py

# Sync all content to packages/{version}/llmbook/
py 1_sync_llmbook.py --sync

# Preview without changes
py 1_sync_llmbook.py --sync --dry-run

# Sync specific category only
py 1_sync_llmbook.py --sync --category popular_science
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
| `3_VISUALS/*.png` | `figures/generated/llmbook/` |

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
├── 0_SOURCE_MANIFESTS/          # What was fed to NotebookLM + STAGING ingestion
│   ├── STAGING/                 # NotebookLM outputs awaiting ingestion
│   └── ingest.py                # Ingestion script (STAGING -> LLM_BOOK)
├── 1_VALIDATION/                # Core discoveries (Levin, Claims A-E)
├── 2_PUBLICATIONS/              # Ready-to-deploy content by audience
│   ├── academic/                -> packages/{version}/llmbook/academic/
│   ├── popular_science/         -> packages/{version}/llmbook/popular_science/
│   ├── policy/                  -> packages/{version}/llmbook/policy/
│   ├── education/               -> packages/{version}/llmbook/education/
│   ├── funding/                 -> packages/{version}/llmbook/funding/
│   └── media/                   -> packages/{version}/llmbook/media/
├── 3_VISUALS/                   # Generated diagrams -> WHITE-PAPER/figures/generated/llmbook/
├── 4_DEEP_DIVES/                # Topic-specific syntheses
├── 5_FUTURE/                    # Planning for v2
├── 6_EXPERIMENTS/               # NotebookLM probing methodology
│   └── scenarios/               # Individual experiment configs
├── 7_AUDIO/                     # Audio content & transcripts
└── RnD/                         # Non-Nyquist R&D content (Hoffman, Gnostic, RAG, etc.)
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

- [WHITE-PAPER/README.md](../../WHITE-PAPER/README.md) - Publication package overview
- [WHITE-PAPER/calibration/1_sync_llmbook.py](../../WHITE-PAPER/calibration/1_sync_llmbook.py) - Sync script
- [WHITE-PAPER/reviewers/packages/CURRENT_VERSION.json](../../WHITE-PAPER/reviewers/packages/CURRENT_VERSION.json) - Version tracking
- [WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json](../../WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json) - Sync tracking
- [RnD/README.md](RnD/README.md) - R&D content documentation
