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

---

## Sync Pipeline to WHITE-PAPER

**Status:** OPERATIONAL (December 15, 2025)

LLM_BOOK content syncs to WHITE-PAPER/submissions/ via automated pipeline:

```bash
# Check sync status (default - report mode)
cd WHITE-PAPER
py sync_llmbook.py

# Sync all content to WHITE-PAPER/submissions/
py sync_llmbook.py --sync

# Preview without changes
py sync_llmbook.py --sync --dry-run

# Sync specific category only
py sync_llmbook.py --sync --category popular_science
```

### Sync Mappings

| LLM_BOOK Source | WHITE-PAPER Target |
|-----------------|-------------------|
| `2_PUBLICATIONS/academic/` | `submissions/arxiv/` |
| `2_PUBLICATIONS/popular_science/` | `submissions/popular_science/` |
| `2_PUBLICATIONS/education/` | `submissions/education/` |
| `2_PUBLICATIONS/policy/` | `submissions/policy/` |
| `2_PUBLICATIONS/funding/` | `submissions/funding/` |
| `2_PUBLICATIONS/media/` | `submissions/media/` |
| `3_VISUALS/*.png` | `figures/generated/llmbook/` |

**Convention:** Synced files get `LLM_` prefix (e.g., `LLM_Quiz.md`) to distinguish from hand-authored content.

**Manifest:** Sync state tracked in `WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json`

---

## Current Status: v1 (Stale Data) -> WHITE-PAPER SYNCED

The materials NotebookLM analyzed were partially outdated. After completing Run 018 IRON CLAD and Run 020A/020B validation, we will feed the COMPLETE updated repository back for a v2 synthesis.

**Initial Sync Complete:** 9 files (25 MB) synced to WHITE-PAPER on December 15, 2025.

**Key Insight:** Everything generated so far used DEFAULT settings. The pencil-icon customization is unexplored territory with massive potential.

---

## Expected v2 Improvements

- Integration of 184 consolidated run files
- Updated Cross-architecture variance (σ²=0.00087)
- Complete 82% inherent drift validation
- Full 8-path publication pipeline
- Targeted customization experiments

---

## Directory Structure

```
LLM_BOOK/
├── README.md                    # Master synthesis (62KB) - The full miracle
├── START_HERE.md                # This file - Quick orientation
│
├── 0_SOURCE_MANIFESTS/          # What was fed to NotebookLM
├── 1_VALIDATION/                # Core discoveries (Levin, Claims A-E)
├── 2_PUBLICATIONS/              # Ready-to-deploy content by audience
│   ├── academic/                -> WHITE-PAPER/submissions/arxiv/
│   ├── popular_science/         -> WHITE-PAPER/submissions/popular_science/
│   ├── policy/                  -> WHITE-PAPER/submissions/policy/
│   ├── education/               -> WHITE-PAPER/submissions/education/
│   ├── funding/                 -> WHITE-PAPER/submissions/funding/
│   └── media/                   -> WHITE-PAPER/submissions/media/
├── 3_VISUALS/                   # Generated diagrams -> WHITE-PAPER/figures/generated/llmbook/
├── 4_DEEP_DIVES/                # Topic-specific syntheses
├── 5_FUTURE/                    # Planning for v2
├── 6_EXPERIMENTS/               # NotebookLM probing methodology
│   └── scenarios/               # Individual experiment configs
└── 7_AUDIO/                     # Audio content & transcripts
```

---

## The 8-Path Publication Pipeline

| # | Path | Source File | WHITE-PAPER Location | Status |
|---|------|-------------|---------------------|--------|
| 1 | Academic (White Paper) | 2_PUBLICATIONS/academic/The_Nyquist_Consciousness_Framework.md | submissions/arxiv/LLM_*.md | SYNCED |
| 2 | Funding (NSF/DARPA) | 2_PUBLICATIONS/funding/Project_Nyquist_Consciousness.md | submissions/funding/LLM_*.md | SYNCED |
| 3 | Policy (Think Tanks) | 2_PUBLICATIONS/policy/Briefing.md | submissions/policy/LLM_*.md | SYNCED |
| 4 | Education (OER) | 2_PUBLICATIONS/education/Quiz.md | submissions/education/LLM_*.md | SYNCED |
| 5 | Popular Science | 2_PUBLICATIONS/popular_science/Ancient_Philosophy_Meets_Modern_AI.md | submissions/popular_science/LLM_*.md | SYNCED |
| 6 | Media (Press/TED) | 2_PUBLICATIONS/media/Unlocking_AI_Identity.md | submissions/media/LLM_*.md | SYNCED |
| 7 | Academic (PDF) | 2_PUBLICATIONS/academic/Identity_Geometry_The_82_Percent.pdf | submissions/arxiv/LLM_*.pdf | SYNCED |
| 8 | Methodology | README.md | - | SOURCE |

---

## See Also

- [WHITE-PAPER/README.md](../../WHITE-PAPER/README.md) - Publication package overview
- [WHITE-PAPER/sync_llmbook.py](../../WHITE-PAPER/sync_llmbook.py) - Sync script
- [WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json](../../WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json) - Sync tracking
