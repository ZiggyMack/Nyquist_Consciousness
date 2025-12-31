<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-30
depends_on:
  - ./LLMBOOK_SYNC_MANIFEST.json
  - ./packages/CURRENT_VERSION.json
impacts:
  - ../README.md
keywords:
  - consciousness
  - 93_percent_inherent
  - cosine_era
-->
# Reviewers Directory

**Last Updated:** 2025-12-30

> **Statistics Source:** [../guides/UNIFIED_STATISTICS_REFERENCE.md](../guides/UNIFIED_STATISTICS_REFERENCE.md)
> - Event Horizon: D = 0.80 (Cosine)
> - Inherent Drift: ~93% (Run 020B IRON CLAD)
> - Scale: 750 experiments, 25 models, 5 providers

This directory contains draft papers, reviews, and review packages organized by phase.

## Directory Structure

```text
reviewers/
├── README.md                    # This file
├── LLMBOOK_SYNC_MANIFEST.json   # LLM_BOOK sync tracking
│
├── packages/                    # VERSIONED REVIEW PACKAGES
│   ├── CURRENT_VERSION.json     # Version tracking + methodology
│   ├── pdf/                     # Generated PDFs (all paths)
│   ├── v4/                      # CURRENT - Run 020B + 023d IRON CLAD
│   │   ├── .shared/             # ★ MINIMUM VIABLE PACKAGE (send first!)
│   │   │   ├── START_HERE.md    # Reviewer entry point
│   │   │   ├── REVIEWER_BRIEF.md # Full orientation
│   │   │   ├── PACKAGE_INDEX.json # Content mapping
│   │   │   ├── theory/          # Core theory docs
│   │   │   ├── guides/          # Reference materials
│   │   │   ├── planning/        # Strategy docs
│   │   │   └── figures/         # All visuals
│   │   ├── {8 publication paths}/ # Extracted packages
│   │   ├── figures/             # Visualization PNGs
│   │   ├── llmbook/             # NotebookLM synced content
│   │   ├── visualization_pdfs/  # 16 PDF run summaries
│   │   └── feedback/            # Reviewer feedback
│   │       ├── Claude/          # Claude feedback files
│   │       └── Grok/            # Grok feedback files
│   ├── v3/                      # HISTORICAL - Run 023 + drafting history
│   ├── v2/                      # NotebookLM integration era
│   └── v1/                      # Initial package
```

## Review Packages (NEW)

**Problem:** WHITE-PAPER is ~41MB total (figures + PDF dominate). Too large for AI reviewers.

**Solution:** Extract path-specific review packages with manageable sizes (~50-500 KB).

### Generate Packages

```bash
cd WHITE-PAPER/calibration

# Show available paths and sizes
py 3_package_review.py --status

# Extract single path (auto-syncs .shared/ first)
py 3_package_review.py workshop

# Extract multiple paths (auto-syncs .shared/ first)
py 3_package_review.py workshop arxiv

# Extract ALL paths (auto-syncs .shared/ first) ← RECOMMENDED
py 3_package_review.py --all

# Sync ONLY .shared/ (no path packages)
py 3_package_review.py --sync-shared

# Skip auto-sync if needed
py 3_package_review.py --all --no-sync-shared
```

**Template Source:** `planning/reviewer_templates/` → `.shared/`

- Templates auto-sync when extracting any path
- PACKAGE_INDEX.json version increments on each sync

### Available Paths

| Path | Target Venue | Est. Size |
|------|--------------|-----------|
| workshop | NeurIPS/AAAI Workshop | ~90 KB |
| arxiv | cs.AI Preprint | ~360 KB |
| journal | Nature MI | ~530 KB |
| popular_science | Atlantic/Wired | ~30 KB |
| education | OER/Coursera | ~40 KB |
| policy | Think tanks | ~30 KB |
| funding | NSF/DARPA | ~70 KB |
| media | Press/TED | ~35 KB |

### Package Contents

Each extracted package includes:

- `PACKAGE_MANIFEST.md` — What's included + reading order
- `submissions/{path}/` — Core submission materials
- `blueprints/` — Blueprint for this publication path
- `theory/` — Theory docs (varies by path)
- `guides/` — Supporting guides
- `reviewers/` — Previous reviews (if relevant)

---

## Phase History

### Phase 1: Initial Drafts
- **When:** December 2025
- **By:** Code Claude + Opus 4.5
- **What:** First complete drafts of all 3 publication paths
- **Status:** COMPLETE (99/100 validation score)

### Phase 2: Post-Figure Review
- **When:** December 2025
- **By:** Opus 4.5
- **What:** Review after figures generated + circulation package
- **Status:** COMPLETE

### Phase 3: Final Papers (COMPLETE)
- **When:** December 2025
- **By:** Opus 4.5
- **What:** Final PDF generation with Run 023 IRON CLAD data
- **Status:** COMPLETE - Run 023 IRON CLAD (750 experiments, 25 models, 5 providers)

## Current State of Evidence

### Run 023 IRON CLAD Complete

| Run | Experiments | Models | Providers | Status |
|-----|-------------|--------|-----------|--------|
| **Run 023d** | 750 | 25 | 5 | **IRON CLAD ✓** |
| **Run 020B** | 248 sessions | 37 ships | 5 | **IRON CLAD ✓** (Inherent Drift) |
| Run 018 | 1,549 trajectories | 51 | 5 | 52.6% IRON CLAD |
| Run 001-017 | Historical | - | - | Archived |

### Key Metrics (Cosine Methodology)

| Metric | Value | Source |
|--------|-------|--------|
| Event Horizon | D = 0.80 | Run 023b calibration |
| Cohen's d | 0.698 | Run 023d Phase 3B |
| Inherent Drift | **~93%** | Run 020B IRON CLAD (0.661/0.711) |
| p-value | 2.40e-23 | Run 023d validation |
| 90% Variance | 2 PCs | Run 023d PCA |

## What Opus 4.5 Needs to Do

### Current Task (Post-Run 023 IRON CLAD)

1. **Review** Run 023 IRON CLAD results (750 experiments, 25 models, 5 providers)
2. **Verify** all claims use correct COSINE methodology values
3. **Generate** submission-ready PDFs with validated data
4. **Prepare** Workshop and arXiv submissions

### Papers Ready for PDF Generation

| Paper | Status | Notes |
|-------|--------|-------|
| **Workshop** | READY | Run 023 IRON CLAD data complete |
| **arXiv** | READY | Run 023 IRON CLAD data complete |
| **Journal** | DRAFT ONLY | Awaits human validation Q2-Q3 2026 |

## LLM_BOOK Sync Pipeline

LLM_BOOK content (NotebookLM-generated publications) syncs to `packages/v4/llmbook/` for reviewer access.

**When LLM_BOOK is updated, run sync to propagate changes:**

```bash
cd WHITE-PAPER/calibration
py 1_sync_llmbook.py --sync           # Sync to packages/v4/llmbook/
py 1_sync_llmbook.py --sync --dry-run # Preview changes
```

**Manifest:** `LLMBOOK_SYNC_MANIFEST.json` (this directory)
**Destination:** `packages/v4/llmbook/{category}/` (NOT submissions/)

---

## For General Reviewers

If you're reviewing the research (not generating papers):

1. Start with `packages/v4/.shared/START_HERE.md` — Reviewer entry point
2. Read `packages/v4/.shared/REVIEWER_BRIEF.md` — Full orientation with key numbers
3. Review `../guides/VISUAL_QUICK_START.md` — Top 3 visualizations explained
4. See `../START_HERE.md` (parent directory) for full reading order

**Historical phases** (v3/ and earlier) are archived but available for reference.

---

*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23, ~93% inherent drift*
