<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-29
depends_on:
  - ./0_sync_viz.py
  - ./1_sync_llmbook.py
  - ./2_package_review.py
  - ./3_generate_pdfs.py
  - ./4_publish_stats.py
impacts:
  - ../README.md
  - ../START_HERE.md
keywords:
  - consciousness
  - calibration
  - iron_clad
  - cosine_methodology
-->
# Calibration Pipeline

**Purpose:** Sync assets, generate PDFs, create review packages, and extract statistics.
**Last Updated:** 2025-12-29
**Methodology:** IRON CLAD COSINE ERA (Event Horizon = 0.80, p = 2.40e-23, 92% Inherent Drift)

---

## Complete Feedback Loop Architecture

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                              OUTBOUND FLOW                                   │
│   0_sync_viz.py → packages/v4/ → Reviewers receive materials                │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                              INBOUND FLOW                                    │
│   Reviewers → packages/v4/feedback/{reviewer}/ → feedback files             │
│                                                                              │
│   Types of feedback:                                                         │
│   1. Visual requests ("I need oobleck_thermometer.png in Fig 3")            │
│   2. Content feedback ("Section 2.1 needs clarification")                   │
│   3. Placement suggestions ("Move settling_curves to appendix")             │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PROCESSING FLOW                                    │
│                                                                              │
│   TWO SOURCES OF UPDATES (experiment-driven takes precedence):              │
│                                                                              │
│   ┌─────────────────────────────┐    ┌─────────────────────────────┐        │
│   │  EXPERIMENT-DRIVEN          │    │  REVIEWER-DRIVEN            │        │
│   │  (Authoritative)            │    │  (Feedback)                 │        │
│   │                             │    │                             │        │
│   │  • New runs (IRON CLAD)     │    │  • Visual requests          │        │
│   │  • Updated thresholds       │    │  • Placement suggestions    │        │
│   │  • Corrected metrics        │    │  • Content clarifications   │        │
│   │  • Supersedes old data      │    │  • Figure improvements      │        │
│   └──────────────┬──────────────┘    └──────────────┬──────────────┘        │
│                  │                                   │                       │
│                  │    ┌─────────────────────┐       │                       │
│                  └───►│  CURRENT_VERSION.json│◄──────┘                       │
│                       │  (visual_requests)  │                               │
│                       └──────────┬──────────┘                               │
│                                  │                                          │
│                                  ▼                                          │
│                       ┌─────────────────────┐                               │
│                       │  visual_index.md    │                               │
│                       │  (per-pipeline map) │                               │
│                       └──────────┬──────────┘                               │
│                                  │                                          │
│                                  ▼                                          │
│                       ┌─────────────────────┐                               │
│                       │  figures/           │                               │
│                       │  (synced PNGs)      │                               │
│                       └─────────────────────┘                               │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                           GENERATION FLOW                                    │
│   3_generate_pdfs.py                                                        │
│     → Reads visual_index.md for per-pipeline figure placement               │
│     → Incorporates visuals at correct locations                             │
│     → Produces final PDFs with experiment + reviewer-informed layout        │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Quick Reference

| # | Script | Purpose | Typical Usage |
|---|--------|---------|---------------|
| 0 | `0_sync_viz.py` | Sync PDFs + PNGs + reviewer feedback | `py 0_sync_viz.py --sync --sync-pngs` |
| 1 | `1_sync_llmbook.py` | Sync LLM_BOOK → reviewer packages | `py 1_sync_llmbook.py --sync` |
| 2 | `2_package_review.py` | Sync .shared/ + extract path packages | `py 2_package_review.py --all` |
| 3 | `3_generate_pdfs.py` | Extract + generate submission PDFs | `py 3_generate_pdfs.py --from-review` |
| 4 | `4_publish_stats.py` | Extract dashboard statistics | `py 4_publish_stats.py` |

**Workflow Order:** 0 → 1 → 2 → 3 → 4

**Note:** Step 2 (`--all`) auto-syncs `.shared/` first, so you only need one command.

---

## 0. Sync Visualizations (`0_sync_viz.py`)

Comprehensive sync tool for PDFs, PNGs, and reviewer feedback loop.

### PDF Sync (Summary PDFs → packages)

```bash
# Quick status check
py 0_sync_viz.py --check

# Auto-sync all outdated PDFs
py 0_sync_viz.py --sync

# Sync specific visualization
py 0_sync_viz.py --sync 15_Oobleck_Effect

# Regenerate PNGs + PDFs, then sync
py 0_sync_viz.py --regenerate --sync
```

### PNG Sync (visual_index.md → figures/publication/)

```bash
# Sync all identified PNGs from visual_index.md
py 0_sync_viz.py --sync-pngs

# Preview what would sync
py 0_sync_viz.py --sync-pngs --dry-run

# Include approved reviewer requests
py 0_sync_viz.py --sync-pngs --include-requests
```

### Reviewer Feedback Loop

Reviewers submit feedback in `packages/v4/feedback/{reviewer}/`. The flow is:

```text
feedback/{reviewer}/visual_requests.json
          ↓
     --process-feedback
          ↓
CURRENT_VERSION.json (visual_requests)
          ↓
     --approve "name.png"
          ↓
     --update-index
          ↓
figures/visual_index.md (per-pipeline placement)
          ↓
3_generate_pdfs.py (incorporate into final PDFs)
```

```bash
# Import feedback from all reviewers
py 0_sync_viz.py --process-feedback

# Show pending visual requests
py 0_sync_viz.py --requests

# Approve a request
py 0_sync_viz.py --approve "new_visual.png"

# Add approved visuals to visual_index.md
py 0_sync_viz.py --update-index
```

**Feedback directory:** `packages/v4/feedback/{Claude,Grok}/`

- `visual_requests.json` - Structured visual requests with pipeline/placement
- `content_feedback.md` - General content feedback

### Version Management

```bash
py 0_sync_viz.py --version-info
py 0_sync_viz.py --bump-check "IRON CLAD 100% complete"
```

Version rules in `CURRENT_VERSION.json`:

- **Stay on current:** Bug fixes, data corrections
- **Create new version:** New runs, methodology changes

**Known Visualizations:** `15_Oobleck_Effect/`, `run018/`, `run020/`

**Auto-Discovery:** Finds any directory with `*_Summary.pdf` files.

---

## 1. Sync LLM_BOOK (`1_sync_llmbook.py`)

Sync NotebookLM synthesis outputs to reviewer packages for feedback.

**NOTE:** This syncs to `reviewers/packages/v4/llmbook/`, NOT `submissions/`.
The `submissions/` directory contains only curated `*_FINAL.md` papers.
NotebookLM outputs go to reviewer packages so AI reviewers can evaluate
how to incorporate them into final publications.

```bash
# Status report (default)
py 1_sync_llmbook.py

# Sync all categories
py 1_sync_llmbook.py --sync

# Preview changes
py 1_sync_llmbook.py --sync --dry-run

# Sync specific category
py 1_sync_llmbook.py --sync --category popular_science

# Include visuals
py 1_sync_llmbook.py --sync --include-visuals
```

**Categories:**

- `academic` → `reviewers/packages/v4/llmbook/academic/`
- `popular_science` → `reviewers/packages/v4/llmbook/popular_science/`
- `education` → `reviewers/packages/v4/llmbook/education/`
- `policy` → `reviewers/packages/v4/llmbook/policy/`
- `funding` → `reviewers/packages/v4/llmbook/funding/`
- `media` → `reviewers/packages/v4/llmbook/media/`

**Source:** `REPO-SYNC/LLM_BOOK/2_PUBLICATIONS/`
**Manifest:** `reviewers/LLMBOOK_SYNC_MANIFEST.json`

---

## 2. Package Reviews (`2_package_review.py`)

Extract path-specific review packages for AI reviewers.

**Key Feature:** `.shared/` (core reviewer package) auto-syncs when extracting any path.

```bash
# Show available paths and estimated sizes
py 2_package_review.py --status

# Extract single path (auto-syncs .shared/ first)
py 2_package_review.py workshop

# Extract multiple paths (auto-syncs .shared/ first)
py 2_package_review.py workshop arxiv

# Extract ALL paths (auto-syncs .shared/ first) ← RECOMMENDED
py 2_package_review.py --all

# Sync ONLY .shared/ (no path packages)
py 2_package_review.py --sync-shared

# Skip auto-sync if needed
py 2_package_review.py --all --no-sync-shared

# Preview without extracting
py 2_package_review.py workshop --dry-run

# Custom output location
py 2_package_review.py workshop --output ./FOR_OPUS
```

**Template Source:** `planning/reviewer_templates/` → `.shared/`

- Templates (START_HERE.md, REVIEWER_BRIEF.md, PACKAGE_INDEX.json) sync automatically
- PACKAGE_INDEX.json version increments on each sync (e.g., 1.1 → 1.2)

**Output:** `WHITE-PAPER/reviewers/packages/v4/{path}/`

**Available Paths (8 Publication Pipelines):**

| # | Path | Target Venue | Status |
|---|------|--------------|--------|
| 1 | workshop | NeurIPS/AAAI | READY |
| 2 | arxiv | cs.AI Preprint | READY |
| 3 | journal | Nature MI | Draft (awaits human validation) |
| 4 | popular_science | Atlantic/Wired | READY (LLM_BOOK) |
| 5 | education | OER/Coursera | READY (LLM_BOOK) |
| 6 | policy | Think tanks | READY (LLM_BOOK) |
| 7 | funding | NSF/DARPA | READY (LLM_BOOK) |
| 8 | media | Press/TED | READY (LLM_BOOK) |

**Expected Sizes (text-only):**

| Path | Size | Files | Notes |
|------|------|-------|-------|
| workshop | ~90 KB | ~13 | Core claims + validation |
| arxiv | ~360 KB | ~17 | Full methodology + results |
| journal | ~530 KB | ~29 | Complete with supplements |
| popular_science | ~30 KB | ~4 | Accessible narrative |
| education | ~40 KB | ~4 | Teaching modules |
| policy | ~30 KB | ~3 | Brief for decision-makers |
| funding | ~70 KB | ~6 | Proposal framework |
| media | ~35 KB | ~5 | Press-ready excerpts |

---

## 3. Generate PDFs (`3_generate_pdfs.py`)

Generate publication-ready PDFs from markdown sources using ReportLab.

```bash
cd WHITE-PAPER/calibration

# Generate from existing submissions/
py 3_generate_pdfs.py

# Extract from reviewers/ first, then generate (RECOMMENDED)
py 3_generate_pdfs.py --from-review

# Preview what would be extracted
py 3_generate_pdfs.py --from-review --dry-run
```

**Workflow:**

```text
reviewers/packages/v4/{path}/submissions/{path}/   <- Reviewers edit here
                    |
        py 3_generate_pdfs.py --from-review
                    |
                    v
submissions/{path}/{TYPE}_FINAL.md + .pdf          <- Ready to submit
```

**Output:** PDFs generated in their respective `submissions/` subdirectories.

**8 Publication Pipelines:**

| Pipeline | Source | Output |
|----------|--------|--------|
| arxiv | `arxiv/NYQUIST_ARXIV_PAPER_FINAL.md` | `NYQUIST_ARXIV_PAPER_FINAL.pdf` |
| workshop | `workshop/Nyquist_workshop_paper_FINAL.md` | `Nyquist_workshop_paper_FINAL.pdf` |
| journal | `journal/JOURNAL_PAPER_FINAL.md` | `JOURNAL_PAPER_FINAL.pdf` |
| funding | `funding/FUNDING_FINAL.md` | `FUNDING_FINAL.pdf` |
| policy | `policy/POLICY_FINAL.md` | `POLICY_FINAL.pdf` |
| media | `media/MEDIA_FINAL.md` | `MEDIA_FINAL.pdf` |
| education | `education/EDUCATION_FINAL.md` | `EDUCATION_FINAL.pdf` |
| popular_science | `popular_science/POPULAR_SCIENCE_FINAL.md` | `POPULAR_SCIENCE_FINAL.pdf` |

**IRON CLAD Methodology (all values from source markdown):**

- Event Horizon = 0.80 (cosine)
- p-value = 2.40e-23
- Settling time = tau_s ~ 10.2 probes
- 2 PCs for 90% variance

---

## 4. Publish Stats (`4_publish_stats.py`)

Extract statistics for dashboard integration.

```bash
cd WHITE-PAPER/calibration
py 4_publish_stats.py
```

**Output:** `publication_stats.json`

**What Gets Extracted:**

| Category | Data Points |
|----------|------------|
| **Claims (A-E)** | Name, status, key metric |
| **Runs** | Total count, S7 count, latest run |
| **Files** | Figures, ASCII, workshop, references, total |
| **Submissions** | Status and target for each path |
| **Key Statistics** | PFI correlation (ρ=0.91), threshold (D=0.80), 92% inherent ratio, stability (97.5%) |

**Dashboard Integration:**

```python
import json

with open("WHITE-PAPER/calibration/publication_stats.json") as f:
    pub_stats = json.load(f)

# Display metrics
st.metric("Claims Validated", f"{sum(1 for c in pub_stats['claims'].values() if c['status']=='validated')}/5")
st.metric("Runs Complete", pub_stats['runs']['total'])
```

---

## Files in This Directory

| File | Purpose |
|------|---------|
| `README.md` | This file |
| `0_sync_viz.py` | Sync S7_ARMADA visualizations to packages |
| `1_sync_llmbook.py` | Sync LLM_BOOK content to WHITE-PAPER |
| `2_package_review.py` | Review package extraction script |
| `3_generate_pdfs.py` | PDF generation (ReportLab) |
| `4_publish_stats.py` | Statistics extraction script |
| `publication_stats.json` | Generated statistics output |

---

## Typical Workflow

```bash
cd WHITE-PAPER/calibration

# 1. Sync visualizations (after regenerating in S7_ARMADA)
py 0_sync_viz.py --sync

# 2. Sync LLM_BOOK content (if updated)
py 1_sync_llmbook.py --sync

# 3. Extract all review packages
py 2_package_review.py --all

# 4. Generate publication PDFs (extract from reviewers/ first)
py 3_generate_pdfs.py --from-review

# 5. Update dashboard stats
py 4_publish_stats.py
```

---

## Key Metrics (COSINE ERA)

| Metric | Value | Source |
|--------|-------|--------|
| **Event Horizon** | D = 0.80 (cosine) | Run 023d IRON CLAD |
| **P-value** | 2.40e-23 | Chi-squared validation |
| **Inherent Drift** | ~93% | Run 020B IRON CLAD |
| **Context Damping** | 97.5% stability | Run 018 IRON CLAD |
| **PFI Correlation** | ρ = 0.91 | Cross-model validation |
| **Settling Time** | τₛ ≈ 7 probes | Run 023d |
| **Experiments** | 750 | Run 023d total |
| **Models** | 25 unique | 5 providers |

---

*Last updated: 2025-12-29*
*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23, 92% Inherent Drift*
