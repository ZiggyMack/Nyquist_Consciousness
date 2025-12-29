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
keywords:
  - consciousness
  - calibration
-->
# Calibration Pipeline

**Purpose:** Sync assets, generate PDFs, create review packages, and extract statistics.
**Last Updated:** 2025-12-29

---

## Quick Reference

| # | Script | Purpose | Typical Usage |
|---|--------|---------|---------------|
| 0 | `0_sync_viz.py` | Sync S7_ARMADA visualizations → packages | `py 0_sync_viz.py --sync` |
| 1 | `1_sync_llmbook.py` | Sync LLM_BOOK content → submissions | `py 1_sync_llmbook.py --sync` |
| 2 | `2_package_review.py` | Extract reviewer packages | `py 2_package_review.py --all` |
| 3 | `3_generate_pdfs.py` | Generate publication PDFs | `py 3_generate_pdfs.py` |
| 4 | `4_publish_stats.py` | Extract dashboard statistics | `py 4_publish_stats.py` |

**Workflow Order:** 0 → 1 → 2 → 3 → 4 (syncs first, stats last)

---

## 0. Sync Visualizations (`0_sync_viz.py`)

Sync visualization PDFs from S7_ARMADA to WHITE-PAPER packages.

```bash
# Quick status check
py 0_sync_viz.py --check

# Detailed status with timestamps
py 0_sync_viz.py --status

# Interactive mode (asks questions when uncertain)
py 0_sync_viz.py --interactive

# Auto-sync all outdated PDFs
py 0_sync_viz.py --sync

# Sync specific visualization
py 0_sync_viz.py --sync 15_Oobleck_Effect

# Regenerate PNGs + PDFs, then sync
py 0_sync_viz.py --regenerate --sync

# Target a different package version
py 0_sync_viz.py --sync --target v5
```

**Version Management:**

```bash
# Show current version and triggers
py 0_sync_viz.py --version-info

# Check if a change warrants a version bump
py 0_sync_viz.py --bump-check "IRON CLAD 100% complete"
py 0_sync_viz.py --bump-check "bug fix in legend"
```

Version rules are stored in `WHITE-PAPER/reviewers/packages/CURRENT_VERSION.json`:

- **Stay on current:** Bug fixes, data corrections, documentation
- **Create new version:** New runs, methodology changes, IRON CLAD milestones

**Known Visualizations:**

- `15_Oobleck_Effect/` → Oobleck Effect (Run 020A/B)
- `run018/` → Persona Pressure Experiment
- `run020/` → Tribunal + Control/Treatment

**Auto-Discovery:** Finds any directory with `*_Summary.pdf` files.

---

## 1. Sync LLM_BOOK (`1_sync_llmbook.py`)

Sync NotebookLM outputs from LLM_BOOK to WHITE-PAPER submissions.

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

- `academic` → `submissions/arxiv/`
- `popular_science` → `submissions/popular_science/`
- `education` → `submissions/education/`
- `policy` → `submissions/policy/`
- `funding` → `submissions/funding/`
- `media` → `submissions/media/`

**Source:** `REPO-SYNC/LLM_BOOK/2_PUBLICATIONS/`
**Manifest:** `reviewers/LLMBOOK_SYNC_MANIFEST.json`

---

## 2. Package Reviews (`2_package_review.py`)

Extract path-specific review packages for AI reviewers.

```bash
# Show available paths and estimated sizes
py 2_package_review.py --status

# Extract single path
py 2_package_review.py workshop

# Extract multiple paths
py 2_package_review.py workshop arxiv

# Extract ALL paths
py 2_package_review.py --all

# Include figures (increases size)
py 2_package_review.py arxiv --include-figures

# Preview without extracting
py 2_package_review.py workshop --dry-run

# Custom output location
py 2_package_review.py workshop --output ./FOR_OPUS
```

**Output:** `WHITE-PAPER/reviewers/packages/{path}/`

**Available Paths:** workshop, arxiv, journal, popular_science, education, policy, funding, media

**Expected Sizes (text-only):**

| Path | Size | Files |
|------|------|-------|
| workshop | ~90 KB | ~13 |
| arxiv | ~360 KB | ~17 |
| journal | ~530 KB | ~29 |
| popular_science | ~30 KB | ~4 |
| education | ~40 KB | ~4 |
| policy | ~30 KB | ~3 |
| funding | ~70 KB | ~6 |
| media | ~35 KB | ~5 |

---

## 3. Generate PDFs (`3_generate_pdfs.py`)

Generate publication-ready PDFs from markdown sources using ReportLab.

```bash
cd WHITE-PAPER/calibration
py 3_generate_pdfs.py
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
| **Key Statistics** | PFI correlation, threshold, 92% ratio, stability |

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

# 4. Generate publication PDFs
py 3_generate_pdfs.py

# 5. Update dashboard stats
py 4_publish_stats.py
```

---

*Last updated: 2025-12-29*
*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23*
