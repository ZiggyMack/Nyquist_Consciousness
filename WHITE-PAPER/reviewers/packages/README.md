# Reviewer Packages

**Last Updated:** December 30, 2025
**Status:** v4 packages ready with Run 020B IRON CLAD complete (248 sessions, 37 ships)
**Version Source:** `CURRENT_VERSION.json`

---

## Package Versions

### v4/ (Current - December 29, 2025)

**Run 020B IRON CLAD Complete + Shared Content Architecture**

Major updates:
- **`.shared/` directory** — Deduplicated content across all 8 publication paths
- **PACKAGE_INDEX.json** — Maps shared content to paths
- **16 visualization PDFs** — Full IRON CLAD audit complete
- **Run 020B Complete:** 248 sessions, 37 IRON CLAD ships, ~93% inherent drift

Key features:
- Shared content architecture eliminates duplication (~60% size reduction)
- Reviewers work in `{path}/submissions/` directories (flat structure)
- Extract to final submission via `3_generate_pdfs.py --from-review`

**Use this version for all current work.**

### v3/ (December 26, 2025)

**Run 023 IRON CLAD Complete + Full Visualization Suite**

Historical snapshot with:
- All 8 publication paths (duplicated content)
- 16 visualization PDFs
- **Event Horizon = 0.80** (Cosine, calibrated)
- **750 experiments, 25 models, 5 providers**

**Superseded by v4. Preserved for reference.**

### v2/ (Historical - December 24, 2025)

Previous extraction with NotebookLLM integration. Superseded by v3.

**Preserved for historical reference. Do not use for new reviews.**

### v1/ (Historical - Pre-December 24, 2025)

Archived content from before Run 023 completion.

**Preserved for historical reference. Do not use for new reviews.**

---

## Directory Structure

```text
packages/
├── README.md              # This file
├── CURRENT_VERSION.json   # Source of truth for current version
├── v1/                    # Historical (archived)
├── v2/                    # Historical (superseded)
├── v3/                    # Historical (superseded by v4)
├── v4/                    # ★ CURRENT
│   ├── START_HERE.md      # Reviewer entry point
│   ├── REVIEWER_BRIEF.md  # Full orientation
│   ├── PACKAGE_INDEX.json # Shared content mapping
│   ├── .shared/           # ★ Deduplicated content library
│   │   ├── theory/        # Core theoretical documents
│   │   ├── guides/        # Methodology and statistics
│   │   ├── planning/      # Review orientation
│   │   ├── references/    # Bibliography
│   │   ├── figures/       # Visual assets
│   │   └── LLM_SYNTHESIS/ # NotebookLM outputs
│   ├── arxiv/             # arXiv preprint (path-specific)
│   ├── workshop/          # NeurIPS/AAAI (path-specific)
│   ├── journal/           # Nature MI (path-specific)
│   ├── popular_science/   # Atlantic/Wired (path-specific)
│   ├── education/         # OER/Coursera (path-specific)
│   ├── policy/            # Think tanks (path-specific)
│   ├── funding/           # NSF/DARPA (path-specific)
│   ├── media/             # Press/TED (path-specific)
│   ├── visualization_pdfs/# 16 S7 ARMADA visualization PDFs
│   └── feedback/          # Reviewer feedback goes here
└── pdf/                   # ★ Submission PDFs (flat structure for easy distribution)
    ├── NYQUIST_ARXIV_PAPER_FINAL.pdf
    ├── JOURNAL_PAPER_FINAL.pdf
    ├── Nyquist_workshop_paper_FINAL.pdf
    ├── EDUCATION_FINAL.pdf
    ├── FUNDING_FINAL.pdf
    ├── MEDIA_FINAL.pdf
    ├── POLICY_FINAL.pdf
    ├── POPULAR_SCIENCE_FINAL.pdf
    └── README.md
```

---

## Quick Start for Reviewers

### For Any Review

```text
v4/START_HERE.md  <- Start here (cold boot reading order)
```

### For arXiv Review

```text
v4/arxiv/submissions/  <- Full preprint draft
```

### For Workshop Review

```text
v4/workshop/submissions/  <- Workshop paper
```

### For Visualization Overview

```text
v4/visualization_pdfs/README.md  <- 16 PDF summaries
```

---

## THE THREE CORE CLAIMS — ALL VALIDATED (Cosine Methodology)

1. **DRIFT IS REAL** — p = 2.40e-23, cosine distance detects genuine identity differences
2. **WE DON'T CAUSE IT** — ~93% inherent drift ratio (Run 020B IRON CLAD)
3. **WE CAN MEASURE IT** — Cohen's d = 0.698 (model-level aggregates), 2 PCs = 90% variance

---

## Key Metrics (v4)

| Metric | Value | Source |
| ------ | ----- | ------ |
| **Event Horizon** | D = 0.80 | Run 023b calibration |
| **Cohen's d** | 0.698 | Run 023d model-level |
| **Inherent Drift** | ~93% | Run 020B IRON CLAD |
| **p-value** | 2.40e-23 | Run 023d perturbation |
| **PCs for 90%** | 2 | Run 023d PCA |
| **Settling Time** | τₛ ≈ 7 probes | Run 023d |
| **Fleet Size** | 25 models, 5 providers | Run 023d |
| **Experiments** | 750 | Run 023d |

---

## NotebookLM Integration

v4 packages include NotebookLM synthesis content in `.shared/LLM_SYNTHESIS/`:

| Path | LLM_SYNTHESIS Contents |
| ---- | ---------------------- |
| arxiv | Full academic paper + Technical report |
| journal | Full academic paper + Technical report |
| workshop | Briefing document |
| popular_science | Engineer's toolkit article |
| education | Visual guide to waveforms |
| policy | Briefing document |
| funding | Briefing document + Technical report |
| media | Engineer's toolkit article |

---

## Regenerating Packages

To regenerate v4 packages:

```bash
cd WHITE-PAPER/calibration
py 2_package_review.py --all
```

Output will go to `reviewers/packages/v4/`

**Note:** `--all` automatically copies submission PDFs to `packages/pdf/` for easy distribution.

To extract and generate final submission PDFs:

```bash
py 3_generate_pdfs.py --from-review  # Extract from reviewers/, generate PDFs
py 3_generate_pdfs.py                # Generate from existing submissions/
```

To copy submission PDFs to flat folder (standalone):

```bash
py 2_package_review.py --submission-pdfs
```

---

## Package Architecture (v4)

v4 uses a **shared content architecture** to eliminate duplication:

| Component | Purpose |
| --------- | ------- |
| `.shared/` | Deduplicated content (theory, guides, figures) |
| `PACKAGE_INDEX.json` | Maps shared files to publication paths |
| `{path}/submissions/` | Path-specific content + reviewer working area |
| `visualization_pdfs/` | 16 IRON CLAD visualization summaries |

**Size reduction:** ~60% compared to v3 (duplicated content eliminated)

---

*Package infrastructure maintained by 2_package_review.py*
*Submission workflow: 3_generate_pdfs.py --from-review*
*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23, ~93% inherent drift*
