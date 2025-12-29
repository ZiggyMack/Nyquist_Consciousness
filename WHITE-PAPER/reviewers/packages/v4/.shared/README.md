# .shared/ - Deduplicated Content Library

**Package Version:** v4 — IRON CLAD ERA
**Updated:** 2025-12-29

---

## Purpose

This directory contains **shared content** used across multiple publication paths. Instead of duplicating files like `MINIMUM_PUBLISHABLE_CLAIMS.md` across 8 paths, we store one copy here and reference it via `PACKAGE_INDEX.json`.

## Structure

```
.shared/
├── theory/              # Core theoretical documents
│   ├── MINIMUM_PUBLISHABLE_CLAIMS.md
│   ├── THEORY_SECTION.md
│   ├── HYPOTHESES_AND_RESULTS.md
│   └── B-CRUMBS.md
├── guides/              # Methodology and statistics
│   ├── summary_statistics.md
│   ├── MANIFEST.md
│   ├── UNIFIED_STATISTICS_REFERENCE.md
│   └── REPRODUCIBILITY_README.md
├── planning/            # Review orientation
│   ├── OPUS_REVIEW_BRIEF.md
│   ├── NOVAS_OVERCLAIMING_PREVENTION.md
│   ├── METHODOLOGY_DOMAINS.md
│   └── PUBLICATION_PIPELINE_MASTER.md
├── references/          # Bibliography
│   ├── references.md
│   └── references.bib
├── figures/             # Visual assets
│   ├── visual_index.md
│   ├── ascii/           # Text-based figures
│   ├── conceptual/      # Theory visualizations
│   └── experiments/     # Run 023 results
└── LLM_SYNTHESIS/       # NotebookLM outputs
    ├── README.md
    ├── INDEX.md
    └── [various reports and images]
```

## How It Works

1. **PACKAGE_INDEX.json** maps which files belong to which paths
2. **Path directories** (arxiv/, workshop/, etc.) contain ONLY path-specific content
3. **Reviewers work in** `{path}/submissions/{path}/` for each publication path
4. **3_generate_pdfs.py --from-review** extracts and generates final PDFs

## Benefits

| Benefit | Description |
|---------|-------------|
| **No duplication** | One copy of each shared file |
| **Easy updates** | Change once, affects all paths |
| **Smaller repo** | ~60% reduction in package size |
| **Clear ownership** | `PACKAGE_INDEX.json` is source of truth |

## Usage

### To generate submission PDFs:
```bash
cd WHITE-PAPER/calibration
py 3_generate_pdfs.py                # Generate from existing submissions/
py 3_generate_pdfs.py --from-review  # Extract from reviewers/ first, then generate
py 3_generate_pdfs.py --from-review --dry-run  # Preview what would be extracted
```

### To update shared content:
1. Edit the file in `.shared/`
2. No need to update path directories - they reference `.shared/`

### To add new shared content:
1. Add file to appropriate `.shared/` subdirectory
2. Update `PACKAGE_INDEX.json` with file mapping

---

## File Mapping (Summary)

| File | Paths |
|------|-------|
| `theory/MINIMUM_PUBLISHABLE_CLAIMS.md` | arxiv, journal, workshop, education, funding |
| `guides/summary_statistics.md` | ALL paths |
| `planning/OPUS_REVIEW_BRIEF.md` | ALL paths |
| `figures/experiments/run023/*` | arxiv, journal |

See `../PACKAGE_INDEX.json` for complete mapping.

---

*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23*
