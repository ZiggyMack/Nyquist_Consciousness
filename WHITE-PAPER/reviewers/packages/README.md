# Reviewer Packages

**Last Updated:** December 24, 2025
**Status:** v2 packages ready with NotebookLLM integration

---

## Package Versions

### v2/ (Current - December 24, 2025)

**Run 023 IRON CLAD + NotebookLLM Integration**

Fresh extraction with:
- All 8 publication paths
- NotebookLLM synthesis content in `LLM_SYNTHESIS/` subdirs
- Updated Claims table (Cosine methodology)
- Event Horizon = 0.80 (calibrated)
- Cohen's d = 0.698 (honest model-level)
- Custom `REVIEWER_GUIDE.md` for arXiv + workshop

**Use this version for all new reviews.**

### v1/ (Historical - Pre-December 24, 2025)

Archived content from before:
- NotebookLLM integration
- Run 023 completion
- Cosine methodology standardization

**Preserved for historical reference. Do not use for new reviews.**

---

## Directory Structure

```
packages/
├── README.md              # This file
├── v1/                    # Historical (archived)
│   ├── arxiv/
│   ├── workshop/
│   └── ... (8 paths)
├── v2/                    # Current (Run 023 + NotebookLLM)
│   ├── arxiv/             # Priority
│   │   ├── REVIEWER_GUIDE.md
│   │   ├── README.md
│   │   ├── PACKAGE_MANIFEST.md
│   │   ├── LLM_SYNTHESIS/
│   │   ├── submissions/
│   │   ├── theory/
│   │   ├── figures/
│   │   └── ...
│   ├── workshop/          # Priority
│   │   ├── REVIEWER_GUIDE.md
│   │   ├── LLM_SYNTHESIS/
│   │   └── ...
│   ├── journal/
│   ├── popular_science/
│   ├── education/
│   ├── policy/
│   ├── funding/
│   └── media/
├── pdf/                   # PDF layer (separate)
└── visualization_pdfs/    # S7 ARMADA visualization summaries (16 PDFs)
```

---

## Quick Start for Reviewers

### For arXiv Review
```
v2/arxiv/REVIEWER_GUIDE.md  <- Start here
```

### For Workshop Review
```
v2/workshop/REVIEWER_GUIDE.md  <- Start here
```

---

## NotebookLLM Integration

Each v2 package includes an `LLM_SYNTHESIS/` subdirectory with relevant NotebookLLM outputs:

| Path | LLM_SYNTHESIS Contents |
|------|------------------------|
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

To regenerate v2 packages:

```bash
cd WHITE-PAPER/calibration
py extract_review_package.py --all
```

Output will go to `reviewers/packages/v2/`

---

## Package Sizes (v2)

| Path | Files | Size | Priority |
|------|-------|------|----------|
| **arxiv** | 94 | 8.9 MB | HIGH |
| **workshop** | 14 | 133 KB | HIGH |
| journal | 97 | 8.9 MB | Medium |
| popular_science | 4 | 51 KB | Low |
| education | 4 | 41 KB | Low |
| policy | 3 | 31 KB | Low |
| funding | 6 | 74 KB | Low |
| media | 5 | 35 KB | Low |

---

*Package infrastructure maintained by extract_review_package.py*
