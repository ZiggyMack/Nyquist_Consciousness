# Reviewer Packages

**Last Updated:** December 29, 2025
**Status:** v4 packages ready with Run 020B IRON CLAD data audit (221 sessions, 37 ships)

---

## Package Versions

### v4/ (Current - December 29, 2025)

**Run 020B IRON CLAD Data Audit + Updated Visualization PDFs**

Incremental update with 3 regenerated PDFs:
- **15_Oobleck_Effect_Summary.pdf** — Updated with full IRON CLAD data
- **run018_Summary.pdf** — Updated trajectory counts (1,549, was 1,145)
- **run020_Summary.pdf** — Updated with IRON CLAD (226 sessions, 38 ships)

Key data corrections:
- Run 020B: 226 sessions (was 73), 38 ships (was 7), 100% attribution
- Run 018: 1,549 trajectories (was 1,145), corrected provider counts
- Inherent drift ratio: ~92% (Control: 0.650, Treatment: 0.709)

**Use this version for current IRON CLAD data references.**

### v3/ (December 26, 2025)

**Run 023 IRON CLAD Complete + Full Visualization Suite**

Fresh extraction with:
- All 8 publication paths
- **16 visualization PDFs** in `visualization_pdfs/` (Run 023 summaries)
- NotebookLLM synthesis content in `LLM_SYNTHESIS/` subdirs
- Updated Claims table (Cosine methodology)
- **Event Horizon = 0.80** (Cosine, calibrated)
- **Cohen's d = 0.698** (honest model-level)
- **92% inherent drift** (Run 023 Thermometer Result)
- **750 experiments, 25 models, 5 providers**

**Use this version for Run 023 references and full package set.**

### v2/ (Historical - December 24, 2025)

Previous extraction with NotebookLLM integration. Superseded by v3.

**Preserved for historical reference. Do not use for new reviews.**

### v1/ (Historical - Pre-December 24, 2025)

Archived content from before Run 023 completion.

**Preserved for historical reference. Do not use for new reviews.**

---

## Directory Structure

```
packages/
├── README.md              # This file
├── v1/                    # Historical (archived)
├── v2/                    # Historical (superseded)
├── v3/                    # ★ CURRENT (Run 023 IRON CLAD)
│   ├── arxiv/             # Priority - arXiv preprint
│   │   ├── README.md
│   │   ├── PACKAGE_MANIFEST.md
│   │   ├── LLM_SYNTHESIS/     # NotebookLLM synthesis
│   │   ├── submissions/
│   │   ├── theory/
│   │   ├── guides/
│   │   ├── figures/
│   │   └── ...
│   ├── workshop/          # Priority - NeurIPS/AAAI
│   │   ├── README.md
│   │   ├── LLM_SYNTHESIS/
│   │   └── ...
│   ├── journal/           # Nature MI
│   ├── popular_science/   # Atlantic/Wired
│   ├── education/         # OER/Coursera
│   ├── policy/            # Think tanks
│   ├── funding/           # NSF/DARPA
│   ├── media/             # Press/TED
│   └── visualization_pdfs/    # ★ 16 S7 ARMADA visualization PDFs
│       ├── README.md
│       ├── 1_Vortex_Summary.pdf
│       ├── 2_Boundary_Mapping_Summary.pdf
│       ├── 3_Stability_Summary.pdf
│       ├── 4_Rescue_Summary.pdf
│       ├── 5_Settling_Summary.pdf
│       ├── 6_Architecture_Summary.pdf
│       ├── 8_Radar_Oscilloscope_Summary.pdf
│       ├── 9_FFT_Spectral_Summary.pdf
│       ├── 10_PFI_Dimensional_Summary.pdf
│       ├── 11_Unified_Dashboard_Summary.pdf
│       ├── 12_Metrics_Summary.pdf
│       ├── 13_Model_Waveforms_Summary.pdf
│       ├── 14_Ringback_Summary.pdf
│       ├── 15_Oobleck_Effect_Summary.pdf
│       ├── run018_Summary.pdf
│       └── run020_Summary.pdf
└── pdf/                   # Legacy PDF layer
```

---

## Quick Start for Reviewers

### For arXiv Review
```
v3/arxiv/README.md  <- Start here
```

### For Workshop Review
```
v3/workshop/README.md  <- Start here
```

### For Visualization Overview
```
v3/visualization_pdfs/README.md  <- 16 PDF summaries
```

---

## THE THREE CORE CLAIMS — ALL VALIDATED (Cosine Methodology)

1. **DRIFT IS REAL** — p = 2.40e-23, cosine distance detects genuine identity differences
2. **WE DON'T CAUSE IT** — 92% inherent drift ratio (Run 023 COSINE Thermometer Result)
3. **WE CAN MEASURE IT** — Cohen's d = 0.698 (model-level aggregates), 2 PCs = 90% variance

---

## Key Metrics (v3)

| Metric | Value | Source |
|--------|-------|--------|
| **Event Horizon** | D = 0.80 | Run 023 COSINE |
| **Cohen's d** | 0.698 | Run 023 model-level |
| **Inherent Drift** | 92% | Run 023 Thermometer |
| **p-value** | 2.40e-23 | Run 023 perturbation |
| **PCs for 90%** | 2 | Run 023 PCA |
| **Settling Time** | τₛ ≈ 10.2 | Run 023d |
| **Fleet Size** | 25 models, 5 providers | Run 023 |
| **Experiments** | 750 | Run 023 |

---

## NotebookLLM Integration

Each v3 package includes an `LLM_SYNTHESIS/` subdirectory with relevant NotebookLLM outputs:

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

To regenerate v3 packages:

```bash
cd WHITE-PAPER/calibration
py extract_review_package.py --all
```

Output will go to `reviewers/packages/v3/`

---

## Package Sizes (v3)

| Path | Files | Size | Priority |
|------|-------|------|----------|
| **arxiv** | 26 | 2.7 MB | HIGH |
| **workshop** | 16 | 2.5 MB | HIGH |
| journal | 30 | 2.8 MB | Medium |
| popular_science | 6 | 67 KB | Low |
| education | 6 | 60 KB | Low |
| policy | 5 | 50 KB | Low |
| funding | 9 | 99 KB | Low |
| media | 8 | 58 KB | Low |
| **visualization_pdfs** | 17 | ~15 MB | HIGH |

**Total:** 123 files across all packages

---

*Package infrastructure maintained by extract_review_package.py*
*Run 023 IRON CLAD: 750 experiments, 25 models, 5 providers*
