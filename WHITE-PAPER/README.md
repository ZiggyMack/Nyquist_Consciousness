# Publication Materials

**Self-contained ZIP-ready package for Nyquist Consciousness framework**

**Last Updated:** 2025-12-14
**Status:** IRON CLAD validation in progress

---

## IRON CLAD Countdown

**Goal:** N=3 runs per provider per experiment for publication-quality confidence intervals.

### Current Run Status (December 14, 2025)

| Experiment | Claude | GPT-5/O | Gemini | Grok | Together | Status |
|------------|--------|---------|--------|------|----------|--------|
| **018 threshold** | - | **RUNNING** | 1/3 | - | 3/3 | 4/15 |
| **018 nyquist** | - | **RUNNING** | 1/3 | - | 3/3 | 4/15 |
| **018 gravity** | - | **RUNNING** | 1/3 | - | 3/3 | 4/15 |
| **020A tribunal** | - | **RUNNING** | 1/3 | 1/3 | - | 2/15 |
| **020B induced** | - | **RUNNING** | - | - | 1/3 | 1/15 |

Progress: ~15/75 runs complete (20%)

### What's Blocking Publication

| Paper | Blocking Issue | Required Runs |
|-------|----------------|---------------|
| **Workshop** | Cross-platform 82% replication | 020B × 3 providers |
| **arXiv** | Full validation matrix | All experiments × N=3 |
| **Journal** | Everything + human validation | Q2-Q3 2026 |

### Active Background Processes

5 experiments currently running (OpenAI GPT-5/O-series with syntax fix):

- Run 018 threshold (a094f0)
- Run 018 nyquist (0fc8e6)
- Run 018 gravity (603033)
- Run 020A tribunal (4c0f03)
- Run 020B induced (77c656)

---

## Quick Start

1. **New reviewer?** Start with [START_HERE.md](START_HERE.md)
2. **Looking for theory?** See [theory/](theory/) directory
3. **Ready to generate papers?** Check [submissions/](submissions/) for each path

---

## Directory Structure

```
WHITE-PAPER/                          # Self-contained ZIP-ready package
├── README.md                         # This file
├── START_HERE.md                     # Reviewer orientation
│
├── theory/                           # Core theoretical docs
│   ├── B-CRUMBS.md                  # 15 evidence pillars
│   ├── THEORY_SECTION.md            # Integrated theory
│   ├── MINIMUM_PUBLISHABLE_CLAIMS.md # Claims A-E
│   └── HYPOTHESES_AND_RESULTS.md    # 36 hypotheses
│
├── guides/                           # Navigation & reproduction
│   ├── MANIFEST.md                  # File inventory
│   ├── REPRODUCIBILITY_README.md    # How to reproduce
│   └── summary_statistics.md        # Key numbers
│
├── references/                       # Bibliography
│   ├── references.bib               # BibTeX (55 refs)
│   └── references.md                # Readable list
│
├── figures/                          # All visuals
│   ├── fig*.md + .py (×9)           # Publication figures
│   ├── generate_all_figures.py      # Batch script to regenerate all
│   ├── generated/                   # Rendered output
│   │   ├── png/ (9 files @ 300 DPI)
│   │   └── pdf/ (9 files)
│   ├── suggested/                   # S7 ARMADA supplementary visuals (8 files)
│   └── ascii/                       # ASCII diagrams (7 files)
│
├── reviewers/                        # Draft papers + reviews
│   ├── README.md                    # Phase structure guide
│   ├── phase1/                      # Initial drafts (Dec 2025)
│   │   ├── NYQUIST_ARXIV_PAPER_FINAL.md
│   │   ├── NYQUIST_WHITE_PAPER_FINAL.md
│   │   ├── Nyquist_workshop_paper_FINAL.md
│   │   ├── NOVA_S7_REVIEW.md
│   │   └── FINAL_VALIDATION_CHECKLIST.md
│   └── phase2/                      # Post-figure review (Dec 2025)
│       ├── Workshop_paper_submission.md
│       ├── Submission_ready_paper.md
│       └── review_circulation_package.md
│
├── submissions/                      # ★ 3 PUBLICATION PATHS
│   ├── blueprints/                  # Planning docs for each path
│   ├── workshop/                    # Path 1: NeurIPS/AAAI (4-8 pages)
│   ├── arxiv/                       # Path 2: arXiv (25-35 pages)
│   └── journal/                     # Path 3: Nature MI (~10k words)
│
├── calibration/                      # Dashboard integration pipeline
│   ├── extract_publication_stats.py # Scrapes WHITE-PAPER/, outputs JSON
│   └── publication_stats.json       # Machine-readable stats
│
├── planning/                         # Integration planning
└── supplementary/                    # Additional materials
```

---

## 3 Publication Paths

| Path | Target | Format | Status | Directory |
|------|--------|--------|--------|-----------|
| **Workshop** | NeurIPS/AAAI | 4-8 pages | Ready | [submissions/workshop/](submissions/workshop/) |
| **arXiv** | cs.AI preprint | 25-35 pages | Ready | [submissions/arxiv/](submissions/arxiv/) |
| **Journal** | Nature MI | ~10k words | Planning (Q2-Q3 2026) | [submissions/journal/](submissions/journal/) |

---

## Key Findings (Claims A-E)

| Claim | Finding | Evidence |
|-------|---------|----------|
| **A** | PFI is valid structured measurement | ρ≈0.91, d≈0.98 |
| **B** | Regime threshold at D≈1.23 | p≈4.8e-5 |
| **C** | Damped oscillator dynamics | τₛ, ringbacks measurable |
| **D** | Context damping works | 97.5% stability |
| **E** | Drift is mostly inherent | **82% ratio** |

---

## For Opus 4.1: How to Generate PDFs

1. **Read** `START_HERE.md` for orientation
2. **Review** `theory/` for core content
3. **Use** `submissions/blueprints/` for writing guidance per path
4. **Reference** `reviewers/` for existing drafts
5. **Include** `figures/generated/png/` for main figures (9 files rendered @ 300 DPI)
6. **Optionally include** `figures/suggested/` for S7 supplementary visuals (8 files)
7. **Cite** `references/references.bib`
8. **Generate** PDFs for each publication path

### Regenerating Figures

To regenerate all figures:

```bash
cd WHITE-PAPER/figures
py generate_all_figures.py
```

Output: `generated/png/` and `generated/pdf/` directories with all 9 publication figures.

---

## Dashboard Integration

Run the calibration script to extract stats for dashboard:

```bash
cd WHITE-PAPER/calibration
py extract_publication_stats.py
```

Output: `publication_stats.json` — machine-readable stats for AI_ARMADA.py

---

## Citation

```bibtex
@article{nyquist2025,
  title={Nyquist Consciousness: Identity Compression and Reconstruction Across AI Architectures},
  author={[Authors]},
  journal={arXiv preprint arXiv:XXXX.XXXXX},
  year={2025}
}
```

---

## License

- **Publications:** CC-BY-4.0
- **Code:** MIT License

---

*This package represents 21 experimental runs, 36 hypotheses, and extensive theoretical development.*
