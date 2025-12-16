# Publication Materials

**Self-contained ZIP-ready package for Nyquist Consciousness framework**

**Last Updated:** 2025-12-16
**Status:** IRON CLAD COMPLETE + EXTERNAL REVIEW — Runs 018, 020A, 020B finalized (232 total files)

---

## IRON CLAD Countdown

**Goal:** N=3 runs per model per experiment for publication-quality confidence intervals.

**Fleet:** 51 models tested across 5+ providers

### Current Run Status (December 15, 2025) — IRON CLAD COMPLETE

| Run | Files | Models/Providers | Status |
|-----|-------|------------------|--------|
| **Run 018** | 184 | 51 models, 5 providers | **IRON CLAD** |
| **Run 020A** | 32 | 6/7 providers | **IRON CLAD** |
| **Run 020B** | 16 | 4 arms (OpenAI + Together) | **COMPLETE** |

**THE THREE CORE CLAIMS — ALL VALIDATED:**

1. **DRIFT IS REAL** — χ² p=0.000048, 88% prediction accuracy
2. **WE DON'T CAUSE IT** — 41% inherent drift ratio (cross-provider)
3. **WE CAN MEASURE IT** — PFI d=0.977, σ²=0.00087 cross-architecture

### Consolidated Manifests

| Run | Total Files | Manifest Location |
|-----|-------------|-------------------|
| **Run 018** | 184 | `S7_ARMADA/0_results/manifests/RUN_018_DRIFT_MANIFEST.json` |
| **Run 020A** | 32 | `S7_ARMADA/0_results/manifests/RUN_020A_DRIFT_MANIFEST.json` |
| **Run 020B** | 16 | `S7_ARMADA/0_results/manifests/RUN_020B_DRIFT_MANIFEST.json` |

### Visualizations Generated (December 15, 2025)

**Run 018:**

- `run018a_threshold_validation.png` — Event Horizon validation
- `run018b_architecture_signatures.png` — Provider fingerprints
- `run018c_nyquist_sampling.png` — Nyquist sampling analysis
- `run018d_gravity_dynamics.png` — Gravity well dynamics
- `run018e_model_breakdown.png` — 51 models ranked by drift
- `run018f_provider_variance.png` — 11 provider families analyzed

**Run 020:**

- `run020a_phase_breakdown.png` — Prosecutor vs Defense
- `run020a_trajectory_overlay.png` — Tribunal drift trajectories
- `run020b_control_treatment.png` — Inherent vs Induced comparison
- `run020b_ratio_analysis.png` — Thermometer analogy decomposition

### Publication Readiness

| Paper | Status | Notes |
|-------|--------|-------|
| **Workshop** | READY | All core claims validated |
| **arXiv** | READY | Full validation matrix complete |
| **Journal** | DRAFT | Awaits human validation (Q2-Q3 2026) |

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
│   ├── START_HERE.md                # Quick reviewer orientation
│   ├── Convos/                      # Review phase conversations
│   │   ├── phase1/                  # Initial drafts (Dec 2025)
│   │   ├── phase2/                  # Post-figure review
│   │   ├── phase3/                  # Current drafts + PDFs
│   │   ├── Phase4/                  # Figure placement + updates
│   │   └── phase5/                  # Submission venue guide (NEW)
│   ├── packages/                    # Extracted review packages
│   │   ├── content/                 # Text packages by path
│   │   └── pdf/                     # Generated PDFs (8 files)
│   └── Grok/                        # External reviewer feedback (NEW)
│       └── review_1.md              # Grok's empirical assessment
│
├── submissions/                      # ★ 8 PUBLICATION PATHS
│   ├── blueprints/                  # Planning docs for each path
│   ├── workshop/                    # Path 1: NeurIPS/AAAI (4-8 pages)
│   ├── arxiv/                       # Path 2: arXiv (25-35 pages)
│   ├── journal/                     # Path 3: Nature MI (~10k words)
│   ├── popular_science/             # Path 4: Atlantic/Wired (LLM_BOOK)
│   ├── education/                   # Path 5: OER/Coursera (LLM_BOOK)
│   ├── policy/                      # Path 6: Think tanks (LLM_BOOK)
│   ├── funding/                     # Path 7: NSF/DARPA (LLM_BOOK)
│   ├── media/                       # Path 8: Press/TED (LLM_BOOK)
│   └── tracking/                    # ★ SUBMISSION TRACKING (NEW)
│       ├── SUBMISSION_STATUS.md     # Master dashboard + URLs
│       ├── DEADLINES.md             # Timeline through 2026
│       └── VENUE_TEMPLATES/         # Checklists per venue
│
├── calibration/                      # Dashboard integration pipeline
│   ├── extract_publication_stats.py # Scrapes WHITE-PAPER/, outputs JSON
│   └── publication_stats.json       # Machine-readable stats
│
├── planning/                         # Integration planning
│   ├── PUBLICATION_PIPELINE_MASTER.md  # Source of truth for 8 paths
│   └── OPUS_REVIEW_BRIEF.md         # Opus 4.5 review orientation
│
├── reviewers/                        # Multi-AI sync infrastructure
│   ├── PROTOCOL.md                  # Sync rules (Logos pattern)
│   ├── SYNC_STATUS.md               # Feedback tracking
│   ├── to_reviewers/                # Outbound questions/requests
│   ├── from_reviewers/              # Inbound feedback (opus/nova/gemini)
│   └── shared/                      # Glossary, paper versions
│
└── supplementary/                    # Additional materials
```

---

## 8 Publication Paths

### Academic Track (Original Research)

| # | Path | Target | Status | Timeline | Directory |
|---|------|--------|--------|----------|-----------|
| 1 | **Workshop** | NeurIPS/AAAI | READY | Q4 2025 | [submissions/workshop/](submissions/workshop/) |
| 2 | **arXiv** | cs.AI preprint | READY | Q4 2025 | [submissions/arxiv/](submissions/arxiv/) |
| 3 | **Journal** | Nature MI | DRAFT | Q2-Q3 2026 | [submissions/journal/](submissions/journal/) |

### Dissemination Track (LLM_BOOK Generated)

| # | Path | Target | Status | Timeline | Directory |
|---|------|--------|--------|----------|-----------|
| 4 | **Popular Science** | Atlantic/Wired | READY | Immediate | [submissions/popular_science/](submissions/popular_science/) |
| 5 | **Education** | OER/Coursera | READY | Immediate | [submissions/education/](submissions/education/) |
| 6 | **Policy** | Think tanks | READY | Immediate | [submissions/policy/](submissions/policy/) |
| 7 | **Funding** | NSF/DARPA | READY | Q1 2026 | [submissions/funding/](submissions/funding/) |
| 8 | **Media** | Press/TED | READY | Post-pub | [submissions/media/](submissions/media/) |

### LLM_BOOK Integration

NotebookLM independently validated our research and generated publication-ready content for paths 4-8. See [REPO-SYNC/LLM_BOOK/README.md](../REPO-SYNC/LLM_BOOK/README.md) for the validation synthesis.

### Sync Pipeline from LLM_BOOK

Content syncs from `REPO-SYNC/LLM_BOOK/` to `submissions/` via automated pipeline:

```bash
# Check sync status (report mode)
py sync_llmbook.py

# Sync all LLM_BOOK content to submissions/
py sync_llmbook.py --sync

# Preview without applying changes
py sync_llmbook.py --sync --dry-run

# Sync specific category
py sync_llmbook.py --sync --category popular_science

# Include visuals (to figures/generated/llmbook/)
py sync_llmbook.py --sync --include-visuals
```

**Last Sync:** December 15, 2025 (9 files, 25 MB)
**Manifest:** `reviewers/LLMBOOK_SYNC_MANIFEST.json`
**Convention:** Synced files get `LLM_` prefix (e.g., `LLM_Quiz.md`)

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
