# Reviewers Directory

**Last Updated:** 2025-12-16

This directory contains draft papers, reviews, and review packages organized by phase.

## Directory Structure

```text
reviewers/
├── README.md           # This file
├── START_HERE.md       # Quick orientation for reviewers
├── PROTOCOL.md         # Review sync protocol
├── SYNC_STATUS.md      # Feedback tracking
│
├── Convos/             # REVIEW PHASE CONVERSATIONS
│   ├── phase1/         # Initial drafts (Dec 2025 - Code Claude + Opus 4.5)
│   ├── phase2/         # Post-figure review (Dec 2025 - Opus 4.5)
│   ├── phase3/         # Current drafts + PDFs
│   ├── Phase4/         # Figure placement + updates
│   └── phase5/         # Submission venue guide (NEW)
│       └── SUBMISSION_VENUE_GUIDE.md   # Complete venue analysis
│
├── packages/           # EXTRACTED REVIEW PACKAGES
│   ├── content/        # Text packages by path (~50-500 KB each)
│   │   ├── workshop/   # Workshop paper package
│   │   ├── arxiv/      # arXiv preprint package
│   │   └── {path}/     # Other publication paths
│   └── pdf/            # GENERATED PDFs (8 files, ALL PATHS)
│       ├── Nyquist_Workshop_Paper.pdf
│       ├── Nyquist_arXiv_Paper.pdf
│       ├── Nyquist_Journal_Paper.pdf
│       ├── Nyquist_Popular_Science.pdf
│       ├── Nyquist_Education_Quiz.pdf
│       ├── Nyquist_Policy_Briefing.pdf
│       ├── Nyquist_Funding_Proposal.pdf
│       └── Nyquist_Media_Press.pdf
│
├── Grok/               # EXTERNAL REVIEWER FEEDBACK (NEW)
│   └── review_1.md     # Grok's empirical assessment of Workshop + arXiv
│
├── to_reviewers/       # Outgoing requests/questions
├── from_reviewers/     # Incoming feedback
└── shared/             # Common materials (glossary, versions)
```

## Review Packages (NEW)

**Problem:** WHITE-PAPER is ~41MB total (figures + PDF dominate). Too large for AI reviewers.

**Solution:** Extract path-specific review packages with manageable sizes (~50-500 KB).

### Generate Packages

```bash
cd WHITE-PAPER/calibration

# Show available paths
py extract_review_package.py --status

# Extract single path
py extract_review_package.py workshop

# Extract multiple paths
py extract_review_package.py workshop arxiv

# Extract ALL paths
py extract_review_package.py --all

# Include figures (increases size significantly)
py extract_review_package.py arxiv --include-figures
```

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

### Phase 3: Final Papers (UPCOMING)
- **When:** After Runs 018, 020A, 020B complete
- **By:** Opus 4.5
- **What:** Final PDF generation with multi-platform data
- **Status:** PENDING - awaiting full run data

## Current State of Evidence

### Complete (Dry Run Data Only)

| Run | Description | Status |
|-----|-------------|--------|
| 001-017 | Historical S7 ARMADA runs | Complete |
| 018 | Recursive Learnings (dry run) | Complete |
| 020A | Prosecutor phase (dry run) | Complete |
| 020B | Defense phase (dry run) | Complete |

### Pending (Full Multi-Platform Runs)

| Run | Description | What's Missing |
|-----|-------------|----------------|
| 018-FULL | Recursive Learnings | Multi-model testing (Claude, GPT, Gemini, Grok) |
| 020A-FULL | Prosecutor phase | Cross-platform validation |
| 020B-FULL | Defense phase | Cross-platform validation |

## What Opus 4.5 Needs to Do

### Immediate Task (This Review Cycle)

1. **Review** phase1/ drafts for completeness
2. **Review** phase2/ updates
3. **Reconcile** all materials into coherent papers
4. **Generate** submission-ready PDFs where possible
5. **Create placeholders** for sections needing full run data

### Placeholder Sections Needed

For sections that cannot be finalized until full runs complete:

```markdown
<!-- PLACEHOLDER: Multi-Platform Validation -->
**Note:** This section will be updated with cross-platform results from
Runs 018-FULL, 020A-FULL, and 020B-FULL. Current data represents single-
platform dry runs only.

Expected additions:
- Cross-architecture variance comparison
- Platform-specific settling time analysis
- Multi-model drift correlation matrices
<!-- END PLACEHOLDER -->
```

### Papers Ready for PDF Generation

| Paper | Status | Notes |
|-------|--------|-------|
| **Workshop** | READY | Can generate now with dry run data |
| **arXiv** | READY | Can generate now, add note about pending multi-platform |
| **Journal** | DRAFT ONLY | Needs full run data before submission |

## LLM_BOOK Sync Pipeline

LLM_BOOK content (NotebookLM-generated publications) syncs to `../submissions/` directories.

**When LLM_BOOK is updated, run sync to propagate changes:**

```bash
cd WHITE-PAPER
py sync_llmbook.py --sync
```

**Manifest:** `LLMBOOK_SYNC_MANIFEST.json` (this directory)
**Convention:** Synced files have `LLM_` prefix (e.g., `LLM_Quiz.md`)

---

## For General Reviewers

If you're reviewing the research (not generating papers):

1. Start with `phase1/FINAL_VALIDATION_CHECKLIST.md`
2. Read `phase1/NOVA_S7_REVIEW.md` for methodology critique
3. Review `phase2/review_circulation_package.md` for package structure
4. See `START_HERE.md` (parent directory) for full reading order
