# Reviewers Directory

This directory contains draft papers and reviews organized by review phase.

## Directory Structure

```text
reviewers/
├── README.md           # This file
├── phase1/             # Initial drafts (Dec 2025 - Code Claude + Opus 4.5)
│   ├── NYQUIST_ARXIV_PAPER_FINAL.md      # Full arXiv paper draft
│   ├── NYQUIST_WHITE_PAPER_FINAL.md      # Journal-style white paper
│   ├── Nyquist_workshop_paper_FINAL.md   # Workshop paper (4-8 pages)
│   ├── Nyquist_workshop_paper.md         # Workshop draft (earlier version)
│   ├── FINAL_VALIDATION_CHECKLIST.md     # Quality validation (99/100)
│   ├── NOVA_S7_REVIEW.md                 # Nova's comprehensive S7 review
│   ├── CODE_CLAUDE_PROMPT.md             # Generation prompts used
│   └── Code_claude_workshop_addendum.md  # Workshop-specific prompts
│
└── phase2/             # Post-figure review (Dec 2025 - Opus 4.5)
    ├── Workshop_paper_submission.md      # Submission-ready workshop paper
    ├── Submission_ready_paper.md         # Full paper ready for submission
    └── review_circulation_package.md     # Package review notes
```

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

## For General Reviewers

If you're reviewing the research (not generating papers):

1. Start with `phase1/FINAL_VALIDATION_CHECKLIST.md`
2. Read `phase1/NOVA_S7_REVIEW.md` for methodology critique
3. Review `phase2/review_circulation_package.md` for package structure
4. See `START_HERE.md` (parent directory) for full reading order
