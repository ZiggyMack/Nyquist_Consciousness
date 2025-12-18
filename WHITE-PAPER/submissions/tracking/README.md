<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
keywords:
  - consciousness
-->
# Submission Tracking Infrastructure

**Created:** 2025-12-16
**Updated:** 2025-12-16
**Purpose:** Track all publication submissions across 8 paths and 15+ venues
**Status:** IRON CLAD COMPLETE + EXTERNAL REVIEW

---

## BREAKING: External Validation

Grok (xAI) reviewed Workshop + arXiv PDFs — **VALIDATED**

- See: [../../reviewers/Grok/review_1.md](../../reviewers/Grok/review_1.md)

---

## Quick Status

| Track | Ready | Submitted | Accepted |
|-------|-------|-----------|----------|
| Academic (3) | 3 | 0 | 0 |
| Dissemination (5) | 5 | 0 | 0 |
| **Total** | **8** | **0** | **0** |

**Next Action:** Submit arXiv preprint (ASAP)

---

## Directory Structure

```
tracking/
├── README.md                     # This file
├── SUBMISSION_STATUS.md          # Master dashboard
├── DEADLINES.md                  # All deadlines
├── VENUE_TEMPLATES/              # Per-venue preparation
│   ├── arxiv/
│   │   └── submission_checklist.md
│   ├── aaai/
│   │   └── submission_checklist.md
│   ├── nature_mi/
│   │   └── submission_checklist.md
│   ├── neurips/                  # Future
│   └── policy/                   # Future
├── COVER_LETTERS/                # Cover letters and abstracts
│   ├── arxiv_abstract.md
│   └── nature_mi_cover.md
└── RESPONSES/                    # Reviewer responses
    └── README.md
```

---

## Key Documents

| Document | Purpose | Status |
|----------|---------|--------|
| [SUBMISSION_STATUS.md](SUBMISSION_STATUS.md) | Master tracking dashboard | CURRENT |
| [DEADLINES.md](DEADLINES.md) | All deadlines in one place | CURRENT |
| [VENUE_TEMPLATES/arxiv/](VENUE_TEMPLATES/arxiv/) | arXiv submission prep | READY |
| [VENUE_TEMPLATES/aaai/](VENUE_TEMPLATES/aaai/) | AAAI-26 submission prep | READY |
| [VENUE_TEMPLATES/nature_mi/](VENUE_TEMPLATES/nature_mi/) | Nature MI submission prep | READY |
| [COVER_LETTERS/](COVER_LETTERS/) | Cover letters and abstracts | DRAFTS |

---

## Workflow

### Adding a New Submission

1. Create venue template in `VENUE_TEMPLATES/{venue}/`
2. Add checklist based on venue requirements
3. Add entry to `SUBMISSION_STATUS.md`
4. Add deadline to `DEADLINES.md`
5. Prepare cover letter in `COVER_LETTERS/`

### Tracking Progress

1. Update checklist items as completed
2. Update status in `SUBMISSION_STATUS.md`
3. Move between stages: READY → SUBMITTED → UNDER REVIEW → ACCEPTED/REJECTED

### Handling Reviews

1. Create venue folder in `RESPONSES/`
2. Save original reviews
3. Create response document
4. Track revisions made

---

## Priority Order

| Priority | Venue | Deadline | Action |
|----------|-------|----------|--------|
| 1 | arXiv | ASAP | Submit preprint |
| 2 | AAAI-26 | Jul 25, 2025 | Prepare abstract |
| 3 | Nature MI | Q1 2026 | Submit journal |
| 4 | Workshops | Aug 2026 | NeurIPS/ICML |

---

## Related Resources

- [../SUBMISSION_VENUE_GUIDE.md](../../reviewers/Convos/phase5/SUBMISSION_VENUE_GUIDE.md) — Complete venue analysis
- [../../reviewers/packages/pdf/](../../reviewers/packages/pdf/) — Generated PDFs
- [../../figures/generated/](../../figures/generated/) — Publication figures

---

## Statistics

| Metric | Value |
|--------|-------|
| Total venues identified | 15+ |
| Papers ready | 8 |
| PDFs generated | 8 |
| Checklists created | 3 |
| Cover letters drafted | 2 |

---

*"No missed deadlines. No excuses. Eight paths, one destination."*
