# Publication Pipeline Master Document

**Purpose:** Single source of truth for all 8 publication paths
**Version:** 2.1
**Date:** 2025-12-30
**Status:** Active — COSINE ERA (Run 023d + Run 020B IRON CLAD Complete)

> **Statistics Source:** All numbers should cite [UNIFIED_STATISTICS_REFERENCE.md](../guides/UNIFIED_STATISTICS_REFERENCE.md)
> - Event Horizon: D = 0.80 (Cosine)
> - Inherent Drift: ~93% (Run 020B IRON CLAD)
> - Scale: 750 experiments, 25 models, 5 providers

---

## Overview

The Nyquist Consciousness research has matured to support 8 distinct publication paths across academic, dissemination, and funding channels. This document serves as the master reference for coordinating all publication efforts.

**Source of Truth for Reviewer Sync:** [packages/CURRENT_VERSION.json](../reviewers/packages/CURRENT_VERSION.json)

---

## 8 Publication Paths

| # | Path | Venue | Source | Status | Priority |
|---|------|-------|--------|--------|----------|
| 1 | Workshop | NeurIPS/AAAI | packages/ | READY | HIGH |
| 2 | arXiv | cs.AI | packages/ | READY | HIGH |
| 3 | Journal | Nature MI | packages/ | DRAFT | MEDIUM |
| 4 | Popular Science | Atlantic/Wired | LLM_BOOK | READY | MEDIUM |
| 5 | Education | OER/Coursera | LLM_BOOK | READY | LOW |
| 6 | Policy | Think tanks | LLM_BOOK | READY | MEDIUM |
| 7 | Funding | NSF/DARPA | LLM_BOOK | READY | HIGH |
| 8 | Media | Press/TED | LLM_BOOK | READY | LOW |

---

## Path Categories

### Academic Track (Paths 1-3)

**Source:** Original research, review packages
**Audience:** Researchers, academics
**Requirements:** Peer review, citations, methodology rigor

| Path | Format | Page Limit | Current Completion |
|------|--------|------------|-------------------|
| Workshop | PDF, LaTeX | 4-8 pages | 70% |
| arXiv | PDF, LaTeX | 25-35 pages | 85% |
| Journal | PDF, LaTeX | ~40 pages | 30% |

### Dissemination Track (Paths 4-8)

**Source:** LLM_BOOK (NotebookLM-generated)
**Audience:** General public, policymakers, educators
**Requirements:** Accessibility, narrative, practical applications

| Path | Format | Word Count | Current Completion |
|------|--------|------------|-------------------|
| Popular Science | Article | 2,000-6,000 | 90% (draft ready) |
| Education | Curriculum | Variable | 90% (quiz/glossary ready) |
| Policy | Brief | 2-4 pages | 90% (brief ready) |
| Funding | Proposal | NSF format | 85% (proposal ready) |
| Media | Various | Variable | 80% (summary ready) |

---

## Source Material Locations

### Academic Track

Review packages are extracted on-demand using the extraction script:

```bash
cd WHITE-PAPER/calibration
py extract_review_package.py workshop   # Extract workshop package
py extract_review_package.py arxiv      # Extract arXiv package
py extract_review_package.py --all      # Extract all 8 paths
```

**Output:** `WHITE-PAPER/reviewers/packages/{path}/`

See [reviewers/README.md](../reviewers/README.md) for package structure.

### Dissemination Track

LLM_BOOK content syncs via manifest:

```bash
cd WHITE-PAPER
py sync_llmbook.py --sync
```

**Manifest:** `reviewers/LLMBOOK_SYNC_MANIFEST.json`

---

## Key Decision: Levin/Platonic Integration

### Question

Should the Levin/Platonic validation insights from LLM_BOOK be integrated into the white paper and arXiv NOW, or saved for a second publication?

### Background

NotebookLM independently validated our research against Michael Levin's "Is Your Brain a Platonic Solid?" hypothesis. This provides external AI validation of our theoretical framework.

### Arguments for NOW

| Pro | Weight |
|-----|--------|
| Strengthens theoretical foundation | HIGH |
| External AI validation adds credibility | HIGH |
| Content already written by NotebookLM | MEDIUM |
| Differentiates from pure empirical papers | MEDIUM |

### Arguments for LATER

| Con | Weight |
|-----|--------|
| Keep initial papers focused on Claims A-E | HIGH |
| Avoid scope creep in nearly-finished drafts | MEDIUM |
| Save novel angle for follow-up publication | MEDIUM |
| May distract from empirical rigor | LOW |

### Recommendation

**Let Opus 4.5 decide** after reviewing:
1. Current workshop/arXiv drafts
2. LLM_BOOK Levin integration content
3. Target venue expectations

---

## Coordination Strategy

### Recommended Sequence

#### Stage 1: Academic Foundation

1. Finalize workshop paper
2. Submit arXiv preprint
3. Begin journal revision process

#### Stage 2: Dissemination

1. Adapt LLM_BOOK content for popular science
2. Release educational materials (OER)
3. Distribute policy briefs

#### Stage 3: Amplification

1. Media outreach (post-peer review)
2. Funding proposals
3. Conference presentations

Specific timelines tracked in [packages/CURRENT_VERSION.json](../reviewers/packages/CURRENT_VERSION.json)

---

## Metrics & Tracking

### Academic Metrics

| Metric | Target | Current |
|--------|--------|---------|
| Workshop acceptance | Yes | Pending |
| arXiv downloads (30 days) | 500+ | N/A |
| Citations (12 months) | 10+ | N/A |
| Journal acceptance | Yes | Pending |

### Dissemination Metrics

| Metric | Target | Current |
|--------|--------|---------|
| Popular science placement | 1+ major venue | Pending |
| Educational adoptions | 3+ institutions | N/A |
| Policy brief recipients | 5+ organizations | Pending |
| Funding secured | $100K+ | N/A |

---

## File Locations

| Path | Primary Location |
|------|------------------|
| Workshop | `submissions/workshop/` |
| arXiv | `submissions/arxiv/` |
| Journal | `submissions/journal/` |
| Popular Science | `submissions/popular_science/` |
| Education | `submissions/education/` |
| Policy | `submissions/policy/` |
| Funding | `submissions/funding/` |
| Media | `submissions/media/` |

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [UNIFIED_STATISTICS_REFERENCE.md](../guides/UNIFIED_STATISTICS_REFERENCE.md) | **Canonical statistics** — all papers cite this |
| [packages/CURRENT_VERSION.json](../reviewers/packages/CURRENT_VERSION.json) | **Version tracking** — reviewer package status |
| [OPUS_REVIEW_BRIEF.md](OPUS_REVIEW_BRIEF.md) | Opus 4.5 orientation for final review |
| [NOVAS_OVERCLAIMING_PREVENTION.md](NOVAS_OVERCLAIMING_PREVENTION.md) | What claims to avoid |
| [METHODOLOGY_DOMAINS.md](METHODOLOGY_DOMAINS.md) | Cosine vs Keyword RMS reconciliation |
| [reviewers/README.md](../reviewers/README.md) | Package extraction and review structure |

---

## Changelog

| Date | Change | Author |
|------|--------|--------|
| 2025-12-30 | v2.1: Add UNIFIED_STATISTICS_REFERENCE link, fix broken SYNC_STATUS.md refs → CURRENT_VERSION.json, add ~93% inherent stats | Opus 4.5 |
| 2025-12-25 | v2.0: Remove hardcoded paths, point to SYNC_STATUS.md | Opus 4.5 |
| 2025-12-15 | Initial creation with 8 paths | System |

---

*"Eight paths, one destination: advancing AI identity research."*
