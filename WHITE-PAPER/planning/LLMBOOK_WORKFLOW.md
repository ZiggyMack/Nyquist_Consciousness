# LLM_BOOK Workflow: Distillation to Publication

**Purpose:** How to sync NotebookLM distillations from REPO-SYNC/LLM_BOOK/ and use them in WHITE-PAPER publications
**Version:** 1.0
**Date:** 2025-12-25
**Status:** Active

---

## Overview

NotebookLM generates publication-ready content ("distillations") that feed into 5 of the 8 publication paths. This document explains:

1. **How to bring in** distillations from `REPO-SYNC/LLM_BOOK/`
2. **How to use** those distillations in WHITE-PAPER publications

---

## Source and Target Structure

### Source: REPO-SYNC/LLM_BOOK/

```text
LLM_BOOK/
├── 2_PUBLICATIONS/
│   ├── academic/           → Workshop, arXiv, Journal supplementary
│   ├── popular_science/    → Atlantic/Wired style articles
│   ├── education/          → OER/Coursera materials
│   ├── policy/             → Think tank briefings
│   ├── funding/            → NSF/DARPA proposals
│   └── media/              → Press/TED summaries
│
└── 3_VISUALS/              → NotebookLM-generated diagrams
```

### Target: WHITE-PAPER/submissions/

```text
submissions/
├── arxiv/                  ← LLM_academic syncs here
├── popular_science/        ← LLM_popular_science syncs here
├── education/              ← LLM_education syncs here
├── policy/                 ← LLM_policy syncs here
├── funding/                ← LLM_funding syncs here
└── media/                  ← LLM_media syncs here
```

**Naming Convention:** Synced files get `LLM_` prefix (e.g., `LLM_Quiz.md`) to distinguish from hand-authored content.

---

## Step 1: Check Sync Status

Before syncing, see what's pending:

```bash
cd WHITE-PAPER
py sync_llmbook.py
```

This shows:
- Files found in each category
- Which are already synced (`[*]`)
- Which are pending (`[!]`)
- Total size

---

## Step 2: Sync Distillations

### Sync All Categories

```bash
py sync_llmbook.py --sync
```

### Preview Changes First (Dry Run)

```bash
py sync_llmbook.py --sync --dry-run
```

### Sync Specific Category

```bash
py sync_llmbook.py --sync --category popular_science
py sync_llmbook.py --sync --category education
```

### Include Visuals

```bash
py sync_llmbook.py --sync --include-visuals
```

Visuals go to: `WHITE-PAPER/figures/generated/llmbook/`

---

## Step 3: Use Distillations in Publications

### For Dissemination Paths (4-8)

These paths use LLM_BOOK content as the **primary source**:

| Path | LLM_BOOK Source | Use For |
|------|-----------------|---------|
| Popular Science | `2_PUBLICATIONS/popular_science/` | Atlantic/Wired articles |
| Education | `2_PUBLICATIONS/education/` | Quiz, Glossary, Curriculum |
| Policy | `2_PUBLICATIONS/policy/` | Briefing documents |
| Funding | `2_PUBLICATIONS/funding/` | NSF/DARPA proposals |
| Media | `2_PUBLICATIONS/media/` | Press releases, TED scripts |

**Workflow:**
1. Sync the category
2. Review `LLM_*.md` files in `submissions/{path}/`
3. Edit if needed (preserve `LLM_` prefix)
4. Generate PDF using `submissions/generate_paper_pdfs.py`

### For Academic Paths (1-3)

Academic paths (Workshop, arXiv, Journal) use LLM_BOOK as **supplementary** material:

- Levin/Platonic synthesis from NotebookLM
- Accessible explanations for appendices
- Cross-references to validate claims

**Workflow:**
1. Review `LLM_*.md` in `submissions/arxiv/`
2. Extract relevant quotes or summaries
3. Integrate into hand-authored paper sections
4. Cite as "NotebookLM synthesis" in methodology

---

## Step 4: Track Sync Status

### Manifest File

All syncs are tracked in:
```
WHITE-PAPER/reviewers/LLMBOOK_SYNC_MANIFEST.json
```

This records:
- File hashes (for change detection)
- Last sync timestamps
- Category mappings
- Sync history (last 20 operations)

### Update CURRENT_VERSION.json

After major syncs, optionally update:
```
WHITE-PAPER/reviewers/packages/CURRENT_VERSION.json
```

Add entry to version_history section if methodology changed.

---

## When to Sync

| Trigger | Action |
|---------|--------|
| New NotebookLM output | Run full sync |
| Updated LLM_BOOK content | Sync specific category |
| Before extracting review packages | Ensure synced |
| Before generating PDFs | Verify latest content |

---

## Category Mapping Reference

| LLM_BOOK Category | WHITE-PAPER Target | Publication Path |
|-------------------|-------------------|------------------|
| `academic` | `submissions/arxiv/` | arXiv, Workshop, Journal |
| `popular_science` | `submissions/popular_science/` | Popular Science |
| `education` | `submissions/education/` | Education |
| `policy` | `submissions/policy/` | Policy |
| `funding` | `submissions/funding/` | Funding |
| `media` | `submissions/media/` | Media |

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [PUBLICATION_PIPELINE_MASTER.md](PUBLICATION_PIPELINE_MASTER.md) | All 8 publication paths |
| [../reviewers/packages/CURRENT_VERSION.json](../reviewers/packages/CURRENT_VERSION.json) | Master version tracking |
| [../sync_llmbook.py](../sync_llmbook.py) | Sync script source |
| [../reviewers/LLMBOOK_SYNC_MANIFEST.json](../reviewers/LLMBOOK_SYNC_MANIFEST.json) | Sync manifest |

---

## Troubleshooting

### "No files found" in category

1. Check `REPO-SYNC/LLM_BOOK/2_PUBLICATIONS/{category}/` exists
2. Verify files have correct extensions (`.md`, `.pdf`)
3. Ensure LLM_BOOK is populated from NotebookLM

### Files not syncing (already synced)

The sync uses hash comparison. If content unchanged, it won't re-copy.
To force re-sync, delete the target file or modify the manifest.

### Manifest corrupted

Delete and regenerate:
```bash
del WHITE-PAPER\reviewers\LLMBOOK_SYNC_MANIFEST.json
py sync_llmbook.py --sync
```

---

*Created: 2025-12-25*
*For the 8-path publication pipeline*
