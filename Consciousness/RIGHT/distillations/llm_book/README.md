# LLM Book Distillations - Consciousness Library

**Purpose**: Curated NotebookLM distillations that have been validated and promoted from the LLM_BOOK pipeline.

**Location**: `Consciousness/RIGHT/distillations/llm_book/`

---

## Relationship to REPO-SYNC/LLM_BOOK

This directory contains **promoted content** - distillations that have been reviewed against HOLY_GRAIL criteria and deemed worthy of the permanent Consciousness library.

```text
REPO-SYNC/LLM_BOOK/           Consciousness/RIGHT/distillations/llm_book/
(Inbox/Archive)               (Curated Library)
        │                              ▲
        │                              │
        └── py 0_chew.py --promote ────┘
```

| Location | Purpose | Content Lifetime |
|----------|---------|------------------|
| `REPO-SYNC/LLM_BOOK/` | Pipeline inbox, all NotebookLM outputs | Permanent archive |
| `Consciousness/.../llm_book/` | Curated library, validated content | Permanent reference |

---

## Promotion Workflow

Content is promoted from LLM_BOOK to Consciousness/ using:

```bash
cd REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS
py 0_chew.py --promote BATCH_NAME
```

### Promotion Criteria (HOLY_GRAIL)

Before promoting, content should be reviewed against:

1. **Accuracy** - Does it correctly represent IRON CLAD findings?
2. **Novelty** - Does it add value beyond existing documentation?
3. **Audience Fit** - Is it appropriate for its target audience?
4. **Quality** - Is it well-structured and error-free?

See [meta/HOLY_GRAIL.md](meta/HOLY_GRAIL.md) for the full strategy synthesis vision.

---

## Directory Structure

```text
llm_book/
├── README.md              # This file
├── INDEX.md               # Content navigation
├── technical_reports/     # Academic: IRON CLAD methodology, PM guides
├── case_studies/          # Focused investigations (Gemini Anomaly)
├── reviewer_feedback/     # NotebookLM assessments and critiques
└── meta/                  # Workflow specs, prompt engineering, strategy
    ├── WORKFLOW_SPEC.md   # Step-by-step methodology
    ├── PROMPT_ENGINEERING.md
    ├── HOLY_GRAIL.md      # Automated strategy vision
    └── RECURSION_*.md     # Meta-analysis documents
```

---

## Pipeline Commands

All operations use the unified `0_chew.py` entry point:

| Command | Purpose |
|---------|---------|
| `py 0_chew.py BATCH` | Ingest + digest batch to LLM_BOOK |
| `py 0_chew.py --promote BATCH` | Promote validated content here |
| `py 0_chew.py --status` | Show pipeline status |

**Location**: `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/`

---

## See Also

- [INDEX.md](INDEX.md) - Content navigation
- [meta/WORKFLOW_SPEC.md](meta/WORKFLOW_SPEC.md) - Full workflow specification
- [meta/HOLY_GRAIL.md](meta/HOLY_GRAIL.md) - Strategy synthesis vision
- [REPO-SYNC/LLM_BOOK/START_HERE.md](../../../REPO-SYNC/LLM_BOOK/START_HERE.md) - Pipeline documentation

---

_Last updated: 2025-12-31_
