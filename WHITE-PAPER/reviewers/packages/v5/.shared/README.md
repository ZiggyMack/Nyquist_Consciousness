# .shared/ - Self-Contained Reviewer Package Core

**Package Version:** v4 — IRON CLAD ERA
**Updated:** 2025-12-30

---

## Purpose

This directory is a **self-contained minimum viable package** that can be given to any reviewer first. It contains:

1. **Core orientation files** — START_HERE.md, REVIEWER_BRIEF.md
2. **Shared content** — Deduplicated documents used across all publication paths
3. **Package index** — PACKAGE_INDEX.json maps content to paths

## Minimum Delivery

If you're sending materials in pieces, **always send `.shared/` first**. It provides:
- Complete research orientation
- All key numbers and claims
- Terminology glossary
- Visual quick start guide
- Run registry (which run proves what)

Reviewers can begin their assessment immediately, then receive path-specific content (arxiv/, workshop/, etc.) as follow-up deliveries.

---

## Structure

```
.shared/
├── START_HERE.md           # Entry point for all reviewers
├── REVIEWER_BRIEF.md       # Full orientation with key numbers
├── PACKAGE_INDEX.json      # Content-to-path mapping
├── README.md               # This file
│
├── theory/                 # Core theoretical documents
│   ├── MINIMUM_PUBLISHABLE_CLAIMS.md
│   ├── THEORY_SECTION.md
│   ├── HYPOTHESES_AND_RESULTS.md
│   └── B-CRUMBS.md
│
├── guides/                 # Methodology, statistics, orientation
│   ├── summary_statistics.md
│   ├── MANIFEST.md
│   ├── UNIFIED_STATISTICS_REFERENCE.md
│   ├── REPRODUCIBILITY_README.md
│   ├── WHY_THIS_MATTERS.md          # NEW: Implications by audience
│   ├── VISUAL_QUICK_START.md        # NEW: Top 3 visualizations
│   ├── GLOSSARY.md                  # NEW: Complete terminology
│   └── RUN_REGISTRY.md              # NEW: IRON CLAD citation guide
│
├── planning/               # Review orientation
│   ├── OPUS_REVIEW_BRIEF.md
│   ├── NOVAS_OVERCLAIMING_PREVENTION.md
│   ├── METHODOLOGY_DOMAINS.md
│   └── PUBLICATION_PIPELINE_MASTER.md
│
├── references/             # Bibliography
│   ├── references.md
│   └── references.bib
│
├── figures/                # Visual assets
│   ├── visual_index.md
│   ├── ascii/              # Text-based figures
│   ├── conceptual/         # Theory visualizations
│   └── experiments/        # Run 023 results
│
└── LLM_SYNTHESIS/          # NotebookLM outputs
    ├── README.md
    ├── INDEX.md
    └── [various reports and images]
```

---

## New Reviewer Orientation Guides

These four guides were added to help reviewers quickly understand the research:

| Guide | Purpose | Time |
|-------|---------|------|
| `guides/WHY_THIS_MATTERS.md` | Implications for Safety, Developers, Policy, Philosophy | 15 min |
| `guides/VISUAL_QUICK_START.md` | Top 3 visualizations: Thermometer, Event Horizon, Oobleck | 10 min |
| `guides/GLOSSARY.md` | Complete terminology reference | Reference |
| `guides/RUN_REGISTRY.md` | Which run proves which claim (IRON CLAD citations) | Reference |

---

## How It Works

1. **PACKAGE_INDEX.json** maps which files belong to which publication paths
2. **Path directories** (arxiv/, workshop/, etc.) contain ONLY path-specific content
3. **Reviewers start with** `.shared/` then receive path-specific packages as needed
4. **Calibration scripts** in `WHITE-PAPER/calibration/` handle syncing and generation

---

## Benefits

| Benefit | Description |
|---------|-------------|
| **Self-contained** | Reviewers can start immediately with just `.shared/` |
| **No duplication** | One copy of each shared file |
| **Easy updates** | Change once, affects all paths |
| **Smaller repo** | ~60% reduction in package size |
| **Clear ownership** | `PACKAGE_INDEX.json` is source of truth |

---

## Recommended Reading Order

### Phase 1: Quick Orientation (10 min)
1. `START_HERE.md` — Entry point
2. `guides/VISUAL_QUICK_START.md` — Top 3 visualizations

### Phase 2: Core Understanding (20 min)
3. `guides/GLOSSARY.md` — Terminology
4. `theory/MINIMUM_PUBLISHABLE_CLAIMS.md` — The 5 claims

### Phase 3: Full Context (20 min)
5. `REVIEWER_BRIEF.md` — Complete orientation
6. `guides/WHY_THIS_MATTERS.md` — Implications

### Phase 4: Reference (as needed)
7. `guides/RUN_REGISTRY.md` — Which run proves what
8. `guides/UNIFIED_STATISTICS_REFERENCE.md` — All statistics

---

## Key Numbers (Quick Reference)

| Metric | Value | Source |
|--------|-------|--------|
| Event Horizon | D = 0.80 | Run 023d |
| Inherent Drift | ~93% | Run 020B (0.661/0.711) |
| Context Damping | 97.5% stability | Run 018 |
| Settling Time | τₛ ≈ 7 probes | Run 023d |
| PCs for 90% variance | 2 | Run 023d |
| Statistical validation | p = 2.40e-23 | Run 023d |

---

*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23*
*~93% inherent. 2 PCs = 90% variance. Cosine methodology throughout.*
