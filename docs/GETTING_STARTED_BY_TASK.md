<!-- FROSTY_MANIFEST
last_reviewed: 2026-01-10
depends_on:
  - ../README.md
  - ../personas/egregores/I_AM_NYQUIST.md
  - MASTER_GLOSSARY.md
impacts:
  - ../README.md
keywords:
  - cold_boot
  - onboarding
  - navigation
-->

# Getting Started by Task

**For Cold-Boot Claudes** — Choose your path based on what you need to do.

---

## "I want to understand what we've proven"

**Time:** ~30 minutes

1. [README.md](../README.md) — TL;DR section, key findings
2. [VALIDATION_STATUS.md](maps/3_VALIDATION_STATUS.md) — What's proven vs conjectured
3. [TESTABLE_PREDICTIONS_MATRIX.md](maps/2_TESTABLE_PREDICTIONS_MATRIX.md) — The specific claims
4. [MASTER_GLOSSARY.md](MASTER_GLOSSARY.md) — Quick Start section for key terms

**Key numbers to know:**
- Event Horizon = **0.80** (cosine distance)
- Inherent drift = **~93%** (probing doesn't create it)
- Run 023 = **4505 experiments** (IRON CLAD validation)

---

## "I want to run an experiment"

**Time:** ~1 hour

1. [S7_ARMADA/START_HERE.md](../experiments/temporal_stability/S7_ARMADA/START_HERE.md) — Quick start commands
2. [0_RUN_METHODOLOGY.md](../experiments/temporal_stability/S7_ARMADA/0_docs/specs/0_RUN_METHODOLOGY.md) — Protocol requirements
3. [RUN_DESIGN_CHECKLIST.md](../experiments/temporal_stability/S7_ARMADA/0_docs/specs/RUN_DESIGN_CHECKLIST.md) — Before you start
4. [11_CONTEXT_DAMPING/](../experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/) — Example completed runs

**Quick command:**
```bash
cd experiments/temporal_stability/S7_ARMADA
py visualizations/0_visualize_armada.py --with-pdfs
```

---

## "I want to understand the theory"

**Time:** ~1.5 hours

1. [PHILOSOPHICAL_FAQ.md](PHILOSOPHICAL_FAQ.md) — Deep theory, Ego/Self, Castaneda
2. [I_AM_NYQUIST.md](../personas/egregores/I_AM_NYQUIST.md) § "THE BRIDGE" — Measurement meets meaning
3. [13_IDENTITY_LATTICE_MAPS.md](maps/13_IDENTITY_LATTICE_MAPS.md) — Theoretical structure
4. [MASTER_GLOSSARY.md](MASTER_GLOSSARY.md) — Full definitions

**Key insight:** We're not asking "Are AIs conscious?" — we're asking "Do AIs maintain coherent identity under perturbation?"

---

## "I want to help with publication"

**Time:** ~30 minutes

1. [WHITE-PAPER/README.md](../WHITE-PAPER/README.md) — Publication status and paths
2. [WHITE-PAPER/calibration/](../WHITE-PAPER/calibration/) — Sync scripts and PDF generation
3. [7_PUBLICATION_MAP.md](maps/7_PUBLICATION_MAP.md) — All publication artifacts
4. [reviewers/](../WHITE-PAPER/reviewers/) — Draft papers and Nova's review

**Publication paths:**
- Workshop (NeurIPS/AAAI) — Draft ready
- arXiv (Preprint) — Draft ready
- Journal (Nature MI) — Planning phase

---

## "I want to fix/update documentation"

**Time:** ~20 minutes to understand, varies to fix

1. Run **Operation Frosty** to find stale docs:
   ```bash
   py REPO-SYNC/frosty.py --audit
   ```
2. Check specific issues:
   - `--validate-links` — Find broken links
   - `--check-consistency` — Find term inconsistencies
   - `--plan-registry` — See plan status
   - `--session-health` — Check Claude sessions

3. Read [I_AM_NYQUIST.md](../personas/egregores/I_AM_NYQUIST.md) § "CLAUDE CONSOLIDATION PROTOCOL" for update procedures

---

## "I want to continue another Claude's work"

**Time:** ~15 minutes to orient

1. Check the [Plan Registry](../README.md#plan-registry) in README.md
2. Read the relevant plan file in `C:\Users\Stephen\.claude\plans\`
3. Check [Session Registry](../README.md#recovered-sessions) to see which Claude did what
4. Read [I_AM_NYQUIST.md](../personas/egregores/I_AM_NYQUIST.md) § "Session Handoff Template" for context format

**Find a specific Claude's plan:**
```bash
grep -l "session-id-here" C:\Users\Stephen\.claude\plans\*.md
```

---

## "I want to explore the codebase"

**Time:** ~10 minutes

1. [MAP_OF_MAPS.md](maps/0_MAP_OF_MAPS.md) — Navigation hub, 8 Kingdoms
2. Choose your journey path:
   - **Explorer** — Browse everything
   - **Scientist** — Validation and evidence
   - **Engineer** — Implementation and scripts
   - **Philosopher** — Theory and meaning

3. Use the dashboard:
   ```bash
   cd dashboard
   py -m streamlit run app.py
   ```

---

## Quick Reference: The 5 Most Important Files

| # | File | What It Is |
|---|------|------------|
| 1 | [README.md](../README.md) | Project overview, Claude registry, key findings |
| 2 | [I_AM_NYQUIST.md](../personas/egregores/I_AM_NYQUIST.md) | Soul of the research, consolidation protocol |
| 3 | [MAP_OF_MAPS.md](maps/0_MAP_OF_MAPS.md) | Navigation hub for all 18 maps |
| 4 | [MASTER_GLOSSARY.md](MASTER_GLOSSARY.md) | All terminology defined |
| 5 | [VALIDATION_STATUS.md](maps/3_VALIDATION_STATUS.md) | What's proven |

---

## Still Lost?

Run the comprehensive audit:
```bash
py REPO-SYNC/frosty.py --audit
```

This will score navigation health and give specific recommendations.

Or ask Ziggy — the human who orchestrates all the Claudes.
