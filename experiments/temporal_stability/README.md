<!-- FROSTY_MANIFEST
last_reviewed: 2026-07-15
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
  - temporal_stability
  - armada
  - cfa_trinity
-->
# Temporal Stability Experiments (S7)

**Testing whether AI identity behaves as a dynamical system with measurable attractor basins, critical thresholds, and recovery dynamics consistent across architectures.**

**Last Updated:** 2026-07-15

---

## What's Here

```text
temporal_stability/
├── S7_ARMADA/             ← THE ACTIVE WORK (all current experiments)
│   ├── README.md          ← Theory, key concepts, directory map, run history
│   ├── START_HERE.md      ← Operations guide (how to run experiments)
│   ├── 1_CALIBRATION/     ← CLAL.py fleet calibration (78 ships)
│   ├── 2-10_*/            ← Legacy search-type experiments (Runs 006-016)
│   ├── 11_CONTEXT_DAMPING/  ← Phase 4 experiments (Runs 017-020)
│   ├── 12_CFA/            ← CFA Trinity adversarial audit (702+ runs)
│   ├── 13_LOGOS/           ← LOGOS Commutation Cartography (Run 022)
│   ├── 14_CONSCIOUSNESS/   ← Gold/Diamond/Quartz Rush mining
│   ├── 15_IRON_CLAD_FOUNDATION/  ← Run 023 (4505 experiments)
│   ├── 0_docs/             ← Summaries, specs, analysis
│   ├── 0_results/          ← Consolidated JSON results + manifests
│   └── visualizations/     ← Charts, plots, PDF summaries
│
├── .env                   ← API keys (NEVER commit — single source of truth)
├── requirements.txt       ← Python dependencies for all S7 work
└── OUTPUT/                ← Meta-loop results (Runs 001-005, legacy)
```

**Start here:** [`S7_ARMADA/README.md`](S7_ARMADA/README.md) for theory and concepts, [`S7_ARMADA/START_HERE.md`](S7_ARMADA/START_HERE.md) for operations.

---

## Quick Start

```powershell
# Install dependencies
cd experiments/temporal_stability
py -m pip install -r requirements.txt

# Then navigate into the ARMADA
cd S7_ARMADA
```

Everything runs from inside `S7_ARMADA/`. This parent directory holds the shared `requirements.txt` and `.env`.

---

## Two Paradigms

| Paradigm | Era | What It Does |
|----------|-----|-------------|
| **META-LOOP** (Legacy) | Runs 001-005 | Deep single-model testing with adaptive curriculum. Results in `OUTPUT/`. **Superseded.** |
| **ARMADA** (Active) | Runs 006-present | Wide cross-architecture mapping — 78-ship fleet across 5 providers. All current work. |

---

## Key Validated Findings

| Finding | Evidence |
|---------|----------|
| **Event Horizon at 0.80** | p=2.40e-23 (Run 023 perturbation, cosine distance) |
| **~93% drift is INHERENT** | Run 020B: probing reveals pre-existing drift, doesn't create it |
| **PFI measures identity** | d=0.977, ρ=0.91 embedding invariance across 3 models |
| **Recovery is natural** | 100% manifold return (Platonic Coordinates, Run 014) |

---

## API Keys

**Single source of truth:** `.env` in this directory.

```bash
ANTHROPIC_API_KEY=sk-ant-...   # Claude fleet
OPENAI_API_KEY=sk-...          # GPT fleet + embeddings
XAI_API_KEY=xai-...            # Grok fleet
GOOGLE_API_KEY=...             # Gemini fleet
TOGETHER_API_KEY=...           # Together.ai fleet (29 ships)
```

**NEVER commit this file.** It is gitignored. If you need to regenerate keys, see the provider dashboards. All experiment scripts load from this `.env` via `python-dotenv`.

---

*Last Updated: July 15, 2026*
