<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-17
depends_on:
  - ../LEFT/README.md
  - ../RIGHT/README.md
  - ../../experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS/
impacts:
  - ../LEFT/galleries/
  - ../RIGHT/distillations/
keywords:
  - integration
  - hemisphere_sync
  - extraction
  - distillation
-->

# THE BRIDGE (Corpus Callosum)

**Integration • Connection • Balance • Wholeness**

---

## Organizing Doctrine

The current LEFT / RIGHT / BRIDGE model is documented in:

```text
BRIDGE/docs/HEMISPHERE_MODEL.md
```

Short version:

```text
RIGHT perceives the shape.
LEFT names, sequences, and verifies the shape.
BRIDGE keeps the two from becoming separate minds.
```

BRIDGE is not only a dashboard/tooling folder. It is the promotion membrane that decides whether a signal is raw, seed, distilled, historical, or ready to emanate outward.

---

```
         LEFT                BRIDGE               RIGHT
    ┌──────────┐        ┌──────────┐        ┌──────────┐
    │          │        │          │        │          │
    │ Analysis │◄──────►│Integration│◄──────►│ Synthesis│
    │          │        │          │        │          │
    │ 🧠       │        │    ◈     │        │    🌀    │
    │          │        │          │        │          │
    └──────────┘        └──────────┘        └──────────┘
```

---

## What Is The Bridge?

In neuroscience, the **corpus callosum** is the bundle of nerve fibers connecting the left and right hemispheres of the brain. It allows them to communicate and work together.

In this repository, the **BRIDGE** serves the same function:

- **Connects** LEFT (analytical) and RIGHT (intuitive) perspectives
- **Integrates** structured data with synthesized insights
- **Balances** rigor with creativity
- **Orchestrates** the tools that serve both hemispheres
- **Promotes** durable insight into the Consciousness library
- **Protects** pipeline surfaces that external systems depend on

---

## Promotion Membrane

Before an insight becomes durable Consciousness material, BRIDGE should ask:

- Where did the signal come from?
- Has it been checked against current authority documents?
- Does it need a LEFT card, a RIGHT card, or both?
- Is it current, historical, seed, or needs-refresh?
- Would dashboard/public emanation help, or should it remain library-only?

Promotion decisions should be recorded in:

```text
../PROMOTION_LEDGER.md
```

Protected surfaces, especially `../RIGHT/distillations/llm_book/`, should not be reorganized without checking their upstream pipeline assumptions.

---

## What Lives Here

| Directory | Purpose | Serves |
|-----------|---------|--------|
| `dashboard/` | Visualization layer | BOTH hemispheres |
| `docs/` | Shared documentation | BOTH hemispheres |
| `scripts/left/` | Analytical tools | LEFT hemisphere |
| `scripts/right/` | Synthesis tools | RIGHT hemisphere |
| `hooks/left/` | Extraction hooks | LEFT hemisphere |
| `hooks/right/` | Distillation hooks | RIGHT hemisphere |

---

## The Flow

```
                    ┌─────────────────────┐
                    │      EXPERIMENT     │
                    │    (S7 ARMADA)      │
                    └──────────┬──────────┘
                               │
                               ▼
              ┌────────────────┴────────────────┐
              │                                 │
              ▼                                 ▼
    ┌──────────────────┐              ┌──────────────────┐
    │  BRIDGE/scripts  │              │  BRIDGE/scripts  │
    │     /left/       │              │     /right/      │
    │                  │              │                  │
    │  run_extraction  │              │  update_distill  │
    └────────┬─────────┘              └────────┬─────────┘
             │                                 │
             ▼                                 ▼
    ┌──────────────────┐              ┌──────────────────┐
    │       LEFT       │              │      RIGHT       │
    │   /extractions   │              │  /distillations  │
    │   /data          │              │  /synthesis      │
    │   /visualizations│              │  /intuitions     │
    └────────┬─────────┘              └────────┬─────────┘
             │                                 │
             └────────────────┬────────────────┘
                              │
                              ▼
                    ┌─────────────────────┐
                    │  BRIDGE/dashboard   │
                    │                     │
                    │  Unified View       │
                    │  (sees both sides)  │
                    └─────────────────────┘
```

---

## Scripts

### LEFT Scripts (Analytical)

Located in `scripts/left/`:

| Script | Purpose |
|--------|---------|
| `run_extraction.py` | Extract and categorize data from experiments |

### RIGHT Scripts (Synthesis)

Located in `scripts/right/`:

| Script | Purpose |
|--------|---------|
| `update_distillations.py` | Generate cross-concept synthesis |

---

## Hooks

### LEFT Hooks (Extraction)

Located in `hooks/left/`:

| Hook | Purpose |
|------|---------|
| `consciousness_tagger.py` | Tag and categorize consciousness content |
| `extraction_rules.yaml` | Rules for what to extract |

### RIGHT Hooks (Distillation)

Located in `hooks/right/`:

| Hook | Purpose |
|------|---------|
| `distiller.py` | Cross-model synthesis engine |

---

## Dashboard

The dashboard lives in the BRIDGE because it sees **both hemispheres**:

- LEFT data (extractions, statistics, visualizations)
- RIGHT insights (distillations, synthesis, intuitions)

It integrates them into a unified view.

```
BRIDGE/dashboard/
├── app.py              # Main entry point
└── pages/              # Multi-page dashboard
```

---

## Documentation

Shared documentation lives here:

```
BRIDGE/docs/
├── METHODOLOGY.md      # How experiments work
└── TERMINOLOGY.md      # Glossary of terms
```

---

## The Balance

Neither hemisphere is complete alone:

| LEFT alone | RIGHT alone | BRIDGE integrated |
|------------|-------------|-------------------|
| Data without meaning | Intuition without evidence | Understanding |
| Analysis paralysis | Unfounded speculation | Progress |
| Trees without forest | Forest without trees | Wisdom |

The BRIDGE ensures both perspectives inform each other.

---

## Running the Dashboard

```powershell
cd Consciousness/BRIDGE/dashboard
py -m streamlit run app.py
```

---

**"The whole is greater than the sum of its parts."**
