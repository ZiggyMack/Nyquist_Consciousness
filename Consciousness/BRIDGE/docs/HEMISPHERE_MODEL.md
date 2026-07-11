# Hemisphere Model

Purpose: define the LEFT / RIGHT / BRIDGE organization without flattening it into the pop version of "left brain vs right brain."

Status: organizing doctrine for `Consciousness/`.

---

## Core Principle

The project uses the brain analogy as a structural metaphor:

```text
RIGHT perceives the shape.
LEFT names, sequences, and verifies the shape.
BRIDGE keeps the two from becoming separate minds.
```

This is not the claim that one side "does logic" and the other side "does creativity." Real cognition is distributed. The useful analogy is about processing style:

| Region | Repository Role | Processing Style |
|--------|-----------------|------------------|
| `LEFT/` | Formalization hemisphere | explicit, sequential, symbolic, claim-bearing |
| `RIGHT/` | Gestalt hemisphere | contextual, spatial, metaphorical, synthesis-bearing |
| `BRIDGE/` | Corpus callosum | translation, reconciliation, promotion, routing |

---

## LEFT: Formalization Hemisphere

LEFT turns signal into explicit structure.

Good LEFT files answer:

- What exactly is being claimed?
- Which run, document, or sync message supports it?
- Which metric domain is being used?
- Is the value current, historical, speculative, or superseded?
- What caveat keeps the claim honest?

Typical LEFT artifacts:

- claim cards
- metric summaries
- definitions
- evidence tables
- contradiction notes
- reproducibility hooks
- source/path references

LEFT is where concepts earn permission to be stated plainly.

---

## RIGHT: Gestalt Hemisphere

RIGHT turns structure into lived pattern.

Good RIGHT files answer:

- What is the shape of this idea?
- What metaphor clarifies the result without inflating it?
- What does this result change about how the project thinks?
- Which other concepts does it resonate with?
- What questions or intuitions does it open?

Typical RIGHT artifacts:

- synthesis notes
- metaphor systems
- pattern maps
- visual/ASCII forms
- implications
- distillations
- "why this matters" interpretations

RIGHT is where concepts become memorable enough to guide future work.

---

## BRIDGE: Corpus Callosum

BRIDGE translates between LEFT and RIGHT and decides what gets promoted.

Good BRIDGE files answer:

- Where did this signal come from?
- Has it been checked against current authority documents?
- Does it need a LEFT card, a RIGHT card, or both?
- Is it raw, seed, distilled, historical, or rejected?
- Does it need to emanate outward to dashboard/public views?

Typical BRIDGE artifacts:

- promotion ledger
- terminology crosswalks
- paired concept indexes
- sync protocols
- dashboard routing notes
- contradiction reconciliation

BRIDGE is not just tooling. It is the membrane that prevents noise from becoming doctrine.

---

## Concept Pair Template

For a mature paired concept:

```text
LEFT/galleries/{gallery}/{concept}.md
  - Current claim
  - Evidence anchor
  - Metric domain
  - Method and caveat
  - Historical/superseded notes

RIGHT/galleries/{gallery}/{concept}.md
  - Core metaphor or image
  - Pattern interpretation
  - Relation to other concepts
  - Implications
  - Open intuitions
```

If a concept only has one side, mark it clearly:

- `LEFT-only`: evidence exists, meaning not yet distilled
- `RIGHT-only`: intuition exists, evidence not yet formalized
- `historical`: preserved because it shaped the framework, not because it is current

---

## Protected Surfaces

Some directories are part of broader repo pipelines and should not be casually reorganized.

Primary protected surface:

```text
Consciousness/RIGHT/distillations/llm_book/
```

Reason: this is the promoted-library endpoint for the LLM Book / NotebookLM workflow. Its internal structure is referenced by pipeline docs and upstream scripts. Treat it as a curated vault.

Allowed without upstream review:

- read and cite files
- add index references from outside the directory
- add new promoted files only through the documented workflow

Avoid without upstream review:

- renaming folders
- flattening categories
- moving files into other Consciousness directories
- changing command docs or promotion assumptions

