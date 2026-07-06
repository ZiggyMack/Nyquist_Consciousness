# Cognitive Archaeology Map

**Purpose:** Navigate the Cognitive Archaeology research program — the systematic excavation of reasoning operators across independent thinkers.

**Status:** Infrastructure complete. Phase 0 (Extractor Calibration) queued. No real dig sites beyond 001 yet.

**Location:** `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/`

---

## The Territory

```
                         ┌──────────────────────────────────┐
                         │        THE CORE QUESTION          │
                         │                                    │
                         │  Is there a finite grammar of      │
                         │  reasoning operators?               │
                         │                                    │
                         │  Or is reasoning irreducibly        │
                         │  context-dependent?                 │
                         │                                    │
                         │  (Motivating metaphor: "a periodic │
                         │   table of reasoning itself")      │
                         └───────────────┬──────────────────┘
                                         │
            ┌────────────────────────────┼────────────────────────────┐
            │                            │                            │
            ▼                            ▼                            ▼
  ┌──────────────────┐     ┌──────────────────┐     ┌──────────────────┐
  │   EXCAVATION     │     │   VALIDATION     │     │   GOVERNANCE     │
  │                  │     │                  │     │                  │
  │ DIG_SITES/       │     │ MUSEUM/          │     │ LEDGER.md        │
  │ TEMPLATES/       │     │  INDEX.md        │     │ FIELD_MANUAL.md  │
  │ NOTEBOOKLM_      │     │  GRAPH.md        │     │ README.md        │
  │ PROMPTS.md       │     │  RETIRED.md      │     │                  │
  │                  │     │  operators/       │     │ Promotion Gates  │
  │ "Recover the     │     │                  │     │ Falsification    │
  │  operators"      │     │ "Catalogue and   │     │ Anti-Reification │
  │                  │     │  predict"        │     │                  │
  └──────────────────┘     └──────────────────┘     └──────────────────┘
```

---

## The Scientific Method

```
  Phase 0                      The Core Pipeline
  ─────────                    ───────────────────────────────────────

  EXTRACTOR          OBSERVE ──► EXCAVATE ──► ADMIT ──► CROSS-SITE
  CALIBRATION           │                                    │
  (Dig Site 000)        │                                    ▼
       │                │         PRESSURE ◄── ASSIGN ◄── RECOVER
       │                │         TEST         CONFIDENCE
       │                │            │
       ▼                │            ▼
  "Who is               │         PREDICT ──► FUNDAMENTAL?
   excavating?"         │
                        │         Operators either survive
  Must pass before      │         this process or they don't.
  any real dig site     │
```

---

## The Core Confound

```
╔════════════════════════════════════════════════════════════════════╗
║                                                                    ║
║   "Can you separate operators that are in the thinkers             ║
║    from operators that are in the reader?"                          ║
║                                                                    ║
║                                        — Opus (EOS Methodologist)  ║
║                                                                    ║
║   This is the instrument-vs-object problem.                        ║
║   Phase 0 exists to address it.                                    ║
║                                                                    ║
╚════════════════════════════════════════════════════════════════════╝
```

---

## The Operator Museum (Current State)

```
   CONFIDENCE LEVELS
   ─────────────────
   STAR  Fundamental    0 operators    (requires irreducibility + predicted absence)
   GREEN Confirmed      0 operators    (requires extractor-independence + discrimination)
   YELLOW Candidate     3 operators    OP-001, OP-004, OP-007
   RED   Hypothesis     4 operators    OP-002, OP-003, OP-005, OP-006

   All 7 operators: Ext-Indep = Unknown (all extracted by Claude only)

   OPERATOR HIERARCHY
   ──────────────────
   OP-006: Under-Determination Detection       (most general)
     ├── OP-001: Representation ≠ Ontology
     ├── OP-002: Hidden Selection Audit
     └── OP-005: Hidden Structure Injection

   OP-004: Reconstruction Before Judgment
     └── OP-003: Goal → Optimization Collapse   (requires OP-004)

   OP-007: Locate Disagreement Layer            (cross-cutting)
```

---

## The Failure Atlas

Each operator, when absent, produces a named cognitive failure:

```
   ABSENT OPERATOR                    NAMED FAILURE
   ────────────────                   ──────────────
   OP-001  Rep ≠ Ontology       ──►  Reification
   OP-002  Hidden Selection     ──►  Selection Blindness
   OP-003  Goal → Optimization  ──►  Optimization Drift
   OP-004  Reconstruction       ──►  Strawman
   OP-005  Hidden Structure     ──►  Invisible Import
   OP-006  Under-Determination  ──►  Determination Illusion
   OP-007  Locate Disagreement  ──►  Layer Confusion

   Bidirectional: failure ──► absent operator ──► failure
```

---

## Dig Sites

```
   SITE    TARGET                STATUS          RESULT
   ────    ──────                ──────          ──────
   000     Extractor Calibration QUEUED          Phase 0 (instrument calibration)
   001     Adlam & Barandes      DONE            6 new operators, 0 rediscoveries
   002     Pearl                 NOT STARTED     First genuine test of the theory
   003     Dennett               NOT STARTED
   004     Jaynes                NOT STARTED
   ...     (11 thinkers total)
```

---

## Promotion Gates

```
   RED ──────────────────────────────────────────────────────► YELLOW
   Gate: Two extractors see the same thing.
   Rules out: "stylistic tic in one extraction"

   YELLOW ───────────────────────────────────────────────────► GREEN
   Gate: 3+ extractors agree + cross-thinker recurrence
         + differential presence + blind prediction
   Rules out: "artifact of extractor" + "present everywhere"

   GREEN ────────────────────────────────────────────────────► STAR
   Gate: Cross-domain transfer + failure prediction
         + irreducibility + survived falsification attempt
   Rules out: "molecule not atom" + "no consequences"
```

---

## Falsification Criteria

The program is killed or demoted to "descriptive hobby" if:

```
   1. Extractor-independence fails      ──►  Instrument is the finding
   2. Negative controls light up        ──►  Extraction generates, not detects
   3. Operators universally present     ──►  Rorschach test, not grammar
   4. Granularity-dependent             ──►  Overfit to chosen decomposition
   5. No blind predictive success       ──►  Filing system, not theory
```

---

## The Team (emergent specialization)

```
   ROLE                  AGENT           QUESTION
   ────                  ─────           ────────
   Curator               Repo Claude     "How do we preserve this?"
   Experimentalist       CFA Claude      "Does this survive adversarial evaluation?"
   Methodologist         EOS Opus        "Would this convince a skeptical community?"
   Synthesist            Nova            "Are these the same deeper operation?"
   Field Archaeologist   Ziggy           "What's interesting? What connects?"
```

---

## Key Principles

| Principle | Source | What It Means |
|-----------|--------|---------------|
| First Law | Nova | Independent convergence > isolated brilliance |
| Anti-Reification | Nova | Operators are hypotheses, not eternal entities |
| Second Law | Opus | A filing system is not a theory |
| Core Confound | Opus | Separate operators in thinkers from operators in reader |
| Excavation Norm | Nova | Excavate generously, classify conservatively |
| Blind Protocol | Nova | Don't show the Museum before digging |

---

## Success Criteria

```
   SIGNAL                              DIRECTION
   ──────                              ─────────
   Independent convergence             Increasing
   Predictive power                    Increasing
   Need for new operators              Decreasing
   Explanatory compression             Increasing
```

---

## Cross-References

| From CA | To Project | Relationship |
|---------|-----------|--------------|
| Operators | CFA | CFA is one application of the operators; CRUX = failure-mode evidence |
| Operators | FUT | FUT's rep→eval flow IS OP-001/OP-004 |
| Operators | DBEP | DBEP layer model IS OP-007 |
| Operators | EOS | EOS applies operators in institutional contexts |
| Museum | LLM_BOOK | NotebookLM as excavation tool, not summarizer |
| Phase 0 | CFA Identity | Same instrument-vs-object problem in different costume |
| Failure Atlas | CFA CRUX | Every CRUX maps to a Failure Atlas entry |

---

## File Index

```
   New_9_Cognitive_Archaeology/
   ├── README.md                                Core vision + falsification criteria
   ├── FIELD_MANUAL.md                          Workflow + admission criteria + norms
   ├── LEDGER.md                                Confidence tracking + promotion gates
   ├── DIG_SITES/
   │   ├── 000_Extractor_Calibration/           Phase 0 experiment design
   │   │   └── experiment_design.md
   │   └── 001_Adlam_Barandes/                  First excavation (seeded from New_8)
   │       └── excavation.md
   ├── MUSEUM/
   │   ├── INDEX.md                             Master operator list
   │   ├── GRAPH.md                             Relationships + Failure Atlas
   │   ├── RETIRED.md                           Failed/retired operators
   │   └── operators/                           Individual operator pages (7)
   └── TEMPLATES/
       ├── DIG_SITE_TEMPLATE.md
       ├── OPERATOR_TEMPLATE.md
       └── NOTEBOOKLM_PROMPTS.md
```

---

*Created: 2026-07-06*
*Map #19*
*Territory: The Grammar of Thought*
