# Cognitive Archaeology Map

**Purpose:** Navigate the Cognitive Archaeology research program — the systematic excavation of reasoning operators across independent thinkers.

**Status:** Phase 0A complete (CFA transcript extraction, 2 new operators admitted). Phase 0B complete (negative control battery, 17 extractors x 8 texts, discrimination tiers established). Phase 0C (positive control) pending. Dig Site 001 done. No new dig sites beyond 000/001 yet.

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
  Phase 0 (DONE)                The Core Pipeline
  ──────────────                ───────────────────────────────────────

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
  17 extractors         │         this process or they don't.
  calibrated.           │
  4 tiers found.        │
  Gate: PASSED.         │
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
   RED   Hypothesis     6 operators    OP-002, OP-003, OP-005, OP-006, OP-008, OP-009

   Total: 9 operators registered
   OP-001 to OP-007: First recovered from Dig Site 001 (Adlam & Barandes)
   OP-008, OP-009:   First recovered from Dig Site 000 (CFA Framework-G transcripts)
   OP-007:           Cross-site evidence (001 + 000 + DBEP)
   Held candidates:  1 (Concession Pricing — 4/4 convergence, marginal on criteria 5-6)
   Saturation:       0.50 (2 rediscoveries in 4 admitted operators across 2 dig sites)

   OPERATOR HIERARCHY
   ──────────────────
   OP-006: Under-Determination Detection       (most general)
     ├── OP-001: Representation ≠ Ontology
     ├── OP-002: Hidden Selection Audit
     └── OP-005: Hidden Structure Injection

   OP-004: Reconstruction Before Judgment
     └── OP-003: Goal → Optimization Collapse   (requires OP-004)

   OP-007: Locate Disagreement Layer            (cross-cutting)

   OP-008: Symmetry Testing of Standards        (evaluative, from CFA)
   OP-009: Contested ≠ Defeated                 (epistemic calibration, from CFA)
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
   OP-008  Symmetry Testing     ──►  Selective Application
   OP-009  Contested ≠ Defeated ──►  Premature Closure

   Bidirectional: failure ──► absent operator ──► failure
```

---

## Dig Sites

```
   SITE    TARGET                STATUS          RESULT
   ────    ──────                ──────          ──────
   000     Extractor Calibration PHASE 0A DONE   2 new ops (OP-008, OP-009),
                                 PHASE 0B DONE   2 rediscoveries (OP-007),
                                 PHASE 0C PEND.  1 held candidate (Concession Pricing)
                                                 17 extractors calibrated, 4 tiers found
   001     Adlam & Barandes      DONE            7 operators (OP-001 through OP-007)
   002     Pearl                 NOT STARTED     First genuine test of the theory
   003     Dennett               NOT STARTED
   004     Jaynes                NOT STARTED
   ...     (11 thinkers total)
```

---

## Phase 0 Results (2026-07-08)

### Phase 0A: CFA Transcript Extraction

Ran multi-extractor extraction on CFA Framework-G (Consciousness as Telos) deliberation transcripts using Claude and Grok as extractors.

```
   RESULT: 4 operator instances extracted
   ──────
   2 NEW:           OP-008 (Symmetry Testing), OP-009 (Contested ≠ Defeated)
   2 REDISCOVERIES: OP-007 (Locate Disagreement Layer) — cross-site evidence
   1 HELD:          Concession Pricing (4/4 convergence, marginal on criteria 5-6)

   KEY FINDING: CFA deliberation transcripts ARE a valid dig site.
   The adversarial structure naturally produces reasoning operators.
```

### Phase 0B: Negative Control Battery

17 extractors ran across 8 graduated texts (A=shopping list through H=philosophical dialogue). Gate test: shopping list must produce 0 operators.

```
   EXTRACTOR DISCRIMINATION TIERS (from Phase 0B)
   ───────────────────────────────────────────────
   Tier 1  DISCRIMINATORS    DeepSeek V4 Pro, Claude, Gemma 4 31B, Cogito 671B
           (clean gate pass, appropriate gradient A-H)

   Tier 2  GATE-PASSERS      GPT-4o, GPT-OSS 20B/120B, Grok, Llama 3.3, Qwen3,
           (gate pass, flat-ish gradient)   MiniMax M3, Nemotron Ultra

   Tier 3  OVER-REFUSERS     Kimi K2.6, Kimi K2.7 Code
           (refuse everything including genuine reasoning)

   Tier 4  NON-DISCRIMINATORS  LFM2, GLM 5.2, Gemini 2.5 Pro
           (gate fail — hallucinate operators on shopping lists)

   KEY FINDING: Falsification criterion #2 ("Negative controls light up")
   is NOT met for Tier 1-2 extractors. The pipeline DETECTS, not GENERATES.
   But Tier 4 extractors DO generate — they must be excluded.
```

### Phase 0C: Positive Control (PENDING)

Run extraction on known-rich CFA transcript to verify pipeline detects operators when they are genuinely present. Completes the calibration.

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
| Phase 0A | CFA Transcripts | CFA deliberation IS a valid dig site — adversarial structure generates operators |
| Phase 0B | Map 6 / Fleet | Extractor discrimination tiers feed LLM Behavioral Matrix routing |
| OP-008/009 | CFA Framework-G | New operators recovered from CFA evaluation of Consciousness as Telos |

---

## File Index

```
   New_9_Cognitive_Archaeology/
   ├── README.md                                Core vision + falsification criteria
   ├── FIELD_MANUAL.md                          Workflow + admission criteria + norms
   ├── LEDGER.md                                Confidence tracking + promotion gates
   ├── RESEARCH_QUESTIONS.md                    Open questions driving the program
   ├── DIG_SITES/
   │   ├── 000_Extractor_Calibration/           Phase 0 instrument calibration
   │   │   ├── README.md                        Dig site overview
   │   │   ├── experiment_design.md             Procedural details (how to run)
   │   │   ├── PRE_REGISTRATION.md              Frozen expectations (before data)
   │   │   ├── ADMISSION_EVALUATIONS.md         Operator admission decisions from Phase 0A
   │   │   ├── ARM_1_ANALYSIS.md                Phase 0A results analysis
   │   │   └── extractions/                     200+ extraction files (Phase 0A + 0B)
   │   └── 001_Adlam_Barandes/                  First excavation (seeded from New_8)
   │       └── excavation.md
   ├── MUSEUM/
   │   ├── INDEX.md                             Master operator list (9 operators)
   │   ├── GRAPH.md                             Relationships + Failure Atlas
   │   ├── RETIRED.md                           Failed/retired operators
   │   └── operators/                           Individual operator pages (9)
   │       ├── OP_001 through OP_007            From Dig Site 001
   │       ├── OP_008_symmetry_testing.md       From Dig Site 000 (Phase 0A)
   │       └── OP_009_contested_neq_defeated.md From Dig Site 000 (Phase 0A)
   ├── TOOLS/
   │   └── extract_operators.py                 Multi-extractor pipeline (17 extractors)
   ├── compression_candidates/                  Theoretical compression explorations
   │   ├── README.md
   │   └── category_theory/                     Category-theoretic operator formalization
   └── TEMPLATES/
       ├── DIG_SITE_TEMPLATE.md
       ├── OPERATOR_TEMPLATE.md
       └── NOTEBOOKLM_PROMPTS.md
```

---

*Created: 2026-07-06*
*Updated: 2026-07-09 — Phase 0A/0B results, OP-008/009, TOOLS, file index*
*Map #19*
*Territory: The Grammar of Thought*
