# Cognitive Archaeology Map

**Purpose:** Navigate the Cognitive Archaeology research program — the systematic excavation of reasoning operators across independent thinkers, and the discovery of reusable architectures that compose those operators into entire discovery engines.

**Status:** Phase 0 COMPLETE (0A/0B/0C all passed). Empirical arm UNBLOCKED. Theoretical arm running in parallel via LLM Book deep digs. Dig Sites 001, 002, 010 complete. Museum A: 15 operators (7 YELLOW, 8 RED). Museum B: 6 architectures (1 confirmed, 5 candidates). Discovery Simplex hypothesized.

**Last reconciled against Mission Control:** 2026-07-10

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
                         │  And do they compose into a        │
                         │  finite set of discovery           │
                         │  architectures?                    │
                         │                                    │
                         └───────────────┬──────────────────┘
                                         │
            ┌────────────────────────────┼────────────────────────────┐
            │                            │                            │
            ▼                            ▼                            ▼
  ┌──────────────────┐     ┌──────────────────┐     ┌──────────────────┐
  │   EXCAVATION     │     │   MUSEUM A       │     │   MUSEUM B       │
  │                  │     │   (Operators)    │     │   (Architectures)│
  │ DIG_SITES/       │     │                  │     │                  │
  │ TEMPLATES/       │     │ INDEX.md         │     │ DISCOVERY_       │
  │ NOTEBOOKLM_     │     │ GRAPH.md         │     │ ARCHITECTURES.md │
  │ PROMPTS.md       │     │ operators/       │     │                  │
  │                  │     │                  │     │ "How do operators │
  │ "Recover the     │     │ "Catalogue and   │     │  compose into    │
  │  operators"      │     │  predict"        │     │  discovery       │
  │                  │     │                  │     │  engines?"       │
  └──────────────────┘     └──────────────────┘     └──────────────────┘
            │                            │                            │
            └────────────────────────────┼────────────────────────────┘
                                         │
                                         ▼
                              ┌──────────────────┐
                              │   GOVERNANCE     │
                              │                  │
                              │ LEDGER.md        │
                              │ FIELD_MANUAL.md  │
                              │ README.md        │
                              │                  │
                              │ Promotion Gates  │
                              │ Falsification    │
                              │ Anti-Reification │
                              └──────────────────┘
```

---

## The Two Museums

| | Museum A | Museum B |
|---|---|---|
| **Name** | Museum of Cognitive Operators | Museum of Discovery Architectures |
| **Contents** | Individual reasoning moves | Entire discovery engines |
| **Level** | Microscopic (atoms) | Macroscopic (molecules) |
| **Analogy** | Verbs | Grammars |
| **Document** | `MUSEUM/INDEX.md` | `DISCOVERY_ARCHITECTURES.md` |
| **Admission** | 6 criteria (FIELD_MANUAL) | 4 criteria (named composition, multiple instances, predictive, discriminative) |
| **Current** | 15 operators (7Y, 8R) | 1 confirmed (RCI) + 5 candidates (B-F) |

Operators compose into architectures. Architectures compose into scientific traditions.

---

## The Scientific Method

```
  EMPIRICAL ARM (Phase 0)        The Core Pipeline
  ──────────────────────         ───────────────────────────────────────

  EXTRACTOR          OBSERVE ──► EXCAVATE ──► ADMIT ──► CROSS-SITE
  CALIBRATION           │                                    │
  (Dig Site 000)        │                                    ▼
       │                │         PRESSURE ◄── ASSIGN ◄── RECOVER
       │                │         TEST         CONFIDENCE
       │                │            │
       ▼                │            ▼
  0A: Who extracts?     │         PREDICT ──► FUNDAMENTAL?
  0B: What's noise?     │
  0C: What's signal?    │         Operators either survive
      ✅ ALL COMPLETE    │         this process or they don't.
                        │
  THEORETICAL ARM       │
  ─────────────────     │
  LLM Book Deep Digs    │
  (Nova + NotebookLM)   │
       │                │
       ▼                │
  ARCHITECTURE          │
  DISCOVERY             │
  (cross-pollination    │
   back to Museum B)    │
```

**Phase 0C is COMPLETE (2026-07-10).** The empirical arm is UNBLOCKED. Systematic excavation can proceed.

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

## The Operator Museum (Museum A — Current State)

```
   CONFIDENCE LEVELS                          (source: MUSEUM/INDEX.md)
   ─────────────────
   STAR  Fundamental    0 operators    (requires irreducibility + predicted absence)
   GREEN Confirmed      0 operators    (requires extractor-independence + discrimination)
   YELLOW Candidate     7 operators    OP-001, OP-004, OP-007, OP-010, OP-011, OP-012, OP-013
   RED   Hypothesis     8 operators    OP-002, OP-003, OP-005, OP-006, OP-008, OP-009, OP-014, OP-015

   Total: 15 operators registered
   OP-001 to OP-007: First recovered from Dig Site 001 (Adlam & Barandes)
   OP-008, OP-009:   First recovered from Dig Site 000 (CFA Framework-G transcripts)
   OP-010 to OP-015: First recovered from Dig Site 002 (Barandes solo)
   OP-007:           Cross-site evidence (001 + 000 + DBEP)
   Held candidates:  1 (Concession Pricing — 4/4 convergence, marginal on criteria 5-6)
   Saturation:       5 rediscoveries across 3 dig sites (OP-001×1, OP-004×1, OP-006×1, OP-007×2)
   Families:         Translation, Information, Minimal Sufficiency, Blind Spot, Constraint-Induced Discovery
   GREEN candidates: OP-004, OP-008 (6/6 extractors in Phase 0A+0C, pending 2nd dig site)

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

   OP-010: Altitude Escalation                  (meta-level, from Dig Site 002)
   OP-011: Subtractive Discovery                (minimal sufficiency, from Dig Site 002)
   OP-012: Pedagogical Forcing                  (teaching as discovery, from Dig Site 002)
   OP-013: Epistemic Boundary Setting           (knowledge boundary, from Dig Site 002)
   OP-014: Ontological Downgrading              (graded reality, from Dig Site 002)
   OP-015: Question Completion                  (question generation, from Dig Site 002)
```

---

## Discovery Architectures (Museum B — Current State)

```
   CONFIRMED
   ─────────
   Architecture A: Reverse Constraint Inference (RCI)
     Composition: OP-001 → OP-011 → OP-006 → Noether Lens → RCI
     Algorithm:   Change representation → observe survivors → read backward → infer architecture
     Instances:   Noether, Barandes, Darwin, Shannon, EOS
     Simplex:     Constraint corner

   CANDIDATES
   ──────────
   Architecture B: Forward Mathematical Generation         (tests at Dig Site 003 / Dirac)
   Architecture C: Evolutionary Search                     (speculative — meta-architecture?)
   Architecture D: Compression-Driven Discovery            (speculative — related to RCI?)
   Architecture E: Adversarial Discovery                   (INSTANTIATED in CFA)
   Architecture F: Composition Analysis / Op-Validity      (extracted from Dig Site 010 / Curt)
     Algorithm:   Identify operation → recover validity conditions → vary domain → classify A/B/C
     Instances:   Curt, Arrow, Abramsky-Brandenburger, Efron
     Simplex:     Composition corner
```

---

## The Discovery Simplex (Post-Dig-Site-010)

Four orthogonal discovery questions — not competing theories:

```
              Transformation (Noether)
                  ▲
                  │
   Composition ◄──┼──► Generation (Dirac)
      (Curt)      │
                  ▼
             Constraint (Barandes)
```

| Corner | Question | Architecture | Status |
|--------|----------|--------------|--------|
| Transformation | What survives change? | (inside RCI) | Predicted |
| Constraint | What minimal architecture reproduces observations? | RCI (Arch A) | Confirmed |
| Composition | When is an operation licensed at scale? | Arch F | Confirmed |
| Generation | What structures deserve exploration before evidence? | Arch B | Tests at Dig Site 003 |

**Relation Space:** Architecture often lives in TRANSITIONS between nodes (transition functions, gluing data, relational structure), not in the nodes themselves. Confirmed across 5 projects:

| Project | What is relational |
|---------|-------------------|
| Barandes | Pair-dependent laws (A alone doesn't determine conditionals) |
| Curt | Transition functions (gluing data determines the global object) |
| CFA | Crux interactions (matchup produces structure neither framework has alone) |
| ARMADA | Calibration relationships (individual runs don't determine stable lever) |
| EOS | Operators compose into architectures (composition is where architecture lives) |

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
   OP-010  Altitude Escalation  ──►  Level Lock
   OP-011  Subtractive Discovery──►  Additive Bias
   OP-012  Pedagogical Forcing  ──►  Assumed Understanding
   OP-013  Epistemic Boundary   ──►  Boundary Blindness
   OP-014  Ontological Downgrade──►  Binary Ontology
   OP-015  Question Completion  ──►  Question Starvation

   Bidirectional: failure ──► absent operator ──► failure
```

---

## Dig Sites

```
   SITE    TARGET                STATUS              RESULT
   ────    ──────                ──────              ──────
   000     Extractor Calibration 0A/0B/0C ALL DONE    2 new ops (OP-008, OP-009),
                                                     2 rediscoveries (OP-007),
                                                     17 extractors, 4 tiers,
                                                     Gemma4 31B star performer
   001     Adlam & Barandes      DONE                7 operators (OP-001 to OP-007)
   002     Barandes (solo)       DONE                RCI architecture, 40 insights
   010     Curt Jaimungal        DONE (R1 + Audit)   Architecture F, Discovery Simplex,
                                                     Relation Space, Category Theory hyp.
   003     Dirac                 PLANNED (Q50 #1)    Tests Generation corner
   004     Wolfram               QUEUED (Q50 #2)     Computational/deterministic
   005     Hermann               QUEUED (Q50 #3)     Philosophical auditing
   006     Pearl                 QUEUED              Causal separation, convergence potential
   007     Dennett               QUEUED              Heterophenomenology, Nyquist link
   008     Jaynes                QUEUED              ISP lineage, MaxEnt
```

**Note:** From Dig Site 003 onward, the queue is driven by Q50 recursion — each excavation recommends the next targets ranked by expected operator yield.

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

### Phase 0C: Positive Control (COMPLETE — 2026-07-10)

Ran 4 Tier 1 extractors on the Framework-G v2.1 transcript (66,803 chars) — the same source used in Phase 0A, leveraging established ground truth.

```
   EXTRACTOR           OPERATORS   MUSEUM HITS                         MATCH
   ─────────           ─────────   ───────────                         ─────
   Claude (Sonnet 4-6) 11          OP-001, OP-004, OP-007, OP-008     91%
   DeepSeek V4 Pro     8           OP-001, OP-004, OP-008             100%
   Gemma4 31B ★        9           OP-004, OP-007, OP-008, OP-009     100%
   Cogito 671B         8           OP-004, OP-007, OP-008             100%

   ★ Gemma4 31B = star performer (all 4 museum entries recovered blind)
```

**Result:** Pipeline DETECTS when operators are present (0C), doesn't hallucinate them when absent (0B), and independent extractors agree (0A). Calibration triangle complete. **Empirical arm UNBLOCKED.**

**GREEN candidates:** OP-004 and OP-008 recovered by 6/6 independent extractors across 0A+0C. Pending 2nd dig site for formal promotion.

**Evidence:** `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/DIG_SITES/000_Extractor_Calibration/extractions/extraction_*_20260710_*.md`

---

## Dig Site 010 Results (2026-07-10)

### Key Contributions from Curt / "The Reverse Elephant"

**Architecture F (Composition Analysis / Operation-Validity Testing):**
- Every operation has a domain of validity
- Three failure modes are algebraic cases of a composition operator
- Algorithm: identify operation → recover validity conditions → vary domain → classify
- This is the architecture that AUDITS other architectures

**The Discovery Simplex:**
- Four orthogonal discovery questions replace the single direction axis
- Two corners confirmed (Constraint = RCI, Composition = Arch F)
- Two predicted (Transformation = Noether lens, Generation = Dirac test)

**Relation Space:**
- "Architecture lives in transitions, not nodes" (confirmed across 5 projects)
- Don't store nodes — store relations/gluing data

**Category Theory Hypothesis (EOS-level, NOT from Curt):**
- If operators are morphisms (transformations), not objects, the Museum may be a category
- Category Theory as comparative language ABOVE sheaf theory
- Operators extracted from different domains share structure because they're all structure-preserving mappings

**Key Correction:** Curt is anti-premature-unification, NOT anti-unification. "Only unify when gluing conditions are earned."

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
   Synthesist/Auditor    Nova            "Are these the same deeper operation?"
                                         "Does this survive formal pressure?"
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
| Relation Space | Curt/Barandes | Architecture lives in transitions, not nodes |
| Anti-Premature Unification | Curt | Only unify when gluing conditions are earned |

---

## Success Criteria

```
   SIGNAL                              DIRECTION
   ──────                              ─────────
   Independent convergence             Increasing
   Predictive power                    Increasing
   Need for new operators              Decreasing
   Explanatory compression             Increasing
   Architecture reuse                  Increasing (new from Museum B)
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
| Phase 0A | CFA Transcripts | CFA deliberation IS a valid dig site |
| Phase 0B | Map 6 / Fleet | Extractor discrimination tiers feed LLM Behavioral Matrix routing |
| OP-008/009 | CFA Framework-G | New operators recovered from CFA evaluation of Consciousness as Telos |
| Architecture F | New_10_TOE (Curt) | Composition Analysis — audits other architectures for valid operations |
| Discovery Simplex | New_10_TOE / New_9 | 4-corner organizing framework for architectures |
| Relation Space | Barandes + Curt + CFA + ARMADA + EOS | 5-project convergence: "don't privilege nodes" |
| Category Theory hyp. | EOS synthesis | Operators as morphisms — Museum may be a category |

---

## File Index

```
   New_9_Cognitive_Archaeology/
   ├── README.md                                Core vision + falsification criteria
   ├── DISCOVERY_ARCHITECTURES.md               Museum B: architectures + simplex + relation space
   ├── FIELD_MANUAL.md                          Workflow + admission criteria + norms
   ├── LEDGER.md                                Confidence tracking + promotion gates
   ├── RESEARCH_QUESTIONS.md                    Open questions driving the program
   ├── DIG_SITES/
   │   ├── 000_Extractor_Calibration/           Phase 0 instrument calibration
   │   │   ├── README.md                        Dig site overview
   │   │   ├── experiment_design.md             Procedural details
   │   │   ├── PRE_REGISTRATION.md              Frozen expectations
   │   │   ├── ADMISSION_EVALUATIONS.md         Operator admission decisions
   │   │   ├── ARM_1_ANALYSIS.md                Phase 0A results
   │   │   └── extractions/                     164+ extraction files (Phase 0A + 0B)
   │   ├── 001_Adlam_Barandes/                  First excavation (seeded from New_8)
   │   ├── 002_Barandes/                        Barandes solo — COMPLETE (40 insights)
   │   ├── 003_Dirac/                           Q50 #1 — forward-generative test (PLANNED)
   │   ├── 004_Wolfram/                         Q50 #2 — computational architecture
   │   ├── 005_Hermann/                         Q50 #3 — philosophical auditing
   │   ├── 006_Pearl/                           Causal separation, convergence potential
   │   ├── 007_Dennett/                         Heterophenomenology, Nyquist link
   │   └── 008_Jaynes/                          ISP lineage, MaxEnt
   ├── MUSEUM/
   │   ├── INDEX.md                             Master operator list (15 operators)
   │   ├── GRAPH.md                             Relationships + Failure Atlas + direction axis
   │   ├── RETIRED.md                           Failed/retired operators
   │   └── operators/                           Individual operator pages (15)
   ├── TOOLS/
   │   └── extract_operators.py                 Multi-extractor pipeline (17 extractors)
   ├── compression_candidates/                  Theoretical compression explorations
   │   ├── README.md                            Third Law, promotion pathway
   │   └── category_theory/                     UCC — predictions registered, 0 tests run
   └── TEMPLATES/
       ├── DIG_SITE_TEMPLATE.md
       ├── OPERATOR_TEMPLATE.md
       └── NOTEBOOKLM_PROMPTS.md

   New_10_TOE/ (separate staging folder, cross-pollinates to New_9)
   ├── README.md                                Source overview + architectural significance
   ├── _IN/transcript.md                        Formatted transcript
   ├── _IN/*.md, *.pdf                          NotebookLM reports (3 .md, 3 .pdf)
   └── _ROUND_1/                                38 questions (Q1-Q38), formal audit
       ├── chat.md                              All Q&A (6 levels deep)
       ├── routing.md                           Cross-project connections (COMPLETE)
       ├── REVIEW_NOTES_New_10_TOE.md           Quality assessment (CONFIRMED)
       ├── INSIGHTS/Reverse_Elephant.md         Post-audit synthesis
       ├── CONNECTIONS/Reverse_Elephant.md      13 cross-project connections
       └── EXPERIMENTS/Reverse_Elephant.md      8 experiments staged
```

---

*Created: 2026-07-06*
*Updated: 2026-07-10 — Phase 0C COMPLETE, Museum A: 9→15 operators (OP-010 through OP-015 from Dig Site 002), Architecture E INSTANTIATED, empirical arm UNBLOCKED, Failure Atlas extended, reconciled against Mission Control*
*Map #19*
*Territory: The Grammar of Thought*
