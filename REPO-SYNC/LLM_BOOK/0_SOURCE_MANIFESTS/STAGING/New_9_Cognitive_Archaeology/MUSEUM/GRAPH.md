# Operator Relationship Graph

This document maps how recovered operators relate to each other. As new operators are added, update this graph.

---

## Hierarchy

OP-006 (Under-Determination Detection) is the most general operator. Others are special cases or consequences:

```text
OP-006: Under-Determination Detection
├── OP-001: Representation ≠ Ontology  (UD applied to representations)
├── OP-002: Hidden Selection Audit     (UD applied to selection mechanisms)
├── OP-005: Hidden Structure Injection (UD applied to all import channels)
│   ├── via representation  →  representation bias
│   └── via evaluator       →  smuggled observer
├── OP-008: Symmetry Testing of Standards  (UD revealed via cross-candidate application)
└── OP-009: Contested ≠ Defeated           (UD → damage calibration)
```

---

## Operational Sequence

The operators have a natural execution order — a protocol for examining any claim:

```text
Step 1: OP-004  Reconstruction Before Judgment
        ↓       (faithfully reconstruct the object first)
Step 2: OP-006  Under-Determination Detection
        ↓       (does the formalism determine the conclusion?)
Step 3: OP-002  Hidden Selection Audit
        ↓       (if not — what selected the conclusion?)
Step 4: OP-005  Hidden Structure Injection
        ↓       (what was imported without acknowledgment?)
Step 5: OP-001  Representation ≠ Ontology
        ↓       (is the import a feature of reality or the description?)
Step 6: OP-003  Goal → Optimization Collapse
                (if under-determined — does declaring the goal resolve it?)
```

This sequence IS the CFA Phase sequence at a higher level of abstraction:
- Steps 1-2 = Phase 1a (faithful reconstruction + coherence check)
- Steps 3-5 = Phase 1b (auditor calibration / isomorphism checks)
- Step 6 = Phase 2 (lever calibration with declared priors)

---

## Failure Atlas

Each operator, when absent, produces a named cognitive failure. The failure is the operator's shadow — finding the failure in the wild is evidence the operator is real.

| Absent Operator | Named Failure | What Happens | Classical Name |
|----------------|---------------|--------------|----------------|
| OP-001 Representation ≠ Ontology | **Reification** | The map is mistaken for the territory. Properties of the description are treated as properties of reality. | Reification fallacy, map-territory confusion |
| OP-002 Hidden Selection Audit | **Selection Blindness** | An outcome appears uniquely determined when it was actually selected by an unexamined mechanism. | Survivorship bias, hidden variable |
| OP-003 Goal → Optimization Collapse | **Optimization Drift** | Rational strategy is debated in the absence of a declared goal, producing unresolvable disagreement. | Moving goalposts, unstated assumptions |
| OP-004 Reconstruction Before Judgment | **Strawman** | The object is evaluated in the critic's framing, not the creator's. Conclusions drawn about a distortion. | Strawman fallacy, principle of charity violation |
| OP-005 Hidden Structure Injection | **Invisible Import** | Evaluators, observers, coordinate systems, or representations are smuggled in without acknowledgment. Analysis secretly depends on what it claims to be analyzing. | Question-begging, circular reasoning |
| OP-006 Under-Determination Detection | **Determination Illusion** | A formalism appears to uniquely determine an outcome when it actually doesn't. The imported determination goes unnoticed. | Underdetermination (Quine), theory-ladenness |
| OP-007 Locate Disagreement Layer | **Layer Confusion** | A description-layer dispute is treated as an evaluation-layer dispute (or vice versa). Resolution attempts address the wrong stratum. | Talking past each other, level confusion |
| OP-008 Symmetry Testing of Standards | **Prosecution Bias** | A demanding standard is applied to one position while its implications for all positions go unexamined. Selective application masquerades as principled assessment. | Double standard, special pleading |
| OP-009 Contested ≠ Defeated | **Premature Elimination** | Every unresolved difficulty is treated as a refutation. Frameworks with open problems score zero. The space of live options shrinks artificially. | False dichotomy (works/doesn't), anomaly=falsification |

### Reading the Atlas

- **From operator to failure:** "If OP-001 is absent, expect Reification."
- **From failure to operator:** "We observe Strawman reasoning → the missing operator is OP-004."
- The Atlas is bidirectional: it predicts failures AND diagnoses them.
- Every CRUX declaration in CFA can be mapped to this atlas — the CRUX names the failure, the Atlas identifies the absent operator.

---

## Dual Pairs

| Operator A | Operator B | Duality |
|-----------|-----------|---------|
| OP-005 (rep bias channel) | OP-005 (observer channel) | Same operation, different entry point: inject via description vs inject via describer |

---

## CFA-Recovered Operators (Dig Site 000 Preliminary)

Four-way extraction (Claude + Grok extractors × 2 transcripts) recovered five stable operators from CFA deliberation transcripts. These are museum-blind — no CFA vocabulary was shown to the extractors. Cross-referencing against existing Museum:

| CFA Operator | Museum Match | Verdict | Notes |
|-------------|-------------|---------|-------|
| Metric/dimension separation | OP-007, OP-001 | REDISCOVERY | Separating which dimension a dispute actually lives in = OP-007. Separating the metric representation from the thing measured = OP-001. |
| Symmetry testing of standards | **OP-008** (new) | ADMITTED | Passes 6/6 admission criteria. Checking whether a criterion produces consistent results across all positions. Related to OP-006. |
| Concession tracking with explicit pricing | No match | HELD | 4/4 extraction convergence but marginal on criteria 5-6 (translation, epistemic transformation). May be a deliberation heuristic rather than an operator. Pending future dig site evidence. |
| Distinguishing contested from defeated | **OP-009** (new) | ADMITTED | Passes 6/6 admission criteria. Separating "under pressure" from "refuted." Related to OP-006. |
| Meta-dispute identification | OP-007 | REDISCOVERY | Identifying that the dispute is about the metric definition, not the object-level facts = Locate Disagreement Layer. Grok independently surfaced this across both transcripts without CFA vocabulary. |

**Result: 2 rediscoveries (OP-007), 2 operators admitted (OP-008, OP-009), 1 held (Concession Pricing).** Formal admission evaluation in `DIG_SITES/000_Extractor_Calibration/ADMISSION_EVALUATIONS.md`.

**Evidence quality:** Four-way extraction convergence. Two different extractors (Claude, Grok) independently recovered the same operators from two different transcripts (v2 pilot 423K chars, v2.1 MS-only 66K chars). 7 exact matches + 2 strong matches out of 9 Grok operators matched Claude's. This is preliminary Phase 0A data — multi-extractor agreement on a source text.

---

## Composition Pathways (Empirical Question)

The Operational Sequence (above) shows a theorized execution order for Museum operators. The CFA extractions raise a sharper question: **do the five stable operators compose in a consistent order within actual deliberation?**

From the v2.1 MS transcript (15 rounds, stall + DI + coupling probe):

```text
Observed pathway (preliminary — one transcript):
  Metric separation (R1–2)
    → Symmetry testing (R3–5)
    → Concession pricing (R2–4, interleaved)
    → Contested ≠ defeated (R2–8, sustained)
    → Meta-dispute identification (R5–8, crystallizes)
```

The pipeline for investigating composition is deliberately staged. Each step must be earned before the next is adopted:

```text
Recovered operators (DONE — five stable)
  ↓
Composition statistics (co-occurrence, ordering across transcripts)
  ↓
Composition laws (if statistics reveal consistent patterns)
  ↓
Algebra (if laws satisfy associativity, identity — mathematical claim)
  ↓
Ask mathematicians what structure this is
```

Composition statistics are empirical. Associativity is already a mathematical interpretation. Both must be earned separately.

**Test:** Run extraction on a Buddhism transcript (zero CRUX, high convergence). Prediction: meta-dispute identification will NOT appear (there are no meta-disputes to identify in Buddhism deliberations). If 3 of 5 operators appear, they are CFA-general. If fewer, they may be gate-challenge-specific. The Buddhism zero-CRUX finding (48 good runs, 336 metric-deliberations, zero DI fires) is evidence for differential operator activation, not universal presence.

---

## Category Theory Interpretation

> **Operators are not objects that live inside frameworks. They are arrows that carry you between reasoning states.**

The Operational Sequence above is already a composition diagram. Category Theory formalizes what it means for operators to compose:

```text
Museum operators as morphisms:

  State_conflated ──OP-007──► State_decomposed ──OP-006──► State_determined
       │                                                        │
       └──────────────OP-004 (reconstruct first)───────────────┘
```

The Failure Atlas is the shadow: each absent morphism produces a named cognitive failure. Finding the failure in the wild is evidence the morphism is real.

**CRUX as categorical failure:** "There exists no structure-preserving morphism between these two local reasoning systems." Not "they disagree" — "there is currently no faithful translation." The Coupling Probe diagnoses exactly which morphism fails to translate.

**Natural transformation evidence:** Four-way extraction convergence (two extractors recovering the same operators) is evidence that the extraction is natural — intrinsic to the transcript, not an artifact of the extractor. This addresses the Core Confound directly: if the operators are natural transformations, they survive change of extractor.

See README.md § Mathematical Structure for the full theoretical treatment. This interpretation is descriptive compression after discovery, not a design input.

---

## Predicted Relationships (to be confirmed by future dig sites)

- **Pearl** likely performs OP-001 (distinguishing causal graph from physical system), OP-002 (asking what interventions select outcomes), and OP-006 (identifying when observational data underdetermines causal structure)
- **Jaynes** likely performs OP-005 (detecting smuggled physical information in probability assignments) and OP-006 (the entire maximum entropy program is about what distributions are determined vs underdetermined by the constraints)
- **Dennett** likely performs OP-004 (heterophenomenology IS reconstruction before judgment) and a NEW operator related to "competence without comprehension" (evolution produces functional outcomes without understanding — this may be a new operator or a variant of OP-003)

---

*Last updated: 2026-07-08 — OP-008/009 admitted, Failure Atlas updated, hierarchy expanded*
