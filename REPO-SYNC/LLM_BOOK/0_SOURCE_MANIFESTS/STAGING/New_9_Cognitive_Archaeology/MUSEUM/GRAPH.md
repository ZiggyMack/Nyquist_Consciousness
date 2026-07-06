# Operator Relationship Graph

This document maps how recovered operators relate to each other. As new operators are added, update this graph.

---

## Hierarchy

OP-006 (Under-Determination Detection) is the most general operator. Others are special cases or consequences:

```
OP-006: Under-Determination Detection
├── OP-001: Representation ≠ Ontology  (UD applied to representations)
├── OP-002: Hidden Selection Audit     (UD applied to selection mechanisms)
└── OP-005: Hidden Structure Injection (UD applied to all import channels)
    ├── via representation  →  representation bias
    └── via evaluator       →  smuggled observer
```

---

## Operational Sequence

The operators have a natural execution order — a protocol for examining any claim:

```
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

## Predicted Relationships (to be confirmed by future dig sites)

- **Pearl** likely performs OP-001 (distinguishing causal graph from physical system), OP-002 (asking what interventions select outcomes), and OP-006 (identifying when observational data underdetermines causal structure)
- **Jaynes** likely performs OP-005 (detecting smuggled physical information in probability assignments) and OP-006 (the entire maximum entropy program is about what distributions are determined vs underdetermined by the constraints)
- **Dennett** likely performs OP-004 (heterophenomenology IS reconstruction before judgment) and a NEW operator related to "competence without comprehension" (evolution produces functional outcomes without understanding — this may be a new operator or a variant of OP-003)

---

*Last updated: 2026-07-06*
