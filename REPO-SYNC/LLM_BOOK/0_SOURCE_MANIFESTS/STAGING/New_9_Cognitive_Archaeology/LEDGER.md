# Operator Confidence Ledger

Tracks independent confirmation count for each recovered operator. Confidence levels:

- **GREEN — Confirmed**: 5+ independent thinkers. Structural primitive.
- **YELLOW — Candidate**: 2-4 independent thinkers. Promising, needs more excavation.
- **RED — Hypothesis**: 1 thinker only. Needs independent confirmation.

---

## Evidence Type Definitions

Three evidence types, ranked by epistemic weight (highest first):

| Type | Symbol | Definition |
| ------ | -------- | ---------- |
| **Independent** | Indep | Thinker arrived at this operator with no knowledge of our framework or each other — strongest confirmation |
| **Collaborative** | Collab | Two or more parties in dialogue converged on the synthesis — meaningful, but shared context means it could be prompted pattern-matching rather than independent discovery |
| **Synthetic** | Synth | We named the operator by pattern-matching across sources; no thinker formalized it themselves — working hypothesis, could be pareidolia |

A Collaborative confirmation from two researchers across two frameworks (e.g., CFA Claude + Nova synthesizing across physics and audit methodology) is meaningfully stronger than a single Synthetic identification, but weaker than independent thinkers arriving at it from unrelated domains.

---

## Current Registry

All operators currently show Ext-Indep: Unknown — all excavated by Claude. Dig Site 000 (extractor calibration) is queued before any real dig sites proceed. CRUX-derived evidence (PT entries for 001, 004, 007) is doubly confounded: Claude examining Claude. Valid as a hypothesis-generator; not valid as extractor-independent confirmation.

| ID | Operator | Confidence | Ext-Indep | Count | Evidence Types | Dig Sites | Notes |
| -- | -------- | ---------- | --------- | ----- | -------------- | --------- | ----- |
| 001 | Representation ≠ Ontology | YELLOW | Unknown | 2 | Indep, Indep, PT×2 | 001, CFA/FUT | Barandes + FUT. CRUX_MS + CRUX_IP: failure-mode confirmations — but PT evidence is Claude examining Claude (confounded) |
| 002 | Hidden Selection Audit | RED | Unknown | 1 | Indep | 001 | Barandes: "what is doing the selecting?" |
| 003 | Goal → Optimization Collapse | RED | Unknown | 1 | Indep | 001 | Adlam: goal specification immediately fixes credences |
| 004 | Reconstruction Before Judgment | YELLOW | Unknown | 2 | Indep, Indep, PT×1 | 001, CFA | Barandes/Adlam + CFA Phase 1a. PT: CRUX_MS — confounded (Claude examining Claude) |
| 005 | Hidden Structure Injection | RED | Unknown | 1 | Collab | 001 | Nova + CFA Claude convergence: OP-001 + OP-002 are duals. Collab not Synth; but both parties share CFA context |
| 006 | Under-Determination Detection | RED | Unknown | 1 | Synth | 001 | Nova synthesis. Action-framing incomplete; may be detection condition rather than operator |
| 007 | Locate Disagreement Layer | YELLOW | Unknown | 2 | Indep, Indep, PT×2 | 001, DBEP | DBEP + Adlam. CRUX_MS: Layer Mismatch failure (confounded PT). CRUX_IP: Nova successful application (less confounded — Nova is not Claude) |

---

## Transition Log

| Date | Operator | From | To | Trigger |
|------|----------|------|----|---------|
| — | — | — | — | No transitions yet |

---

## Saturation Tracker

| Dig Site | New Operators | Rediscoveries | Ratio |
|----------|--------------|---------------|-------|
| 001 Adlam/Barandes | 6 | 0 | — |

When rediscoveries consistently outnumber new operators, we are approaching saturation.

---

## Promotion Gates

Each stage transition is gated on specific evidence that rules out the specific artifact threat live at that stage. The bar rises sharply at each step. Presence is cheap; predicted absence is the only thing that earns the star.

### RED Observation --> YELLOW Candidate

An operator enters as Candidate when:

- (a) Extracted from at least 1 dig site
- (b) Given an operational definition precise enough that a second extractor can identify it independently
- (c) Demonstrated extractor agreement above pre-committed threshold on a held-out passage

**Gate:** Two extractors applying the definition see the same thing. Rules out "stylistic tic in one extraction."

### YELLOW Candidate --> GREEN Confirmed

An operator is Confirmed when it clears four hurdles:

- (a) **Extractor-independence** — appears across 3+ independent extractors (including heterogeneous types: different LLMs, different human disciplines), above chance
- (b) **Cross-thinker recurrence** — appears in N+ genuinely independent dig sites (pre-registered N, pre-registered independence criterion: thinkers plausibly unexposed to each other)
- (c) **Differential presence** — demonstrated absent in negative-control text AND in at least some genuine reasoning (it is not universal)
- (d) **Blind predictive success** — a blind extractor using the codebook correctly anticipates its presence in held-out text above chance

**Gate:** Survives the instrument-confound AND discriminates. Rules out "artifact of the extractor" and "present everywhere."

### GREEN Confirmed --> STAR Fundamental

Be miserly here. "Fundamental" is exactly the kind of word this project must distrust.

A Confirmed operator becomes a candidate for Fundamental only with:

- (a) **Cross-domain transfer** demonstrated — functions and is recognized across domain boundaries by reasoners native to only one side
- (b) **Failure-mode prediction** confirmed — its absence produces the specific, independently-recognized defect the theory predicts (see Failure Atlas)
- (c) **Irreducibility** — cannot be decomposed into or expressed as a combination of other Confirmed operators (else it's a molecule, not an atom)
- (d) Survival of a genuine, pre-registered attempt to falsify that specific operator's fundamentality, with the falsifier named in advance

**Gate:** Domain-general, consequential, irreducible, and survived someone trying to kill it. Log as "Fundamental (provisional)" with date and surviving-falsifier on record.

---

## Future Refinements (staged for when museum grows)

### 5-Dimensional Evidence Matrix

Nova proposed replacing the single evidence-type column with five independent axes — "different species of evidence, not stronger versions of the same":

| Dimension | What it measures |
|-----------|-----------------|
| Recovered | Found in a thinker's actual work |
| Independent Convergence | Multiple thinkers arrived at it independently |
| Pressure Tested | Survived adversarial challenge (CFA, counterexample review) |
| Predictive | Successfully predicted an operator in a new dig site before excavation |
| Compositional | Combines with other operators to produce emergent effects |

Adopt when the registry reaches 15+ operators and the single-column format becomes inadequate.

---

*Last updated: 2026-07-06*
