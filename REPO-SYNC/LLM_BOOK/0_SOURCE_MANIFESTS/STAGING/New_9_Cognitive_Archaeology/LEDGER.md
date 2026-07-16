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
| **Multi-Extractor Convergence** | MEC | Multiple independent extractors recovered this operator museum-blind from the same source — evidence for extractor-independence, but still single-source |

A Collaborative confirmation from two researchers across two frameworks (e.g., CFA Claude + Nova synthesizing across physics and audit methodology) is meaningfully stronger than a single Synthetic identification, but weaker than independent thinkers arriving at it from unrelated domains.

---

## Current Registry

Dig Site 000 extractor calibration is COMPLETE (Phases 0A/0B/0C + H-baseline). Extractor tiering established: Tier 1 (DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B). H-baseline result: MEC excess ~ 0, operator presence saturates at competence. GREEN promotion for OP-008/009 blocked (criterion (c): found in neg-H). CRUX-derived evidence (PT entries for 001, 004, 007) is doubly confounded: Claude examining Claude. Valid as a hypothesis-generator; not valid as extractor-independent confirmation.

| ID | Operator | Confidence | Ext-Indep | Count | Evidence Types | Dig Sites | Notes |
| -- | -------- | ---------- | --------- | ----- | -------------- | --------- | ----- |
| 001 | Representation ≠ Ontology | YELLOW | Unknown | 4 | Indep, Indep, Indep, Indep, PT×2 | 001, CFA/FUT, 002, 003 | Barandes + FUT + Dig 002 + Dirac (003: "method of representations" vs coordinate-free invariants/kets). CRUX_MS + CRUX_IP (confounded PT) |
| 002 | Hidden Selection Audit | RED | Unknown | 1 | Indep | 001 | Barandes: "what is doing the selecting?" |
| 003 | Goal → Optimization Collapse | RED | Unknown | 1 | Indep | 001 | Adlam: goal specification immediately fixes credences |
| 004 | Reconstruction Before Judgment | YELLOW | Unknown | 3 | Indep, Indep, Indep, PT×1 | 001, CFA, 002 | Barandes/Adlam + CFA Phase 1a + Dig 002. **CE-1 (Dig 003): Dirac deliberately VIOLATES it** — refuses to reconstruct in others' terms ("I put it into my own notation"), yet succeeds. Boundary case, not a rediscovery; count unchanged. PT: CRUX_MS (confounded) |
| 005 | Hidden Structure Injection | RED | Unknown | 1 | Collab | 001 | Nova + CFA Claude convergence: OP-001 + OP-002 are duals. Collab not Synth; but both parties share CFA context |
| 006 | Under-Determination Detection | RED | Unknown | 3 | Synth, Indep, Indep | 001, 002, 003 | Nova synthesis + Dig 002 + Dirac (003: flagged the scattering singularity, imported "outward-moving only" to fix it). 3rd independent source — YELLOW candidate on next review |
| 007 | Locate Disagreement Layer | YELLOW | Partial (2) | 3 | Indep, Indep, PT×2, MEC×2 | 001, DBEP, 000 | DBEP + Adlam. CRUX_MS: Layer Mismatch failure (confounded PT). CRUX_IP: Nova successful application (less confounded — Nova is not Claude). CFA: 2 rediscoveries — metric/dimension separation + meta-dispute identification (4/4 multi-extractor convergence, museum-blind) |
| 008 | Symmetry Testing of Standards | RED | Partial (4) | 1 | MEC | 000 | Recovered via 4/4 museum-blind extraction. Phase 0C: 4 Tier 1 extractors confirm. GREEN BLOCKED: found in neg-H (H-baseline). |
| 009 | Contested ≠ Defeated | RED | Partial (4) | 1 | MEC | 000 | Recovered via 4/4 museum-blind extraction. Phase 0C: 4 Tier 1 extractors confirm. GREEN BLOCKED: found in neg-H (H-baseline). |
| 010 | Altitude Escalation | YELLOW | Unknown | 1 | Indep | 002 | Nova meta-analysis of Barandes extraction. Demonstrated in action: Q1-Q20 to Q21-Q40 generation. Information operator. |
| 011 | Subtractive Discovery | YELLOW | Partial (2) | 3 | Indep, Indep, Indep | 002, 003 | Barandes + Nova + Dirac (003: stripped classical visualization/determinism to the minimal algebraic substratum). Minimal Sufficiency operator. |
| 012 | Pedagogical Forcing | YELLOW | Unknown | 1 | Indep | 002 | Barandes via NotebookLM Q15. Promoted RED→YELLOW (Q33+Q36 dual confirmation). Constraint-Induced Discovery operator. |
| 013 | Epistemic Boundary Setting | YELLOW | Unknown | 2 | Indep, Indep | 002, 003 | Barandes + Dirac (003: "Class One" philosophy quarantined vs "Class Two" math flaws). Now 2 independent thinkers. |
| 014 | Ontological Downgrading | RED | Unknown | 1 | Indep | 002 | Barandes: graded spectrum replaces binary "is X real?" |
| 015 | Question Completion | RED | Unknown | 1 | Indep | 002 | Barandes: generate smallest set of higher-order questions that maximally increase understanding. Dual of compression. |
| 016 | Anomaly Elevation | RED | Unknown | 1 | Indep | 003 | Dirac: non-commutation → Poisson bracket; negative energy → antimatter. Aesthetic Generation family. Failure mode: elevating coincidence (Large Numbers) |
| 017 | Formalism-First Generation | RED | Unknown | 1 | Indep | 003 | Dirac: "equations before interpretation"; spin fell out of the algebra. Pre-registered as "formalism-as-oracle." Aesthetic Generation family |
| 018 | Systematic Structural Translation | RED | Unknown | 1 | Indep | 003 | Dirac: Poisson bracket → commutator. Confirmed distinct from OP-001 (runs after it). Translation family |
| 019 | Aesthetic Filtering | RED | Unknown | 1 | Indep | 003 | Dirac: beauty over experiment ("Final Answer" standard). Failure mode = "Beauty's Two Faces." Aesthetic Generation family |

---

## Transition Log

| Date | Operator | From | To | Trigger |
|------|----------|------|----|---------|
| 2026-07-08 | OP-008 Symmetry Testing | — | RED | Admitted via 6/6 Field Manual criteria, 4/4 multi-extractor convergence |
| 2026-07-08 | OP-009 Contested ≠ Defeated | — | RED | Admitted via 6/6 Field Manual criteria, 4/4 multi-extractor convergence |
| 2026-07-08 | OP-007 Locate Disagreement Layer | YELLOW | YELLOW (evidence added) | 2 CFA rediscoveries (metric separation + meta-dispute) via museum-blind extraction. Ext-Indep updated to Partial (2). |
| 2026-07-10 | OP-010 Altitude Escalation | — | YELLOW | Admitted from Dig Site 002. Independent confirmation via demonstrated use in Q21-Q40 generation. |
| 2026-07-10 | OP-011 Subtractive Discovery | — | YELLOW | Admitted from Dig Site 002. 2 independent sources: Barandes practice + Nova formalization. |
| 2026-07-10 | OP-012 Pedagogical Forcing | — | YELLOW | Admitted RED, promoted via Q33+Q36 dual confirmation. |
| 2026-07-10 | OP-013 Epistemic Boundary Setting | — | YELLOW | Admitted RED, promoted via Q33 missing operator + Q32 Failure Atlas shadow. |
| 2026-07-10 | OP-014 Ontological Downgrading | — | RED | Admitted from Dig Site 002. |
| 2026-07-10 | OP-015 Question Completion | — | RED | Admitted from Dig Site 002. |
| 2026-07-10 | OP-001 Representation != Ontology | YELLOW | YELLOW (evidence added) | Dig Site 002 rediscovery. Count 2→3. |
| 2026-07-10 | OP-004 Reconstruction Before Judgment | YELLOW | YELLOW (evidence added) | Dig Site 002 rediscovery. Count 2→3. |
| 2026-07-10 | OP-006 Under-Determination Detection | RED | RED (evidence added) | Dig Site 002 rediscovery. Count 1→2. |
| 2026-07-11 | OP-008 Symmetry Testing | RED | RED (GREEN BLOCKED) | H-baseline: found in neg-H. Criterion (c) not met. Ext-Indep updated to Partial (4) via Phase 0C. |
| 2026-07-11 | OP-009 Contested != Defeated | RED | RED (GREEN BLOCKED) | H-baseline: found in neg-H. Criterion (c) not met. Ext-Indep updated to Partial (4) via Phase 0C. |
| 2026-07-16 | OP-016 Anomaly Elevation | — | RED | Admitted via 6/6 Field Manual criteria (Dig 003, Dirac). Aesthetic Generation family. |
| 2026-07-16 | OP-017 Formalism-First Generation | — | RED | Admitted 6/6 (Dig 003). Pre-registered as "formalism-as-oracle." |
| 2026-07-16 | OP-018 Systematic Structural Translation | — | RED | Admitted 6/6 (Dig 003). Confirmed distinct from OP-001 (runs after it). |
| 2026-07-16 | OP-019 Aesthetic Filtering | — | RED | Admitted 6/6 (Dig 003). Failure mode = "Beauty's Two Faces." |
| 2026-07-16 | OP-001 Representation != Ontology | YELLOW | YELLOW (evidence added) | Dig 003 rediscovery. Count 3→4. |
| 2026-07-16 | OP-006 Under-Determination Detection | RED | RED (evidence added) | Dig 003 rediscovery. Count 2→3. YELLOW-eligible on next review. |
| 2026-07-16 | OP-011 Subtractive Discovery | YELLOW | YELLOW (evidence added) | Dig 003 rediscovery. Count 2→3. |
| 2026-07-16 | OP-013 Epistemic Boundary Setting | YELLOW | YELLOW (evidence added) | Dig 003 rediscovery. Count 1→2 (2 independent thinkers). |
| 2026-07-16 | OP-004 Reconstruction Before Judgment | YELLOW | YELLOW (counterexample) | Dig 003: Dirac violates it and succeeds — boundary case CE-1. Count unchanged. |

---

## Dig Site 000 Preliminary Evidence (2026-07-08)

Four-way extraction on CFA transcripts (Claude + Grok extractors × v2 pilot + v2.1 MS-only transcripts). Museum-blind — no CFA vocabulary shown to extractors. This is partial Phase 0A data (multi-extractor agreement on source text). Negative controls and granularity sensitivity not yet run.

**Five stable operators recovered across all four extractions:**

| CFA Operator | Museum Cross-Ref | Evidence Type |
|-------------|-----------------|---------------|
| Metric/dimension separation | OP-007, OP-001 (rediscovery) | Multi-extractor convergence |
| Symmetry testing of standards | No match (candidate new) | Multi-extractor convergence |
| Concession tracking with explicit pricing | No match (candidate new) | Multi-extractor convergence |
| Distinguishing contested from defeated | No match (candidate new) | Multi-extractor convergence |
| Meta-dispute identification | OP-007 (rediscovery) | Multi-extractor convergence |

**Extractor agreement:** 7 exact matches + 2 strong matches out of 9 Grok operators matched Claude's on the v2.1 transcript. This exceeds the pre-committed 40% pairwise agreement threshold for Phase 0A.

**Methodological finding — "shorter is richer":** Grok extracted 9 operators from 66K chars (v2.1 MS-only, stalled deliberation) vs 5 from 423K chars (v2 pilot, 7-metric convergence). Stall-induced metacognitive pressure forces auditors to explicitly articulate reasoning operations. Concentrated single-metric deliberation with impasses produces richer CA extraction material than broad multi-metric convergence runs. Implication: select transcripts with stalls and impasses for extraction, not clean convergences.

**Differential presence evidence (Buddhism batch, 2026-07-08):** 48 good runs across 5 Buddhism matchups produced zero CRUXes, zero DI fires, zero coupling probes. Meta-dispute identification — the operator most strongly confirmed in CT transcripts — is predicted absent in Buddhism deliberations (no architectural gating challenge to trigger it). This is evidence AGAINST Falsification Criterion 3 ("operators are universally present"). If extraction on a Buddhism transcript confirms the absence, that is differential presence — the operator discriminates.

---

## Saturation Tracker

| Dig Site | New Operators | Rediscoveries | Ratio |
|----------|--------------|---------------|-------|
| 001 Adlam/Barandes | 6 | 0 | — |
| 000 CFA (admitted) | 2 (OP-008, OP-009) | 2 (OP-007 x2) | 0.50 |
| 000 CFA (held) | 1 (Concession Pricing) | — | — |
| 002 Barandes solo | 6 (OP-010 through OP-015) | 3 (OP-001, OP-004, OP-006) | 0.50 |
| 003 Dirac | 4 (OP-016 through OP-019) | 4 (OP-001, OP-006, OP-011, OP-013) | 1.00 |

When rediscoveries consistently outnumber new operators, we are approaching saturation. Trajectory: 0.50 at Dig Sites 000/002 → **1.00 at Dig 003** (first dig where rediscoveries equal new operators). One data point, not a trend — but the first saturation signal. Note Dig 003 also produced a *counterexample* (OP-004) and 4 *held* candidates reclassified as heuristics/techniques, so the effective "new operator" yield is conservative.

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

*Last updated: 2026-07-16 — Dig Site 003 (Dirac): OP-016 through OP-019 admitted RED (6/6 criteria); rediscoveries OP-001 (3→4), OP-006 (2→3), OP-011 (2→3), OP-013 (1→2); OP-004 counterexample CE-1 (Dirac inversion); Saturation Tracker 003 row (first 1.0 ratio); 4 candidates held as heuristics/techniques. New family: Aesthetic Generation.*
*2026-07-11 — OP-010 through OP-015 added from Dig Site 002; OP-001/004/006 rediscovery counts updated; OP-008/009 GREEN blocked (H-baseline); Phase 0 status COMPLETE; Dig Site 002 added to Saturation Tracker*
