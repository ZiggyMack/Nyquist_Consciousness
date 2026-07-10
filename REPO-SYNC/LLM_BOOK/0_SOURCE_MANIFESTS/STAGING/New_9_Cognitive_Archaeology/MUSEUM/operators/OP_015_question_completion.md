# Operator 015: Question Completion

**Confidence:** RED
**First recovered:** Dig Site 002 (Nova, meta-analysis of extraction pipeline)
**Independent confirmations:** 1
**Extractor-independence:** Unknown
**Class:** Information Operator

---

## Definition

Generate the smallest set of higher-order questions that would maximally increase understanding of a domain — the dual of compression. Not brainstorming; structured meta-inquiry with a termination condition.

---

## The Operation

Given a set of existing answers at level N, ask: "What is the smallest number of new questions whose answers would most increase understanding?" The questions must be:

1. Non-redundant with existing questions
2. At the same or higher inquiry level
3. Answerable in principle (not rhetorical)
4. Maximally discriminating (their answers would change what we think, not just confirm it)

The operator is the dual of compression: compression asks "what is the smallest description that preserves the information?" Question Completion asks "what is the smallest set of questions that would most expand the information?"

**Detection condition:** When existing answers feel comprehensive but the analyst suspects there are unknown unknowns. The question "what am I not asking?" is the trigger.

**Scope:** Universal — applicable to any inquiry. Part of the recursive meta-cycle: extract → compress → complete → extract at new level → repeat until no genuinely new level emerges.

---

## Examples

### From Nova (Dig Site 002)

After Q1-Q20 were answered, Nova generated Q21-Q40 using this operator. The 20 questions weren't random higher-order questions — they were specifically chosen to fill gaps in the extraction. Q22 (representation invariance) tests whether ISP's simplification preserves the right structure. Q33 (discovery operator) directly extracts the transferable artifact. Q41 (pair-dependency) tests a structural prediction. Each question was chosen because its answer would maximally change understanding.

### The Recursive Meta-Cycle

Question Completion is the recursion engine:
```text
Extract theory → compress → apply Question Completion → 
extract at new level → compress → apply Question Completion →
repeat until no genuinely new level emerges
```

The termination condition is genuine: when Question Completion produces questions that are rephrased versions of existing questions, the inquiry is saturated at that altitude.

---

## Failure Modes

1. **Brainstorming Disguised as Completion:** Generating many questions without the maximality constraint. Question Completion demands the SMALLEST set. If 5 questions suffice, 20 is not better — it's noise.
2. **Closed Questions:** Generating questions whose answers are already determined by existing answers. A "completion" question must be genuinely open — its answer should be unpredictable from what's already known.
3. **Infinite Generation:** Generating endlessly because the "smallest set" keeps growing. The operator has a natural termination: when the generated questions are structurally equivalent to previous questions at a different vocabulary, the inquiry is complete.

---

## Duals and Related Operators

| Relationship | Operator | Explanation |
|-------------|----------|-------------|
| Dual of | (Compression — not yet formalized) | Compression: smallest description preserving information. Question Completion: smallest question set maximally expanding information. |
| Receives input from | OP-010 (Altitude Escalation) | Altitude Escalation decides WHEN to climb a level. Question Completion decides WHAT to ask at the new level. |
| Related | OP-006 (Under-Determination Detection) | Both identify gaps. OP-006 finds where existing formalism underdetermines. OP-015 finds where existing questions under-cover. |

---

## Evolution Log

| Date | Event | Details |
|------|-------|---------|
| 2026-07-09 | Recovered | Nova performed this operation live, generating Q21-Q40 as the "completion" of Q1-Q20 |
| 2026-07-09 | Named | Nova identified it as the dual of compression and a core part of the recursive meta-cycle |
| 2026-07-10 | Registered | Formalized with termination condition and failure modes |

---

## Provenance Chain

| # | Dig Site | Thinker | Form | Date |
|---|---------|---------|------|------|
| 1 | 002 | Nova | Generated Q21-Q40 from Q1-Q20 answers using structured meta-inquiry, not brainstorming | 2026-07-09 |
| 2 | 002 | Demonstrated | Q21-Q40 are the PRODUCT of this operator — they exist because Question Completion was applied to Q1-Q20 outputs. The recursive meta-cycle is demonstrated: extract (Q1-Q20) → compress → complete (Q21-Q40) → extract at new level → compress → complete (Q41). Three iterations of the cycle visible in the data. However, the operator itself is still hypothesized rather than extracted from a thinker — it's a methodology we use, not one we've observed someone else use. | 2026-07-10 |

---

*Registered: 2026-07-10*
*Last updated: 2026-07-10 — demonstration provenance added (Q21-Q40 are its product; 3 recursive cycles observed)*
