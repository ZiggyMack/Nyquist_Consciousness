# Operator 011: Subtractive Discovery

**Confidence:** YELLOW
**First recovered:** Dig Site 002 (Barandes, via Nova + NotebookLM Q15/Q35 extraction)
**Independent confirmations:** 2 (Barandes' practice, Nova's formalization)
**Extractor-independence:** Partial (2 extractors: NotebookLM Q15, Nova independent synthesis)
**Class:** Minimal Sufficiency Operator

---

## Definition

Discover new theory by systematically removing assumptions until only the minimal structure needed for empirical recovery remains. Theory construction via removal, not addition.

---

## The Operation

When facing a complex or confusing theoretical framework:

1. **Identify ambiguity** — find where the formalism breaks, contradicts, or becomes vague
2. **Remove the suspect ingredient** — take out the structure that seems responsible for the confusion
3. **Stress test empirical recovery** — check whether the remaining structure still reproduces all confirmed predictions
4. **Repeat** until only minimal sufficiency remains

The operator asks: "What can we remove from the framework while preserving discriminative power?" It terminates when further removal breaks empirical adequacy.

**Detection condition:** When a theory works but carries unexplained complexity, vagueness, or "extra moving parts" that seem to do no empirical work. The signal is: things that are in the formalism but don't correspond to anything observable.

**Scope:** Domain-conditional — applies when a mature theory exists with suspected representational overhead. Does NOT apply to early-stage theory building where you don't yet know what's needed. Requires enough empirical data to test what survives removal.

**IMPORTANT SCOPE BOUNDARY:** This operator is about theory construction via removal. It is NOT about extracting signals from transcripts or data. Keep it separate from extraction operators or it becomes a catch-all.

---

## Examples

### From Barandes (Dig Site 002)

ISP was discovered by subtracting from quantum mechanics, not adding to it. Barandes removed: superposition (not needed — systems always have definite configurations), wave function collapse (not needed — no superposition means nothing to collapse), the observer role (not needed — division events emerge from any interaction, not special measurement). What remained: configurations, ordinary probabilities with sparse conditioning times, interaction-induced division events. This minimal structure reproduces all of quantum theory.

The heuristic is stronger than Occam's Razor: "Don't add explanatory entities until you've exhausted representational alternatives." Occam says prefer fewer entities. Barandes says check whether you've mistaken a representation for ontology FIRST.

### From Barandes — The Representation Ladder

Barandes consistently moves DOWNWARD on the representation ladder:

```text
Reality → Primitive ontology → Probability structure → Mathematics → Pedagogy
```

Each step removes representational overhead. He almost never moves upward. ISP appeared because he kept drilling down until he found a structure simpler than what everyone assumed was necessary.

---

## Failure Modes

1. **Over-Subtraction:** Removing structure that IS doing empirical work, producing a theory that's simpler but wrong. The stress test (step 3) catches this, but only if the empirical tests are comprehensive enough.
2. **Subtraction as Evasion:** Declaring something "not needed" because it's hard to formalize, not because it's genuinely dispensable. Barandes is careful: he acknowledges ISP's "aesthetic gap" (unspecified joint probabilities) rather than hand-waving it away.
3. **Premature Termination:** Stopping subtraction too early because the remaining structure "feels right." The operator demands you keep removing until something breaks.

---

## Counterexamples

### CE-1: Many-Worlds — Theory by Addition

**Violation:** Everett added parallel universes rather than subtracting structure.

**Did it work?** Partially — Many-Worlds removes the observer problem but at the cost of infinite ontological overhead (parallel universes) and an unsolved probability problem (Born rule derivation).

**What this tells us:** Addition CAN work, but Subtractive Discovery produces leaner results. When addition and subtraction both solve the same problem, subtraction usually wins on parsimony. Barandes' ISP solves the same measurement problem as Many-Worlds but with less ontological commitment.

---

## Duals and Related Operators

| Relationship | Operator | Explanation |
|-------------|----------|-------------|
| Complementary | OP-010 (Altitude Escalation) | Altitude Escalation climbs UP (meta-level). Subtractive Discovery drills DOWN (remove structure). Opposite directions. |
| Requires | OP-001 (Representation ≠ Ontology) | You must be able to distinguish representation from ontology before you know WHAT to subtract. Subtracting genuine ontology breaks the theory; subtracting representation overhead doesn't. |
| Enables | OP-006 (Under-Determination Detection) | Once structure is removed, underdetermination becomes visible — you can see what the remaining formalism does and doesn't determine. |
| Related | OP-004 (Reconstruction Before Judgment) | Reconstruction is a prerequisite — you need faithful understanding of what you're subtracting from. |

---

## Alternative Decompositions

### AD-1: Subtractive Discovery = OP-001 + Empirical Stress Test

**Decomposition:** First apply OP-001 to identify what's representation vs ontology, then check whether removing the representation breaks predictions.

**Evidence for:** Step 1 (identify ambiguity) is essentially OP-001. Step 3 (stress test) is the empirical check. The combination might be a composed operator, not a primitive.

**Evidence against:** Subtractive Discovery includes a SEARCH procedure (steps 2-4 iterated) that OP-001 alone doesn't provide. OP-001 identifies; Subtractive Discovery removes and tests. The iteration is the distinctive feature.

**Status:** Open

---

## Evolution Log

| Date | Event | Details |
|------|-------|---------|
| 2026-07-09 | Recovered | Extracted from Barandes interview (Q15) by NotebookLM; independently formalized by Nova |
| 2026-07-09 | Named | Initially conflated with OP-010 (Altitude Escalation). Nova's Round 3 feedback distinguished them as different operators at different levels |
| 2026-07-10 | Registered | Formalized with 4-step process and scope boundary per CFA Claude's guidance |

---

## Provenance Chain

| # | Dig Site | Thinker | Form | Date |
|---|---------|---------|------|------|
| 1 | 002 | Barandes | ISP discovery: removed superposition, collapse, observer from QM; minimal structure reproduced all predictions | 2026-07-09 |
| 2 | 002 | Nova | Independent formalization: "Don't add explanatory entities until you've exhausted representational alternatives" as stronger-than-Occam heuristic | 2026-07-09 |
| 3 | 002 | Q35 | 7 concrete instances catalogued with explicit 4-step process: subtracted (1) dense joint probs, (2) physical wave function, (3) collapse, (4) observer, (5) determinism, (6) Many-Worlds, (7) interventionist causation. Each survived empirical stress test. FAILURE MODE identified: subtracting a genuine primitive (Many-Worlds trying to subtract probability = is-ought fallacy). | 2026-07-10 |

---

*Registered: 2026-07-10*
*Last updated: 2026-07-10 — Q35 7-instance catalogue and failure mode added*
