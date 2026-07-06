# Operator 005: Hidden Structure Injection

**Confidence:** RED
**First recovered:** Dig Site 001 (Nova synthesis of Barandes + Adlam)
**Independent confirmations:** 1

---

## Definition

Detect when an analysis quietly imports evaluators, observers, coordinate systems, representations, or optimization targets without declaring them.

---

## The Operation

When encountering a conclusion that appears to follow from the premises alone, audit the space between premises and conclusion for undeclared imports. The analysis may have quietly introduced:

- **Evaluators** (who is judging?) — smuggled observer
- **Representations** (which formalism?) — representation bias
- **Coordinate systems** (what reference frame?)
- **Optimization targets** (what is being maximized?)
- **Selection mechanisms** (what is doing the choosing?)

These are all instances of the same move: the analysis pretends its conclusion follows from the object alone, when it actually follows from the object **plus** imported structure.

Input: An argument or derivation that claims to be self-contained.
Output: A list of what was imported without acknowledgment.

---

## Examples

### From Barandes + Adlam (Dig Site 001)

Two parallel detection methods that appear unrelated but collapse into one:

**Representation bias:** The Everettian interpretation imports a preferred Hilbert space representation without acknowledging that the same math describes classical oscillators. The "branching" conclusion isn't in the physics — it's in the representation choice.

**Smuggled observer:** Emergence arguments import a macroscopic observer into microphysical theories and then claim to derive the macroscopic from the micro. The observer was there all along — hidden in the experimental apparatus that generated the microphysical data.

Nova's insight: these are **duals**. One injects structure through the description, the other through the describer. Same operator, different entry point.

---

## Failure Modes

1. **Invisible Import:** The most common failure — not realizing anything was imported. The conclusion feels "obvious" because the hidden structure was natural to the analyst.
2. **Partial Audit:** Checking for one type of import (e.g., observer bias) while missing another (e.g., representation bias). The dual structure means both channels must be audited.
3. **Import Laundering:** Acknowledging the import exists but claiming it's "harmless" or "merely conventional" when it actually determines the conclusion.

---

## Duals and Related Operators

| Relationship | Operator | Explanation |
|-------------|----------|-------------|
| Special case of | OP-001 (Rep ≠ Ontology) | HSI is what happens when OP-001 fails — you confuse imported structure with genuine ontology |
| Detected by | OP-002 (Hidden Selection Audit) | Asking "what selected this outcome?" is a specific probe for hidden imports |
| Caused by failure of | OP-006 (Under-Determination Detection) | When a formalism underdetermines and you don't notice, you import structure to fill the gap |

---

## Why This Operator Matters

This is the operator that demonstrates Nova's Mendeleev insight: two phenomena that looked unrelated (representation bias and smuggled observers) collapse into one when you look at the underlying operation rather than the surface manifestation. The collapse itself is a reasoning move — recognizing that apparent diversity masks structural unity. This may be a meta-operator: the operation of collapsing multiple operators into one.

---

## Provenance Chain

| # | Dig Site | Thinker | Form | Date |
|---|---------|---------|------|------|
| 1 | 001 | Nova | Unification of Q18 (rep bias) + Q20 (smuggled observer) into single pattern | 2026-07-05 |

---

*Registered: 2026-07-06*
*Last updated: 2026-07-06*
