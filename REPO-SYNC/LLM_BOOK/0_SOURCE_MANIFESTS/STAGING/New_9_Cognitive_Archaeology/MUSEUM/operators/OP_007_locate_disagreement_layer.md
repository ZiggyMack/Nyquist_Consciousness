# Operator 007: Locate Disagreement Layer Before Resolving

**Confidence:** YELLOW
**First recovered:** DBEP Framework (pre-Dig Site 001)
**Independent confirmations:** 2 (DBEP, Adlam's DBEP-equivalent analysis)

---

## Definition

Before attempting to resolve a disagreement, identify which layer (description, belief, evaluation, or prediction) the disagreement actually lives in — resolving it at the wrong layer wastes effort or creates false resolution.

---

## The Operation

Two parties appear to disagree. Before attempting resolution, diagnose WHERE they disagree:

1. **Description layer:** They see different facts (or define terms differently)
2. **Belief layer:** They agree on facts but interpret them differently
3. **Evaluation layer:** They agree on interpretation but weight it differently
4. **Prediction layer:** They agree on everything above but predict different outcomes

Attempting to resolve a Description-layer disagreement with Evaluation-layer arguments is futile. Attempting to resolve an Evaluation-layer disagreement with more facts is futile. The layer must be correctly identified before resolution can begin.

Input: A disagreement between two parties.
Output: The layer where the disagreement actually lives.

---

## Examples

### From DBEP Framework

The Master→Description→Belief→Evaluation→Prediction stack. When CFA auditors (Claude and Grok) disagree on a metric score, the CRUX declaration identifies which layer the disagreement occupies. CRUX_MS in CFA was diagnosed as a Description-layer disagreement (auditors defining "Moral Substance" differently) masquerading as an Evaluation-layer disagreement (different scores).

### From Adlam (Dig Site 001)

Adlam's analysis of the self-location debate: proponents of different probability assignments appear to disagree about credences (Prediction layer), but actually disagree about goals (a layer BELOW Description — Master/Telos). She locates the disagreement at the correct layer and shows the apparent disagreement dissolves.

---

## Failure Modes

1. **Layer Mismatch:** Applying a resolution strategy appropriate for one layer to a disagreement at a different layer. Throwing more evidence at a values disagreement. Debating definitions when the real dispute is predictive.
2. **False Resolution:** Reaching apparent agreement at a surface layer while the underlying layer-mismatch persists. The disagreement recurs in new forms.

---

## Duals and Related Operators

| Relationship | Operator | Explanation |
|-------------|----------|-------------|
| Requires | OP-004 (Reconstruction Before Judgment) | Must reconstruct both positions before diagnosing where they diverge |
| Enables | OP-003 (Goal → Optimization Collapse) | If disagreement is at the Master/Telos layer, locating it enables the collapse |
| Triggered by | OP-006 (Under-Determination Detection) | Under-determination often manifests as layer-mismatch: the shared formalism underdetermines, and each party imports structure at a different layer |

---

## Provenance Chain

| # | Dig Site | Thinker | Form | Evidence Type | Date |
|---|---------|---------|------|---------------|------|
| 1 | — | DBEP Framework | Master→DBEP layer diagnosis | Independent | pre-existing |
| 2 | 001 | Adlam | Self-location debate: goal-layer disagreement masked as credence-layer | Independent | 2026-07-05 |
| 3 | — | CFA CRUX_MS_20260629 | Failure-mode confirmation (FM-1: Layer Mismatch): Claude's intra-auditor cycling was a Description-layer event (competing MS definitions) being resolved at the Evaluation layer (alternating scores). The cycling persisted because the resolution approach (re-scoring) was the wrong layer. Resolution = lock definition at Description layer before Evaluation begins. | Pressure-tested | 2026-06-29 |
| 4 | — | CFA CRUX_IP_20260629 | Successful application (by Nova): Nova diagnosed the inter-auditor IP divergence as a Description-layer disagreement (Claude and Grok using different IP definitions), not a Beliefs or Evaluation divergence. Correctly located before resolution was attempted. Proposed resolution (Iteration 3 locked definitions) is OP-007 applied operationally. | Pressure-tested | 2026-06-29 |

---

*Registered: 2026-07-06*
*Last updated: 2026-07-06*
