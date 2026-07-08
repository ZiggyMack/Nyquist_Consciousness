# Admission Evaluations — Dig Site 000 Candidate Operators

Three candidate operators recovered from four-way CFA extraction require formal evaluation against the Operator Admission Criteria (Field Manual v2). Two additional operators were classified as rediscoveries of OP-007 and are evaluated separately for Ledger update.

**Evaluator:** Repo (Claude Opus 4.6)
**Date:** 2026-07-08
**Source data:** Four extraction files (Claude × 2 transcripts, Grok × 2 transcripts)
**Museum-blind extraction:** Yes — no CFA vocabulary or Museum operators shown to extractors

---

## Admission Criteria (from Field Manual)

| # | Criterion | Test |
|---|-----------|------|
| 1 | Describes an action | Can you say "the thinker PERFORMED this operation"? |
| 2 | Generalizes beyond domain | Does it apply outside the thinker's field? |
| 3 | Is reusable | Can someone else apply it to new material? |
| 4 | Has observable failure modes | What goes wrong when it's absent? |
| 5 | Survives translation | Can you express it in different terminology without losing the core move? |
| 6 | Transforms epistemic state | After applying it, does something change about what you know, believe, or investigate? |

Additionally: Is this an **operator**, a **heuristic**, or a **rhetorical technique**?

---

## Candidate 1: Symmetry Testing of Standards

### Extraction Evidence

| Extractor | Transcript | Name Used | Present? |
|-----------|-----------|-----------|----------|
| Claude | v2 pilot (423K) | "Applying a Universal-Standard Check" | Yes |
| Grok | v2 pilot (423K) | "Identifying when a standard proves too much" | Yes |
| Claude | v2.1 MS (66K) | "Applying Symmetry Tests to Standards" | Yes |
| Grok | v2.1 MS (66K) | "Testing standards for symmetry" | Yes |

**4/4 extractions.** Both extractors, both transcripts. Naming convergence strong: all four use "standard" or "symmetry" vocabulary independently.

### Admission Evaluation

| # | Criterion | Verdict | Reasoning |
|---|-----------|---------|-----------|
| 1 | Describes an action | **PASS** | "Test whether a scoring criterion, applied consistently across all competitors, produces absurd or uniform results." The thinker performs the symmetry check — it is an action, not a belief. |
| 2 | Generalizes beyond domain | **PASS** | Applies anywhere standards are used asymmetrically: legal reasoning (equal protection), scientific methodology (same statistical threshold for all hypotheses), hiring criteria, peer review. Any domain with evaluative criteria. |
| 3 | Is reusable | **PASS** | Any reasoner can take an evaluative standard and ask "if I apply this to all candidates, not just the one under scrutiny, what happens?" Straightforward to apply in new material. |
| 4 | Has observable failure modes | **PASS** | When absent: standards are applied selectively, producing asymmetric verdicts. Prosecution bias — one position is held to a standard that would destroy all positions equally. All four extractions independently named this failure mode. |
| 5 | Survives translation | **PASS** | Philosophy: "universalizability test on evaluative criteria." Law: "equal protection analysis." Statistics: "applying the same significance threshold to all hypotheses." Science: "does this methodology discriminate, or does it reject everything?" The core move — check whether your standard is being applied selectively — survives all translations. |
| 6 | Transforms epistemic state | **PASS** | Before: you believe a standard reveals something about the target. After: you discover the standard reveals nothing because it would produce the same verdict for everything. This transforms the epistemic landscape — the standard itself is now the finding, not the target's performance. |

### Taxonomy

**OPERATOR.** Not a heuristic (it produces a definite state transition: the standard is either symmetric or asymmetric). Not a rhetorical technique (it changes what the thinker knows, not how they communicate). It produces a binary diagnostic: this standard discriminates or it doesn't.

### Relationship to Existing Museum

Related to OP-006 (Under-Determination Detection): if a standard applies uniformly, it under-determines which framework is better. But Symmetry Testing is the **detection mechanism** — the specific cognitive move of applying the standard across all candidates to check. OP-006 names the condition; this operator names the action that reveals the condition. Not a duplicate.

### Verdict: **ADMIT as OP-008**

**Proposed name:** Symmetry Testing of Standards
**Proposed definition:** Test whether an evaluative standard, applied consistently across all candidates, produces discriminating results — or whether it collapses everything to the same verdict, revealing selective application rather than genuine assessment.
**Confidence:** RED (1 dig site — CFA transcripts only)
**Ext-Indep:** Partial (2 LLM extractors agree)

---

## Candidate 2: Concession Pricing

### Extraction Evidence

| Extractor | Transcript | Name Used | Present? |
|-----------|-----------|-----------|----------|
| Claude | v2 pilot (423K) | "Iterative Concession with Tracking" | Yes |
| Grok | v2 pilot (423K) | "Pricing concessions incrementally" | Yes |
| Claude | v2.1 MS (66K) | "Pricing Concessions Explicitly" | Yes |
| Grok | v2.1 MS (66K) | (not separately named — absorbed into other operators) | Partial |

**3.5/4 extractions.** Strong in both Claude extractions and Grok's v2 pilot. Grok's v2.1 extraction distributes concession behavior across other operators rather than naming it separately.

### Admission Evaluation

| # | Criterion | Verdict | Reasoning |
|---|-----------|---------|-----------|
| 1 | Describes an action | **PASS** | "When making a concession, explicitly name what changes and what doesn't, with a running tally." The thinker performs the pricing — it is an action. |
| 2 | Generalizes beyond domain | **PASS** | Negotiation (pricing each concession in contract terms), scientific debate (conceding specific experimental results while maintaining the theory), legal argument (stipulating facts while contesting interpretation), diplomatic negotiation. Concession-tracking applies wherever positions are contested and updated. |
| 3 | Is reusable | **PASS** | Any reasoner in a multi-round exchange can name what they've conceded, bound what the concession covers, and track cumulative movement. |
| 4 | Has observable failure modes | **PASS** | When absent: concessions are forgotten or overextended. Early-round movement gets relitigated. The conceding party appears to have abandoned more ground than they did. Without tracking, "I've already priced this" is indistinguishable from "I refuse to price this." |
| 5 | Survives translation | **MARGINAL** | Philosophy: "bounded concession with ledger." Negotiation: "itemized terms with running total." Legal: "stipulation with scope limitation." The core move survives, but some translations shade toward mere bookkeeping rather than a cognitive operation. |
| 6 | Transforms epistemic state | **MARGINAL** | After pricing a concession, you know the precise scope of what you've granted and what remains contested. This is a state change. But the transformation is organizational (knowing what you've already done) rather than substantive (discovering something new about the object). It manages deliberation more than it transforms understanding. |

### Taxonomy

**BORDERLINE — between operator and heuristic.** The pricing action does produce a state transition (bounded concession with tracked scope), but the state transition is about the deliberation process, not about the object of reasoning. Concession pricing is closer to a **deliberation management technique** than a cognitive operator that transforms what you know about the world.

Compare: OP-004 (Reconstruction Before Judgment) transforms your understanding of the object. Concession pricing transforms your understanding of the exchange. Both are genuine state transitions, but at different levels.

### Relationship to Existing Museum

No direct match. Touches OP-007 (Locate Disagreement Layer) in that pricing a concession requires knowing which layer you're conceding on. But the operation itself — bounding and tracking — is distinct.

### Verdict: **HOLD — Request second evaluation**

The case is genuinely close. Arguments for admission:
- 4/4 extraction convergence is strong evidence of a real pattern
- The failure mode is clearly observable and consequential
- It generalizes across domains

Arguments against:
- Criterion 5 (translation) is marginal — some translations reduce it to bookkeeping
- Criterion 6 (epistemic transformation) is marginal — it manages deliberation state, not world-knowledge
- The taxonomy classification is ambiguous — may be a heuristic that guides multi-round exchanges

**Recommendation:** Park as a named candidate. If future dig sites recover this operation independently (e.g., in Pearl's causal reasoning or in legal argumentation), revisit. The multi-extractor convergence is real signal — the question is whether the signal is "operator" or "high-quality heuristic."

---

## Candidate 3: Distinguishing Contested from Defeated

### Extraction Evidence

| Extractor | Transcript | Name Used | Present? |
|-----------|-----------|-----------|----------|
| Claude | v2 pilot (423K) | "Distinguishing Tension from Contradiction" | Yes |
| Grok | v2 pilot (423K) | "Distinguishing contested from failed" | Yes |
| Claude | v2.1 MS (66K) | "Distinguishing Pressure from Defeat" | Yes |
| Grok | v2.1 MS (66K) | "Distinguishing logical from evidential pressure" | Partial overlap |

**3.5/4 extractions.** Core operation clearly present in all four. Grok's v2.1 extraction captures a related but narrower version (logical vs evidential pressure is one instance of the contested/defeated distinction).

### Admission Evaluation

| # | Criterion | Verdict | Reasoning |
|---|-----------|---------|-----------|
| 1 | Describes an action | **PASS** | "Separate the claim that something is under pressure from the claim that it has been refuted." The thinker performs the separation — it is an action. |
| 2 | Generalizes beyond domain | **PASS** | Science (a theory with anomalies vs a falsified theory — Kuhn's normal vs revolutionary science), medicine (a finding under review vs a retracted finding), law (a challenged precedent vs an overturned one), politics (a contested policy vs a repealed one). The distinction between "under pressure" and "defeated" applies in every evaluative domain. |
| 3 | Is reusable | **PASS** | Any reasoner facing an objection can ask: "Does this show the position is wrong, or does it show the position faces a hard problem?" Extremely reusable. |
| 4 | Has observable failure modes | **PASS** | When absent: every unresolved difficulty is treated as a refutation. Hard problems become automatic disqualifiers. Frameworks with open questions score zero. All four extractions named this failure mode independently. |
| 5 | Survives translation | **PASS** | Philosophy: "pressure vs defeat." Science: "anomaly vs falsification." Law: "challenged vs overturned." Medicine: "under review vs retracted." Statistics: "p=0.06 vs p<0.001." Every domain has the distinction between "this is difficult" and "this is dead." |
| 6 | Transforms epistemic state | **PASS** | Before: you treat an objection as having destroyed a position. After: you recognize the position faces genuine difficulty but remains live. This transforms the space of live options — the contested position stays in the epistemic landscape instead of being prematurely eliminated. That is a substantive state change about what's still worth investigating. |

### Taxonomy

**OPERATOR.** Produces a definite state transition: the position moves from "eliminated" to "contested but live" (or vice versa). Not a heuristic (it's not a search strategy — it's a classification that changes what you do next). Not a rhetorical technique (it changes what the thinker believes about the position's status, not how they communicate it).

### Relationship to Existing Museum

Related to OP-006 (Under-Determination Detection): a contested position is one where the evidence under-determines whether it's true or false. But OP-006 is about formalisms under-determining outcomes. Contested≠Defeated is about **calibrating damage** — correctly pricing how much an objection actually costs a position. Different operation, related territory.

May also relate to a potential future operator about distinguishing degrees of epistemic damage (objection, anomaly, tension, pressure, challenge, refutation, defeat). Contested≠Defeated is the binary case; a granular version might subsume it. Worth watching for decomposition evidence.

### Verdict: **ADMIT as OP-009**

**Proposed name:** Contested ≠ Defeated
**Proposed definition:** Separate the claim that a position faces genuine difficulty from the stronger claim that it has been refuted — refusing to treat open problems as automatic disqualifiers.
**Confidence:** RED (1 dig site — CFA transcripts only)
**Ext-Indep:** Partial (2 LLM extractors agree)

---

## Summary

| Candidate | Criteria Passed | Verdict | Proposed ID |
|-----------|----------------|---------|-------------|
| Symmetry Testing of Standards | 6/6 | **ADMIT** | OP-008 |
| Concession Pricing | 4/6 (2 marginal) | **HOLD** | — |
| Contested ≠ Defeated | 6/6 | **ADMIT** | OP-009 |

Two operators admitted to the Museum at RED confidence. One held as a named candidate pending further evidence. The held candidate (Concession Pricing) has strong extraction evidence — the question is whether it's an operator or a high-quality deliberation heuristic. Future dig sites will resolve this.

---

## Rediscovery Evaluation: OP-007 (Locate Disagreement Layer)

Two of the five stable operators were classified as rediscoveries of OP-007. Evidence:

### Metric/Dimension Separation → OP-007

| Extractor | Name | Core move |
|-----------|------|-----------|
| Claude (v2) | "Separating Metric Domains" | Insisting a challenge to one metric doesn't score on another |
| Grok (v2) | "Distinguishing metrics from one another" | Separating evaluative dimensions |
| Claude (v2.1) | "Separating Measurement Dimensions That Are Conflated" | Identifying when a metric measures two things simultaneously |
| Grok (v2.1) | "Distinguishing content from grounding" | Separating presence of concepts from justificatory success |

This IS OP-007 applied to CFA's metric architecture. The disagreement layer is "which metric are we actually scoring?" When absent, the failure mode is Layer Confusion — treating an MS objection as a BFI verdict, exactly the failure OP-007 predicts. Also touches OP-001 (the metric representation vs the thing being measured).

**Verdict:** Rediscovery of OP-007. Update Ledger with CFA evidence, evidence type: Multi-extractor convergence (Pressure-tested).

### Meta-Dispute Identification → OP-007

| Extractor | Name | Core move |
|-----------|------|-----------|
| Claude (v2) | "Naming Category Drift in an Opponent's Argument" | Identifying when the question being answered has shifted |
| Grok (v2) | "Diagnosing metric-definition disputes" | Identifying when disagreement is about what a metric measures |
| Claude (v2.1) | "Identifying When Further Exchange Is Non-Productive" | Recognizing iteration vs genuine engagement |
| Grok (v2.1) | "Identifying meta-disputes over metrics" / "Naming the precise impasse" | Isolating standards disagreements from factual ones |

This IS OP-007 at the meta-level: the disagreement isn't about the object (the framework being scored) but about the instrument (what the metric means). Locating this layer is exactly OP-007's operation.

**Verdict:** Rediscovery of OP-007. Same Ledger update.

---

*Evaluation completed: 2026-07-08*
*Evaluator: Repo (Claude Opus 4.6)*
