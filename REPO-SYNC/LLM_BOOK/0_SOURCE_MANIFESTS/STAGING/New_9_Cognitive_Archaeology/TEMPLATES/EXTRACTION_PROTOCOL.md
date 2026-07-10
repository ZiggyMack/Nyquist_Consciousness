# Cognitive Architecture Extraction Protocol

**Version:** 1.0 (Barandes Protocol)
**Origin:** Developed during Dig Site 002 (Barandes "No Time" interview extraction)
**Purpose:** Replicable template for extracting the cognitive architecture of any thinker from source material

---

## Overview

This protocol extracts three artifacts from a thinker's work:

- **Artifact A:** The theory/content (what they said)
- **Artifact B:** The cognitive architecture that produced it (how they think)
- **Artifact C:** This protocol itself (the methodology that recovers B)

Artifact B is the primary target. Artifact A is the input. Artifact C is what you're reading.

---

## Prerequisites

- Source material: transcript, paper, lecture, interview (longer is better — 3+ hours ideal)
- NotebookLM (or equivalent LLM-based mining tool) loaded with the source
- Familiarity with the Operator Museum (to check for rediscoveries)
- The O/I/H epistemic layering discipline (see below)

---

## The 6-Level Inquiry Stack

Questions are organized by altitude. Lower levels must be saturated before escalating.

| Level | Name | Question Type | Example |
|-------|------|---------------|---------|
| 0 | Facts | What did they say? | "What is [THEORY]?" |
| 1 | Mechanism | How does the theory work? | "How does [MECHANISM] produce [PREDICTION]?" |
| 2 | Architecture | How is the theory organized? | "What are the structural dependencies between [CONCEPT_A] and [CONCEPT_B]?" |
| 3 | Discovery | How did they think? | "What cognitive operators does [THINKER] deploy?" |
| 4 | Transfer | Where else would this work? | "Where would [OPERATOR] produce new results outside [DOMAIN]?" |
| 5 | Operating System | What's the reusable machinery? | "What would [THINKER] contribute to an Epistemic Operating System?" |

**Rule:** Levels 0-2 are content extraction. Levels 3-5 are cognitive architecture extraction. The transition from Level 2 to Level 3 requires Altitude Escalation (OP-010).

---

## The 6-Pass Extraction Pipeline

Each pass extracts a different layer from the same source material.

### PASS 0: Historical Contingency

> "Why didn't this appear fifty years earlier?"

Ask: What institutional habits, inherited pedagogy, false dichotomies, or representation lock-in prevented this discovery? What hidden assumptions of the discipline (not just the theory) does the thinker expose?

This pass extracts the **discipline's** cognitive architecture, not the thinker's.

### PASS A: Knowledge Extraction

> "What did they say?"

Standard content mining. Extract claims, definitions, arguments, evidence. Levels 0-1.

### PASS B: Structural Extraction

> "How is the theory organized?"

Map dependencies, hierarchies, prerequisites. What concepts require what other concepts? Where are the load-bearing assumptions? Level 2.

### PASS C: Cognitive Extraction

> "How did they think?"

The primary target. Extract cognitive operators: what moves does the thinker make repeatedly? What heuristics do they apply? What do they refuse to do? Level 3.

#### The Noether Lens (PASS C sub-protocol)

Apply to every thinker during PASS C. Not a separate pass — a lens that sharpens cognitive extraction by asking what the thinker treats as invariant vs representational:

1. **What transformations did they consider admissible?** (What were they willing to change?)
2. **What did they refuse to let change?** (What did they treat as invariant?)
3. **Which invariants generated their theory?** (Did invariance drive the discovery, or merely describe the result?)
4. **Which assumed invariants did they destroy?** (Which things the field treated as fundamental turned out to be representational?)
5. **Which representations turned out to be accidental rather than essential?**

The key distinction: invariants can be *outputs* of finished theories (descriptive) or *tools* for discovering new theories (generative). Noether's contribution is the claim that invariance-seeking is a **discovery strategy**, not just a bookkeeping method. If a thinker uses invariance generatively, that's a candidate for the Invariant Discovery operator family.

### PASS D: Transfer Extraction

> "Where else would this operator work?"

For each operator recovered in PASS C, ask: in what other domains would this operator produce new results? Level 4.

### PASS E: EOS Extraction

> "What would they contribute to an Epistemic Operating System?"

What reusable reasoning machinery emerges? What operator families? What methodological principles? Level 5.

### PASS Ω: Protocol Evolution

> "What changed about the extraction protocol because of this dig site?"

Fires at close of every dig site. Asks: What methodology revisions does this extraction demand? What worked that we didn't expect? What failed that we thought would work? What new tools, formats, or practices should future dig sites adopt?

PASS 0 and PASS Ω are symmetric: PASS 0 looks backward at the THINKER's discipline (what hidden assumptions sustained the blind spot?). PASS Ω looks backward at the EXTRACTOR's methodology (what hidden assumptions of our own protocol did this dig site expose?).

Output: a versioned revision log for the extraction protocol itself.

---

## Question Template (50 Questions)

Replace `[THINKER]`, `[THEORY]`, `[DOMAIN]`, `[MECHANISM]`, `[KEY_CONCEPT]` with subject-specific content.

### Level 0-1: Content Extraction (Q1-Q6)

1. What is [THEORY]? Extract the complete mechanism — not a summary, but the actual structure.
2. How does [MECHANISM] reproduce the standard results in [DOMAIN]? Walk through the bridge step by step.
3. How does [THEORY] resolve the central problem of [DOMAIN]? What specifically dissolves?
4. What are [THEORY]'s acknowledged limitations? Where does [THINKER] draw the boundary of what the theory can and cannot do?
5. How does [THEORY] compare to the leading alternatives? What does each get right, wrong, and leave open?
6. What is the relationship between [THEORY] and [RELATED_FRAMEWORK]? Does [THEORY] subsume, complement, or contradict it?

### Level 1-2: Architecture (Q7-Q15)

7. What is [THINKER]'s position on [ONTOLOGICAL_QUESTION]? Extract the full taxonomy, not just the position.
8. Extract [THINKER]'s evaluation criteria for [DOMAIN]. What are the minimum requirements? What would disqualify a candidate?
9. What is the relationship between [CONCEPT_A] and [CONCEPT_B] in [THEORY]? Does one explain the other?
10. How does [THEORY] handle [EDGE_CASE]? Does it produce unambiguous predictions?
11. Extract the full structure of [THINKER]'s critique of [ALTERNATIVE_THEORY]. Separate the argument into: premises, logic, conclusion, and what would change their mind.
12. Apply [THINKER]'s own evaluation criteria to [THEORY] itself. Where does it pass? Where does it have acknowledged gaps?
13. What role does [MATHEMATICAL_STRUCTURE] play in [THEORY]? Is it essential or representational convenience?
14. What is [THINKER]'s position on [PHILOSOPHICAL_QUESTION]? Extract the argument, not just the conclusion.
15. **CRITICAL — Cognitive Operator Extraction:** What specific cognitive moves, reasoning strategies, and analytical habits does [THINKER] deploy throughout this material? List every identifiable operator: how they test claims, how they construct arguments, how they evaluate alternatives, what they refuse to do. This is the bridge from content to cognitive architecture.

### Level 2-3: Cross-Pollination (Q16-Q20)

16. Does [KEY_CONCEPT_A] in [THEORY] parallel [KEY_CONCEPT_B] in [EXTERNAL_FRAMEWORK]? If so, is the parallel structural or superficial?
17. Can [THEORY]'s temporal/structural framework be applied to [EXTERNAL_DOMAIN]? What would that look like concretely?
18. Does [THEORY]'s [METHODOLOGICAL_PRINCIPLE] transfer to [EXTERNAL_FRAMEWORK]'s methodology?
19. Does [THEORY] genuinely escape [KNOWN_PROBLEM] or does it smuggle in the same assumptions under different names? Perform a circularity audit.
20. If [CONCEPT_FROM_ROUND_1] maps onto [CONCEPT_FROM_THEORY], what does that tell us about the underlying structure they share?

### Level 3-4: Meta-Scientific (Q21-Q35)

21. Is [STANDARD_FORMALISM] a lossy compression of [THEORY]? What information is lost? What artifacts does the compression introduce?
22. What features of [THEORY] are representation-invariant vs representation-dependent? Can you distinguish them?
23. What is the cost of [THEORY]'s representational simplification? What does the simpler representation make harder to see?
24. What is the status of [FUNDAMENTAL_CONCEPT] in [THEORY] — primitive, derived, or assumed?
25. What is the ontological status of [THEORY]'s laws — are they generators, descriptions, or something else?
26. Why does [THEORY] use [MATHEMATICAL_TOOL]? Is there a deeper reason, or is it historical accident?
27. What kind of information is created/destroyed at [KEY_EVENT]? Is this epistemic or ontological?
28. Does [MATHEMATICAL_FRAMEWORK] keep appearing in [THEORY] for structural reasons? What would a category-theoretic analysis reveal?
29. Can [KEY_CONCEPT] be interpreted as an interface between systems rather than a property of either system?
30. What hidden criteria does [THINKER] apply that they never explicitly state? What unstated evaluation standards shape their judgments?
31. What in [THEORY] must be true for mathematical reasons vs what happens to be true empirically?
32. What dead assumptions has [THINKER] identified that [DOMAIN] inherited without examination? What cognitive habits does the field carry that no longer serve it?
33. **CRITICAL — Discovery Operator:** What is the specific cognitive procedure [THINKER] used to arrive at [THEORY]? Not the history — the transferable method. If someone wanted to make a similar discovery in [OTHER_DOMAIN], what steps would they follow?
34. What made [THEORY] invisible to everyone else for so long? What systematic blind spots prevented its discovery? What does this reveal about how [DOMAIN] filters what it can see?
35. **CRITICAL — Subtractive Discovery Catalogue:** Catalogue every instance where [THINKER] discovers something by removing structure rather than adding it. What was removed? What survived? What was revealed by the removal?

### Level 4-5: Cross-Framework Bridges (Q36-Q41)

36. How does [THINKER] use philosophy? Is it a tool, a constraint, a prerequisite, or a byproduct?
37. If [EXTERNAL_FRAMEWORK] is modeled as [THEORY], what testable predictions emerge? Be specific — what experiments would you run?
38. Does [ONTOLOGICAL_POSITION] in [THEORY] have a formal mathematical equivalent in [EXTERNAL_FRAMEWORK]?
39. Does [THEORY]'s pattern for [PROCESS] generalize beyond [DOMAIN]? Where would the same pattern produce new results?
40. What general methodology for [DOMAIN]-level discovery does [THINKER]'s work reveal? Extract everything about the process of finding what nobody was looking for.
41. Are [THEORY]'s core quantities system-intrinsic or pair-dependent? If System A interacts with Environment B vs Environment C, does it develop the same distributions or different ones? What does this imply about the ontology of [THEORY]'s laws?

### Level 5: Invariance Extraction — The Noether Questions (Q42-Q49)

42. [THINKER] identifies [INFLUENCE] as profoundly important. Beyond [INFLUENCE]'s specific results, what cognitive or methodological lesson does [THINKER] believe their work teaches? Is the central insight the theorem/result itself, or is there a deeper discovery strategy that practitioners should emulate?
43. Does [THINKER] treat invariants as outputs of a successful theory, or as tools for discovering new theories? In their own development of [THEORY], did they begin by searching for quantities or structures that should remain invariant under changes of representation? If so, what were those invariants?
44. How does [INFLUENCE]'s emphasis on symmetry and invariance relate to [THINKER]'s emphasis on multiple representations? Are these separate ideas, or does [THINKER] see representation changes as a way of exposing deeper invariants?
45. In [THINKER]'s account, which concepts in [DOMAIN] were mistakenly treated as invariant when they were actually artifacts of a particular representation? How did identifying these false invariants enable [THEORY]?
46. Suppose a scientist wanted to discover the next major advance outside [DOMAIN] using the methodological lessons [THINKER] attributes to [INFLUENCE]. What concrete procedure would that scientist follow? Can the approach be expressed as a general algorithm for scientific discovery?
47. Does [THINKER] suggest that [INFLUENCE]'s methodology of searching for symmetries and invariants could apply outside [DOMAIN] — to biology, cognition, mathematics, or philosophy — or is it fundamentally tied to [DOMAIN]? What reasons does [THINKER] give either way?
48. What assumptions would prevent a researcher from thinking in [INFLUENCE]'s way? Does [THINKER] identify habits of thought that naturally cause scientists to focus on representations instead of invariants? If not explicitly, what habits are implied by the discussion?
49. Imagine [INFLUENCE] were collaborating directly on the design of an Epistemic Operating System whose purpose was to discover new knowledge across disciplines. Based on [THINKER]'s discussion of their work, what single cognitive operator would [INFLUENCE] insist every investigator use? How would that operator function in practice, and how does [THINKER]'s own [THEORY] research exemplify it?

### Level 5+: Meta-Extraction — Discovery Architecture (Q50)

50. **CRITICAL — Source Discovery:** Given the discovery strategies, cognitive operators, and methodological principles extracted from [THINKER] across this entire inquiry, what other thinkers, texts, interviews, or source materials would be most valuable to subject to this same extraction protocol? Identify candidates where: (a) their cognitive architecture is likely to be qualitatively different from [THINKER]'s, (b) their methodology has produced discoveries that practitioners in their field find surprising or hard to explain, and (c) the extraction is likely to reveal operators not yet in the Museum. Rank candidates by expected operator yield, not fame.

---

## Epistemic Layering (O/E/T/H)

Every insight must be tagged:

- **O (Observed):** What [THINKER] explicitly says or demonstrably does — direct quotes, specific examples
- **E (Extracted):** What cognitive operator best explains the observation. Phrased as extraction ("repeatedly does X" → candidate: OP-NNN)
- **T (Transfer):** Where the operator plausibly applies outside [THINKER]'s domain. Must specify mechanism ("...via the mechanism of ___")
- **H (Hypothesis):** Testable prediction generated by the transfer

This discipline prevents over-claiming. O grounds E. E must name a candidate operator. T requires an explicit mechanism (not just a domain name). H must be falsifiable.

HIGH VALUE insights also get an **Alternative Interpretation** — the strongest counter-reading that doesn't violate the observation.

### Notation Convention

Apply consistently across INSIGHTS, CONNECTIONS, and EXPERIMENTS:

- `≅` structural isomorphism (same topology, different ontology) — e.g., "CFA Phase 1 ≅ ISP interaction phase"
- `=` identity (same object, different descriptions) — use sparingly, only where literally true
- `→` generative (one produces the other) — e.g., "interaction → conditioning opportunity"

---

## Operator Family Classification

Every recovered operator gets two labels:

1. **The specific operator** (e.g., Subtractive Discovery)
2. **The family** (e.g., Minimal Sufficiency Operator)

Known families:

| Family | Definition | Examples |
|--------|-----------|----------|
| Translation | Move between equivalent representations | OP-001 Representation ≠ Ontology, OP-004 Reconstruction Before Judgment, OP-014 Ontological Downgrading |
| Information | Manage what is known, unknown, or askable | OP-010 Altitude Escalation, OP-013 Epistemic Boundary Setting, OP-015 Question Completion |
| Minimal Sufficiency | Remove until only what's needed remains | OP-011 Subtractive Discovery |
| Blind Spot | Detect what's hidden, missing, or smuggled | OP-006 Under-Determination Detection, OP-002 Hidden Selection Audit, OP-005 Hidden Structure Injection |
| Constraint-Induced Discovery | Use limitations as discovery tools | OP-012 Pedagogical Forcing, OP-003 Goal → Optimization Collapse, OP-008 Symmetry Testing |

New families may emerge from future dig sites.

---

## Recursion: The Question Completion Operator

After each round of answers, apply OP-015 (Question Completion):

> Generate the smallest set of higher-order questions whose answers would maximally increase understanding.

This creates the recursive meta-cycle:

```text
Extract theory → compress → apply Question Completion →
extract at new level → compress → apply Question Completion →
repeat until no genuinely new level emerges
```

**Termination condition:** When generated questions are structurally equivalent to previous questions in different vocabulary, the inquiry is saturated at that altitude.

### Source Discovery (Q50) — Recursion Fuel

**MANDATORY:** Every dig site extraction MUST end with Q50 (Source Discovery). This question asks the current extraction to identify the next highest-yield sources for the protocol — ranked by expected operator yield, not fame. The extraction recommends its own next inputs.

This makes the protocol self-fueling:

```text
Dig Site N extraction
  → Q50 identifies highest-yield sources for Dig Site N+1
  → Dig Site N+1 extraction
  → Q50 identifies highest-yield sources for Dig Site N+2
  → ...
```

Q50 answers accumulate across dig sites. When multiple extractions independently recommend the same thinker, that convergence is strong signal — prioritize those candidates. When a recommended candidate has a qualitatively different cognitive architecture from all previous dig site subjects, that's the negative control opportunity.

---

## Museum Integration

After extraction:

1. Check each recovered operator against existing Museum entries for rediscoveries
2. Rediscoveries add provenance to existing entries (increase confidence)
3. Genuinely new operators get Museum entries at RED confidence
4. Run `extract_operators.py` against source material for multi-extractor validation (optional but strengthens confidence)

---

## Applying to Next Thinker

1. Load source material into NotebookLM
2. Replace all `[PLACEHOLDERS]` in the Q1-Q50 template with subject-specific content
3. Run PASS 0 first (historical contingency) — this is often the highest-value pass
4. Run PASS A-B (content + structure) via Q1-Q14
5. Run PASS C (cognitive extraction) via Q15 + Noether Lens — this is the bridge question
6. Run PASS D-E (transfer + EOS) via Q16-Q41
7. Run Noether extraction via Q42-Q49 (invariance as discovery method)
8. Apply Question Completion to generate next round
9. **ALWAYS** run Q50 (Source Discovery) — this seeds the next dig site
10. Run PASS Ω (protocol evolution) — what changed about the methodology
11. Integrate into Museum with proper provenance and confidence levels

**Candidate next subjects:** Hoffman (consciousness-first), Adlam (solo), Tegmark (mathematical universe), Pearl (causal inference), Jaynes (maximum entropy), Dennett (heterophenomenology)

**Recommended Dig Site 003 design:** Include a negative control — a thinker where the protocol should STRUGGLE. This demonstrates discriminative power: if PASS 0 extracts 6 dead assumptions from every thinker regardless of domain, it's pattern-matching, not discovering. Choose a thinker whose cognitive architecture is expected to be qualitatively different from Barandes' (e.g., a creative synthesizer rather than a subtractive discoverer).

---

*Protocol version 1.2 — upgraded from Dig Site 002 extraction*
*Version 1.0 created: 2026-07-10*
*Version 1.1 changes: O/I/H → O/E/T/H, counter-readings, ≅ notation convention, PASS Ω added, negative control recommendation*
*Version 1.2 changes: Noether Lens added to PASS C, Q42-Q49 (invariance extraction), Q50 (source discovery for next dig site), template expanded 41→50 questions*
