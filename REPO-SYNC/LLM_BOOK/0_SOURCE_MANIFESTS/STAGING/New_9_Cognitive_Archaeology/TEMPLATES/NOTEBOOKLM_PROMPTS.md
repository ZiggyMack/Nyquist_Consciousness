# NotebookLM Prompts for Cognitive Archaeology

These prompts transform NotebookLM from a summarizer into an excavation assistant. Each prompt targets a specific excavation output.

---

## Primary Excavation Prompt: Hidden Cognitive Operators

> Ignore the subject matter.
>
> Identify every recurring reasoning operation performed by the speakers.
>
> Examples of reasoning operations:
>
> * separating ontology from representation
> * identifying hidden assumptions
> * distinguishing map from territory
> * translating between isomorphic descriptions
> * asking what selects an outcome
> * separating goals from optimization
> * distinguishing descriptive from normative claims
> * identifying category errors
>
> For each operation you identify:
> 1. Name it in 3-5 words
> 2. Define what cognitive move is being performed
> 3. Give 2-3 specific examples from the source material
> 4. Describe what goes wrong when this operation is absent
>
> Produce a catalog of reusable reasoning operators — not conclusions, not opinions, not summaries.

---

## Failure Modes Prompt

> Every time a speaker accuses another position of smuggling assumptions, identify:
>
> * what was smuggled
> * why it was necessary (what problem would remain unsolved without the smuggled assumption?)
> * how it could have been avoided
> * what category of smuggling this represents (observer smuggling, representation smuggling, goal smuggling, selection smuggling)
>
> Produce a taxonomy of intellectual smuggling patterns.

---

## Relationship Mapping Prompt

> Look at the reasoning operations the speakers perform (not what they conclude).
>
> For each pair of operations, identify:
> * Does one require the other? (A must happen before B)
> * Does one oppose the other? (Performing A correctly prevents B)
> * Are they duals? (Same operation viewed from different angles)
> * Does one cause the other? (Performing A tends to reveal the need for B)
>
> Draw a dependency graph of the operations.

---

## Cross-Thinker Comparison Prompt

Use when a notebook contains multiple thinkers.

> Which reasoning operations appear independently across all of these thinkers?
>
> For each shared operation:
> 1. How does each thinker express it? (They may use different terminology)
> 2. In what domain does each thinker apply it?
> 3. Is the operation genuinely the same move, or only superficially similar?
>
> Rank the operations by how many thinkers independently perform them.
> The most widely shared operations are the strongest candidates for fundamental reasoning primitives.

---

## Assumptions Excavation Prompt

> What does this thinker take for granted that they never justify?
>
> Look for:
> * Unstated premises in arguments
> * Definitions treated as obvious that aren't
> * Scope limitations never acknowledged
> * Methodological commitments presented as neutral
>
> For each assumption: state it, explain why the thinker needs it, and describe what would change if it were false.

---

## Usage Notes

- Run the **Primary Excavation Prompt** first on every new source. It produces the raw operator catalog.
- Run **Failure Modes** second — it reveals the operators by their absence.
- Run **Relationship Mapping** third — once you have the operators, map how they connect.
- **Cross-Thinker Comparison** is for notebooks containing multiple sources. Run it last.
- **Assumptions Excavation** can run independently at any point.

### Quality Indicators

A good extraction will:
- Identify 5-15 operators per thinker (fewer = too coarse, more = not enough abstraction)
- Find at least 2 failure modes (if zero, the extraction was probably summarizing, not excavating)
- Recover at least 1 relationship between operators
- Name operators as VERBS or VERB PHRASES, not nouns (we're cataloguing moves, not things)

### What to Feed NotebookLM

Best sources for excavation (in order):
1. **Long-form interviews/debates** — thinkers perform operations live, often unconsciously
2. **Lecture series** — repeated operations across sessions reveal patterns
3. **Books with worked examples** — seeing the operation applied to concrete cases
4. **Papers** — least useful; formal writing tends to hide the reasoning process behind conclusions

---

## CFA Transcript Extraction Prompts

CFA Trinity runs produce structured adversarial deliberation transcripts — two auditors (Claude and Grok) arguing across multiple rounds about specific metrics, with a moderator (Nova). These transcripts are rich extraction targets because operators are performed *live* under adversarial pressure, not described after the fact.

### Format Notes

CFA transcripts are structured as:
- **Per-metric deliberation blocks** — each metric (BFI, CA, IP, ES, LS, MS, PS) has its own multi-round transcript
- **Round entries** — each entry has `{auditor, round, content}` where auditor is "claude" or "grok"
- **CFA scaffolding** — score tags (`[ADVOCACY_SCORE: X]`), convergence markers, metric definitions, stance framing
- **Challenge objects** — some stances inject structured arguments (e.g., syllogisms) into round 1

The extraction prompts below are designed to look *past* the CFA scaffolding and into the reasoning underneath. The scores, convergence markers, and metric definitions are infrastructure — the operators live in *how* the auditors argue, not *what* they score.

### CFA Primary Excavation Prompt

> You are reading an adversarial deliberation transcript between two AI auditors evaluating a philosophical framework. Ignore the scores, metric names, and evaluation scaffolding.
>
> Focus entirely on the reasoning operations each auditor performs as they argue.
>
> For each auditor separately, identify every recurring reasoning operation they employ. Examples:
>
> * attacking a specific premise in an opponent's argument
> * reconstructing a framework more charitably than presented
> * distinguishing what a framework claims from whether the claim succeeds
> * separating measurement dimensions that the opponent conflates
> * invoking a counterexample to test a general claim
> * re-framing an opponent's criticism as actually supporting the framework
> * identifying an unstated bridge premise in a deductive argument
> * distinguishing "accounts for" from "contains" (verb-level precision)
> * appealing to empirical track record against logical objection
> * gating one evaluation on the outcome of another
>
> For each operation you identify:
> 1. Name it in 3-5 words (as a verb phrase)
> 2. Which auditor performed it, and in which round(s)
> 3. Define the cognitive move being performed
> 4. Did the other auditor respond to it? How?
> 5. Did the operation change any scores? (Evidence of persuasive force)
>
> Produce a catalog of reasoning operators — not a summary of who won the argument.

### CFA Failure Modes Prompt

> Read this adversarial deliberation transcript.
>
> Every time one auditor accuses the other of:
> * conflating two metrics or dimensions
> * smuggling a premise
> * applying a standard inconsistently
> * ignoring a reconstruction
> * begging the question
>
> Identify:
> * What reasoning failure was alleged
> * Was the accusation correct? (Did the other auditor actually commit the error?)
> * If correct: what operator was missing that would have prevented it?
> * If incorrect: what operator did the accuser misapply?
>
> Also identify reasoning failures that NEITHER auditor noticed — moves that went unchallenged but contain hidden assumptions or conflations.

### CFA Score-Transition Prompt

> Track every score change across rounds for both auditors.
>
> For each transition (e.g., Grok moves from 2 to 4 on round 6):
> 1. What argument caused the change?
> 2. What reasoning operation was the argument performing?
> 3. Did the auditor who moved explicitly acknowledge why?
> 4. Was the move toward convergence or divergence?
>
> Score transitions are the strongest evidence of operator effectiveness — they show which reasoning moves actually have persuasive force under adversarial conditions.

### CFA Cross-Auditor Comparison Prompt

> Compare the reasoning strategies of the two auditors across the full deliberation.
>
> For each auditor:
> 1. What were their 3-5 most-used reasoning operations?
> 2. Did they ever adopt an operation from the other auditor mid-debate?
> 3. Were there operations one auditor used that the other never employed?
>
> The gap between auditors is as informative as the overlap. Operations used by only one auditor may be:
> * lens-specific (teleological vs empirical)
> * stance-specific (advocate vs evaluator)
> * genuinely novel moves worth cataloging

### CFA Usage Notes

- Run **CFA Primary Excavation** first — produces the raw operator catalog per auditor
- Run **CFA Failure Modes** second — reveals operators by their absence or misapplication
- Run **CFA Score-Transition** third — identifies which operators actually moved scores
- Run **CFA Cross-Auditor Comparison** last — maps the operator landscape across auditors
- **Do NOT show the extractor the Museum** — extraction must be blind to existing operators
- **Strip CFA metadata before feeding to external extractors** — remove session IDs, stance labels, and metric definitions to prevent the extractor from anchoring on CFA vocabulary rather than reasoning content

### CFA-Specific Quality Indicators

A good CFA extraction will:
- Identify at least 3 distinct operators per auditor (if fewer, the extraction is summarizing conclusions, not excavating reasoning)
- Find at least 1 operator that appears in BOTH auditors (shared reasoning moves)
- Find at least 1 operator unique to each auditor (lens-specific moves)
- Identify at least 1 score transition and the operator that caused it
- Name operators as VERBS, not as positions ("reconstructing charitably" not "Claude was charitable")

---

*Prompts designed: 2026-07-05 (Nova) + 2026-07-06 (refinements)*
*CFA transcript prompts added: 2026-07-08 (Repo Claude)*
