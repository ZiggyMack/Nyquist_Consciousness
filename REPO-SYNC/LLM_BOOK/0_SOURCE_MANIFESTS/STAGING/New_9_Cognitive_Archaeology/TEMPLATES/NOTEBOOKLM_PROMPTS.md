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

*Prompts designed: 2026-07-05 (Nova) + 2026-07-06 (refinements)*
