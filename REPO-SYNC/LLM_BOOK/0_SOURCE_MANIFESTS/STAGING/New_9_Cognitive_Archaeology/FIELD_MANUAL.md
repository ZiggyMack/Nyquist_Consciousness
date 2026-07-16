# Cognitive Archaeology — Field Manual

> **Ideas are the artifacts. Reasoning operators are the fossils of thought.**

We don't excavate philosophers because we're interested in their conclusions. We excavate their conclusions because they reveal the machinery that produced them.

---

## Framing

This project investigates an **underexplored synthesis** — the hypothesis that thinkers across disciplines perform the same small set of reasoning operations, and that nobody has unified these into one operator framework. That hypothesis is testable: if new thinkers consistently rediscover the same operators, the synthesis is real. If they don't, it isn't. Note: the H-baseline result established that operator *presence* is universal across competent reasoning — the discriminating signal lives in *which* operators a thinker selects, in what *order*, and what they *skip*.

We do not claim novelty. We claim the synthesis appears underexplored. Adjacent work may exist in cognitive science, AI interpretability, philosophy of reasoning, argumentation theory, or epistemology. If found, those become evidence, not threats.

---

## The Core Confound

> **Can you separate operators that are in the thinkers from operators that are in the reader?**

Every dig site is read by an extractor (LLM or human). Every "reasoning operator" is extracted by an extractor. Every judgment of "these two thinkers perform the same operation" is made by an extractor. Convergence across thinkers is therefore confounded with convergence in how extractors represent reasoning. The null hypothesis for any cross-thinker match is not "these thinkers share a reasoning primitive" — it is "the same extractor, prompted the same way, produces the same descriptive vocabulary for two different texts."

This is the instrument-vs-object problem. It must be addressed before any finding is trustworthy. Phase 0 exists for this reason.

---

## Excavation Workflow

```
0. EXTRACTOR CALIBRATION  (Phase 0 — run once, before any real dig)
   ↓
1. SELECT DIG SITE
   ↓
2. EXCAVATE
   ↓
3. RECOVER ARTIFACTS
   ↓
4. CLASSIFY
   ↓
5. CROSS-REFERENCE
   ↓
6. ASSIGN CONFIDENCE
   ↓
7. PRESSURE TEST
   ↓
8. MUSEUM
```

### Phase 0: Extractor Calibration (Dig Site 000)

Before trusting any excavation, calibrate the instrument. Give the same source text to multiple independent extractors — different LLMs (Claude, GPT, Gemini, Grok), human coders from different disciplines (philosopher, mathematician, engineer) — without showing any of them the Museum. Compare results.

This is not a later refinement. It is the first experiment.

**What Phase 0 answers:**
- Do different extractors find the same operators? (Extractor agreement)
- Do extractors find operators in text that has no disciplined reasoning? (Negative controls)
- At what description grain do extractors converge? (Granularity calibration)

**Negative Control Battery:** Run the extraction prompt against shopping lists, weather reports, Twitter rants, pseudo-profound nonsense, and LLM hallucinations. If the Museum lights up on these, the extraction is generating operators, not detecting them. This is the placebo arm.

**Extractor Agreement:** No single extractor gets privileged status. Agreement across a heterogeneous extractor ecology is the signal. Track agreement rates and report them alongside every finding.

See `DIG_SITES/000_Extractor_Calibration/` for the experiment design.

### Step 1: Select Dig Site

Choose a thinker. Prefer sources where the thinker is PERFORMING reasoning live (interviews, debates, lectures) over sources where they REPORT conclusions (papers, books). Performing is where operators surface.

**Source Selection Heuristic (Phase 0A finding):** Shorter transcripts with stalls and impasses produce richer operator extraction than long convergent runs. Stall-induced metacognitive pressure forces explicit articulation of reasoning operations. Prioritize these when selecting from multiple available sources.

**Pre-flight: OP-006 Check.** Before committing to a dig site, apply Under-Determination Detection (OP-006) to the source: does the material actually determine the operators you'll extract, or are you importing them? OP-006 would have caught every false finding in the Test A postmortem (composition without noise floor, asymmetry without main effect). Ask: "What is the noise floor of this extraction?"

Create directory: `DIG_SITES/{NNN}_{Thinker_Name}/`

### Step 1b: Transcript Treatment (Standard)

Downloaded transcripts (YouTube / interview ASR exports) get the **Standard treatment** before excavation, so extractors read reasoning rather than transcription noise:

1. **Header** — prepend a provenance block: `Speaker`, `Type` (Lecture / Interview / Documentary), source `URL`, `Tier` (1 = the thinker's own voice; 1E = *about* the thinker), `Dig Site`, and a `Museum-blind: Yes` marker.
2. **Strip timestamps + reflow** — remove interleaved ASR timestamps (both `0:00`-on-its-own-line and inline `0:1414 seconds…` formats) and reflow into paragraphs.
3. **Light ASR correction** — fix obvious errors on key terms only (proper nouns / domain terms: Bohr, Sommerfeld, monopoles, Schrödinger). Do NOT rewrite the thinker's phrasing — faithfulness beats polish; operators survive minor ASR noise.
4. **Clean filenames** — rename to `{Thinker}_{Source}_{Topic}.md`.
5. **Dedupe** — for multiple uploads of the same source, keep the cleanest as canonical and move the rest to `_IN/_alt_transcriptions/` (preserved, but excluded from the extraction set to avoid double-counting).

Tier-1 (the thinker's own voice) is the highest-value extraction material — tag it so extraction weights it accordingly. PDFs / papers are source documents, not transcripts, and do not get this treatment.

### Step 2: Excavate

Run NotebookLM extraction using prompts from `TEMPLATES/NOTEBOOKLM_PROMPTS.md`. Always run the **Primary Excavation Prompt** (Hidden Cognitive Operators) first. Follow with Failure Modes and Relationship Mapping.

For manual excavation (reading without NotebookLM): read with the question "What cognitive move did they just perform?" not "What did they just say?"

### Step 2b: Abstention Detection (Run after PASS C)

After blind extraction is complete, run PASS F (museum-aware) to identify operators that were available but not deployed. This is the post-H-baseline instrument upgrade — operator presence saturates at competence, so the discriminating signal lives in what's MISSING, not what's present.

Show the extractor the full Museum catalog (INDEX.md). Ask which operators were relevant at each point in the text, which were used, and which were skipped. Classify each abstention (deliberate refusal, competing priority, or true omission). See `TEMPLATES/NOTEBOOKLM_PROMPTS.md` for the Abstention Detection Prompt.

PASS F output feeds directly into Test B (sequence_analysis.py) as omission data.

### Step 3: Recover Artifacts

Four outputs from every dig:

1. **Operators** — reasoning moves the thinker performs repeatedly
2. **Failure modes** — what goes wrong when an operator is absent or misapplied
3. **Assumptions** — hidden premises the thinker relies on
4. **Relationships** — how operators connect, cause, or oppose each other

Document in `DIG_SITES/{NNN}/excavation.md` using the template.

### Step 4: Classify

Each recovered operator must pass the **Admission Criteria** (see below). If it doesn't pass, it's an observation, not an operator. Don't force it.

### Step 5: Cross-Reference

Check whether each operator already exists in the Museum. Three outcomes:

- **Match:** The operator is a rediscovery. Record the new dig site in the existing operator's provenance chain. Update confidence.
- **Partial match:** The operator overlaps with an existing one. Decide: is it the same operator expressed differently, or a genuinely distinct operation?
- **No match:** New operator. Register it in the Museum with RED confidence.

### Step 6: Assign Confidence

Update `LEDGER.md`. Confidence levels:

| Level | Criteria |
|-------|----------|
| GREEN — Confirmed | 5+ independent thinkers |
| YELLOW — Candidate | 2-4 independent thinkers |
| RED — Hypothesis | 1 thinker only |

**Evidence type matters.** Track whether each confirmation is:
- **Independent** — thinker discovered the operator without reference to our framework or other thinkers in the registry
- **Synthetic** — we identified the operator by synthesizing across thinkers (weaker evidence — could be pareidolia)
- **Pressure-tested** — operator survived adversarial challenge (CFA deliberation, counterexample review)

Independent convergence weighs more heavily than synthetic identification.

### Step 7: Pressure Test

Before promoting an operator from RED to YELLOW or YELLOW to GREEN:

- **Counterexample search:** Can we find a brilliant thinker who intentionally violates this operator and succeeds? If yes, the operator has a boundary — document it.
- **CFA stress test:** Can the operator survive CFA's adversarial deliberation? Run it through the Phase sequence. If Claude (PRO) and Grok (ANTI) converge on the operator's validity, it's more robust.
- **Translation test:** Express the operator in a completely different domain. Does it still make sense? If it only works in physics, it's domain-specific, not fundamental.

### Step 8: Museum

Register confirmed operators in `MUSEUM/operators/OP_{NNN}_{name}.md`. Update `MUSEUM/INDEX.md` and `MUSEUM/GRAPH.md`.

---

## Operator Admission Criteria

To qualify as an operator, a recovered pattern MUST satisfy ALL of the following:

| Criterion | Test | Why |
|-----------|------|-----|
| **Describes an action** | Can you say "the thinker PERFORMED this operation"? | We catalogue moves, not beliefs or conclusions |
| **Generalizes beyond domain** | Does it apply outside the thinker's field? | Domain-specific techniques are valuable but not operators |
| **Is reusable** | Can someone else apply it to new material? | If it only works once, it's an insight, not an operator |
| **Has observable failure modes** | What goes wrong when it's absent? | If nothing goes wrong without it, it isn't doing real work |
| **Survives translation** | Can you express it in different terminology without losing the core move? | If renaming breaks it, it's terminology, not structure |
| **Transforms epistemic state** | After applying it, does something change about what you know, believe, or investigate? | If applying it leaves your epistemic position unchanged, it's not doing cognitive work |

### Operator Metadata: Protocol-Dependent vs. Voluntary

When operators are extracted from structured formats (e.g., CFA Trinity deliberations), distinguish:

| Property | Definition | Example | Interpretation |
|----------|-----------|---------|----------------|
| **Voluntary** | Operator requires deliberate cognitive initiative regardless of format | OP-004 (Reconstruction Before Judgment) — evaluator must choose to reconstruct | "This thinker spontaneously deploys this move" |
| **Protocol-Dependent** | Operator appearance is partly explainable by format constraints | OP-008 (Symmetry Testing) in CFA with --reverse stance | "This format induces this move" |

Voluntary operators are stronger evidence of genuine cognitive architecture. Protocol-dependent operators are still real, but they need different interpretation: "this protocol induces this reasoning move" rather than "this thinker spontaneously deploys this move."

Museum entries should record this property when source format could plausibly induce the operator. See Experiment 11 (OP-008 protocol-induction test) for the formal test design.

**Source:** CFA Claude (2026-07-10)

### The Taxonomy: Operators vs Heuristics vs Rhetorical Techniques

These three categories are often confused. Only the first belongs in the Museum.

| Category | Example | Test |
|----------|---------|------|
| **Operator** | Separate representation from ontology | Transforms what you think exists. State transition. |
| **Heuristic** | Start with the simplest explanation | Guides search strategy. No guaranteed state change. |
| **Rhetorical technique** | Use analogy to explain | Communication device. Changes the listener, not the thinker. |

If a recovered pattern is a heuristic or rhetorical technique, it may still be worth documenting — but not in the Operator Museum. Keep the Museum clean.

### What is NOT an operator

- A belief ("consciousness is fundamental") — this is a conclusion, not a move
- A domain-specific technique ("take the Fourier transform") — this doesn't generalize
- A style preference ("write clearly") — this has no failure mode specific enough to catalogue
- A tautology ("think carefully") — this doesn't describe a specific cognitive move
- A methodology ("use the scientific method") — too coarse; it decomposes into operators

### Edge cases

- **Compound operators:** Some operators are compositions of simpler ones. Catalogue the composition AND the components. The composition may have emergent properties the components don't (CFA's Phase sequence is a composition of OP-004, OP-006, OP-002, etc.).
- **Meta-operators:** Some operators operate ON other operators (e.g., collapsing two operators into one, as Nova did with Hidden Structure Injection). These are valid — catalogue them, but note that they're meta-level.
- **Negative operators:** "Refuse to do X" can be an operator if the refusal is a specific, reusable cognitive move with identifiable failure modes when violated.

---

## Organizing Principle

Early in the project: organize by **thinker** (dig sites).

As the museum grows: reorganize by **operator**. The thinker becomes evidence; the operator becomes primary. This mirrors the chemistry transition from "Priestley discovered oxygen" to "oxygen is element 8."

The transition happens naturally when rediscoveries outnumber new operators.

---

## CFA as Evidence Source

CFA's adversarial deliberation generates operator evidence passively — it just hasn't been read that way.

Every **CRUX declaration** in a CFA run is an operator failure-mode event in the wild. When Claude and Grok reach irreconcilable divergence on a metric, the diagnostic question isn't only "which auditor is right" — it's "which operator was absent or misapplied in this scoring session?"

Example: CRUX_MS_20260629 retroactively reads as:
- OP-001 failure (Representation ≠ Ontology): auditors scored in their own representation, not the FUT's
- OP-007 failure (Locate Disagreement Layer): divergence was at the Description layer (competing MS definitions) but was treated as an Evaluation-layer dispute
- OP-004 failure (Reconstruction Before Judgment): Phase 2 evaluation was embedded into Phase 1 reconstruction

This makes every archived CRUX declaration a potential ledger entry — not a new dig site, but a pressure-test event that either confirms an existing operator's failure modes or reveals a failure mode not yet catalogued.

**Protocol:** When reviewing a CRUX declaration, ask: "Which operators from the Museum are flagged by this event? Does this confirm an existing failure mode or reveal a new one?" Log findings in the relevant operator's Provenance Chain under evidence type "Pressure-tested."

### CFA as Reasoning-Structure Assay (Reframe)

CFA is not a worldview scorer. It is a reasoning-structure assay — it measures how frameworks THINK under adversarial pressure, not what they conclude. The 6-step audit pattern (reconstruct, evaluate, challenge, defend, converge, reflect) is a detection instrument for cognitive architecture. Scores measure reasoning quality, not framework truth.

This reframe matters because: the same CFA infrastructure that tests worldviews can test discovery architectures (IQ-027), cognitive scripts (IQ-030), and attention allocation strategies (IQ-028). The assay generalizes to any structured reasoning process, not just philosophical frameworks.

### Extractor Susceptibility: A Property, Not a Flaw

Tier 1 extractors (Claude, DeepSeek V4 Pro, Gemma4 31B, Cogito 671B) are susceptible to the same operators they detect. OP-006 (Under-Determination Detection) is the structural blind spot — extractors are optimized for finding structure, not for finding the null hypothesis that explains structure away. Test A demonstrated this: the extractors found composition effects without checking noise floors.

This is not a flaw to fix. It is a property to document and design around. The compensating control is the 6-step audit pattern: no finding is trusted until it survives the main-effect decomposition, the H-baseline check, and the negative control battery. The extractors find candidates; the audit pattern filters them.

---

## Excavation Norms

> **Excavate generously. Classify conservatively.**

Every shard gets collected. Very few become new species.

### Blind Excavation Protocol

Do NOT show the excavator the existing Museum before digging. Ask only: "Recover recurring reasoning operations." Compare against the Museum afterward. This prevents confirmation bias from shaping what gets found.

When possible, assign different excavators to different thinkers independently — then compare results. This reduces observer bias and produces stronger convergence evidence.

### The Standing Question

After every excavation, before cross-referencing: **What surprised us?** Surprises are where theories improve.

---

## Quality Checks

After every excavation, ask:

1. Did I recover 5-15 operators? (Fewer = too coarse; more = not enough abstraction)
2. Did I find at least 2 failure modes? (Zero = probably summarizing, not excavating)
3. Did at least 1 operator already exist in the Museum? (Zero after 5+ digs = either the operators aren't general, or the dig was sloppy)
4. Are operators named as VERBS, not nouns? (We catalogue moves, not things)
5. Would a thinker RECOGNIZE the operator if you showed it to them? (If not, you may be projecting)

---

## The Cross-Arm Prediction Loop (EOS ↔ CFA)

Each dig site produces two artifacts:

1. A thinker's **cognitive architecture** (operators, genome, discovery architecture)
2. A thinker's **substantive worldview** (their actual position on reality)

The worldview is a candidate for future CFA Trinity batches. This creates a testable prediction loop:

```text
EOS extracts operator profile →
CFA tests worldview under adversarial comparison →
Compare: does the operator profile predict worldview performance?
```

Example: If Dirac's genome shows heavy use of OP-011 (Subtractive Discovery) and weak Epistemic Boundary Setting (OP-013), does his worldview score high on MG and AR but low on CCI?

This is the most underused structural connection in the project. Every dig site that produces a Discovery Genome (see `TEMPLATES/DISCOVERY_GENOME.md`) implicitly generates a CFA prediction. Test it.

---

*Field Manual v2 — 2026-07-06*
