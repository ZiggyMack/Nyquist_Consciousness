# Cognitive Archaeology

> **The empirical search for reasoning invariants under systematic perturbation.**

What refuses to disappear when you change the framework, the auditor, the extractor, the prompt, the advocate, and the deliberation length? Whatever survives is a candidate for real structure. Everything else is observer, instrument, or accident.

---

## What This Is

> *Every intellectual tradition leaves behind two kinds of artifacts: its conclusions, and the cognitive operators that produced them. Conclusions belong to history. Operators belong to everyone.*

We are not studying opinions, conclusions, or ideologies. We are studying **operations** — the cognitive machinery that produces conclusions. Ideas are the artifacts. Reasoning operators are the fossils of thought.

The question is no longer *"What did this thinker believe?"* but *"What cognitive moves does this thinker repeatedly perform?"*

This is the difference between cataloguing every sentence ever written and discovering the rules of syntax. We are looking for the **grammar of reasoning** — the reusable operations that appear wherever competent argumentation occurs, and whose selection, ordering, and omission distinguish one thinker's approach from another's.

---

## Project Status (2026-07-11)

| Milestone | Status | Key Result |
|-----------|--------|------------|
| Dig Site 001 (Adlam/Barandes) | COMPLETE | 6 operators recovered (OP-001 through OP-006) |
| Dig Site 002 (Barandes solo) | COMPLETE | 6 new operators (OP-010 through OP-015), 3 rediscoveries, operator families introduced, Discovery Architectures emerged |
| Dig Site 003 (Dirac) | PLANNING | Q50 rank #1. Tests forward-generative architecture. |
| Phase 0A (positive control) | COMPLETE | 2 extractors (Claude + Grok), 7/9 exact match, 100% Grok-to-Claude match rate |
| Phase 0B (negative controls) | COMPLETE | 17 extractors x 8 negative controls (136 extractions). Extractor tiering established. Clean discrimination gradient. |
| Phase 0C (Tier 1 positive) | COMPLETE | 4 Tier 1 extractors on Framework-G v2.1. 91-100% match with Phase 0A ground truth. |
| H-Baseline (MEC null test) | COMPLETE | MEC excess over matched-difficulty control ~ 0. Operator PRESENCE saturates at competence. Discriminating signal lives in SELECTION, ORDERING, and OMISSION. |
| Test A (composition regimes) | PLANNED | Do worldview transitions compose? 702 CFA Trinity runs available. |
| Test B (sequence statistics) | IN PROGRESS | Tooling built. Preliminary: dig-site avg 12.5 operators vs neg-H 5.7. Blinded matching run PENDING. |
| Museum | 15 operators | 0 GREEN, 7 YELLOW, 8 RED. GREEN promotion BLOCKED for OP-008/OP-009 (found in neg-H). |
| Discovery Architectures | 1 confirmed, 5 candidates | RCI confirmed. Forward-generative, Evolutionary, Compression, Adversarial, Composition Analysis candidates. Discovery Simplex hypothesized. |

### The H-Baseline Finding

The most important empirical result so far. Opus proposed and pre-registered an H-baseline test: run the same extraction on a matched-difficulty negative control (a throwaway philosophy seminar dialogue, neg-H) using the same extractors. If Tier 1 extractors agree on neg-H operators at rates comparable to dig-site operators, then Multi-Extractor Convergence (MEC) measures vocabulary, not the source.

**Result:** Tier 1 extractors agree ~80% on neg-H vs ~78% on dig-site. MEC excess ~ 0. OP-008 and OP-009 — the only two GREEN-track operators — both appeared in neg-H, blocking their promotion (GREEN criterion (c) requires "demonstrated absent in negative-control text").

**What this means:** Operator *presence* discriminates reasoning from non-reasoning (negative controls A-F produce dramatically fewer operators), but it does NOT discriminate exceptional from competent. The operators are a grammar of competent argumentation, not a grammar of genius.

**The escape route:** Ziggy's pre-registration A8 predicts that the discriminating signal lives in operator SELECTION, ORDERING, and OMISSION — not presence. Test B is the load-bearing experiment that tests this.

---

## Levels of Abstraction

The project studies discovery at six levels. We didn't plan to climb this hierarchy — Dig Site 002 pushed us up it.

```text
Level 0  Knowledge               "Barandes thinks X."
Level 1  Patterns                "Barandes repeatedly removes mathematical baggage."
Level 2  Operators               OP-011, OP-014, OP-012
Level 3  Operator Families       Translation, Subtraction, Constraint Induction, Blind Spots
Level 4  Discovery Architectures Backward-Reading (RCI), Forward-Generative (candidate)
Level 5  Meta-science            When should one architecture outperform another?
```

Levels 0-3 are housed in the Operator Museum (`MUSEUM/`). Level 4 has its own document (`DISCOVERY_ARCHITECTURES.md`). Level 5 is what Dig Site 003 tests.

The hierarchy inverts the original direction of explanation:

```text
Original assumption:  Protocol → Knowledge → Operators
Actual structure:     Reality → Invariants → Architectures → Operators → Protocol → Knowledge
```

Protocols don't create operators. Protocols instantiate architectures. Architectures select operators. Operators extract knowledge. Knowledge reveals invariants.

---

## First Law

> **Independent convergence is stronger evidence than isolated brilliance.**

If Barandes discovers Operator X independently of Pearl, who discovers it independently of Jaynes, who discovers it independently of Lakoff — that is vastly stronger evidence than any single thinker's formulation.

An operator seen once is a hypothesis. Seen across 5+ independent thinkers, it is confirmed.

---

## The Anti-Reification Principle

> **We are not discovering eternal entities. We are proposing increasingly useful decompositions of reasoning.**

This project studies operators — and operators are hypotheses about cognition, not fixed objects. The irony is real: a project dedicated to detecting reification (OP-001) must guard against reifying its own constructs.

Every operator in the Museum is provisional. Any operator may be:
- **Decomposed** into simpler operators we haven't identified yet
- **Merged** with another operator once we recognize them as the same move
- **Retired** when a better decomposition renders it unnecessary
- **Split** when we discover it was actually two distinct operations

This is not a flaw. This is the scientific method applied to itself. Phlogiston was retired. Elements moved on Mendeleev's table. Noble gases were added. The table survived because the commitment was to the correct decomposition, not to any particular entry.

---

## The Scientific Method of Cognitive Archaeology

```
OBSERVATION       "I noticed Barandes repeatedly separates representation from ontology."
     |
EXCAVATION        Recover operators from the source material.
     |
ADMISSION         Does it satisfy the Operator Admission Criteria?
     |
CROSS-SITE        Does Pearl independently perform the same operation?
RECOVERY
     |
ARCHITECTURE      Do recovered operators compose into a discovery engine?
IDENTIFICATION    (see DISCOVERY_ARCHITECTURES.md)
     |
PRESSURE          Can CFA successfully use the operator?
TESTING
     |
PREDICTION        Does the operator (or architecture) predict unseen reasoning or failure modes?
     |
FUNDAMENTAL       Saturated across thinkers. Compositional. Predictive.
STATUS
```

Operators either survive this process or they don't.

### The Recursive Discovery Loop

Each dig site feeds the next — not just via Q50 source recommendations, but through every level of the hierarchy:

```text
Dig Site N
    ↓
Knowledge              What did this thinker discover?
    ↓
Operators              What cognitive moves did they repeat?
    ↓
Discovery Architecture What engine composed those operators?
    ↓
Protocol Revision      How should we revise extraction to capture this?
    ↓
Dig Site N+1           Which unexplored region of Discovery Space maximizes information gain?
```

Q50 operationalizes the last step. Originally "who should we study next?" — now "which region of Discovery Space is least sampled?"

---

## Success Criteria

This project succeeds not by accumulating operators, but by four measurable signals:

1. **Increasing independent convergence** — new thinkers rediscover existing operators more often than they produce new ones
2. **Increasing predictive power** — the Museum correctly predicts operators in unseen thinkers before excavation
3. **Decreasing need for new operators** — the rate of genuinely new operators drops as the registry matures
4. **Increasing explanatory compression** — fewer operators explain more reasoning. If 11 operators turn out to be compositions of 5 more fundamental ones, that compression is evidence of real structure.

---

## Falsification Criteria

A program that can't be killed isn't a science. Cognitive Archaeology is falsified — or demoted from "science" to "descriptive hobby" — if any of the following hold:

1. **Extractor-independence fails.** Different competent extractors find substantially different operator sets on the same dig sites. (The instrument is the finding. Run this first.)
2. **Negative controls light up.** Shopping lists and pseudo-profound nonsense yield operator structures indistinguishable from real reasoning. (Extraction generates rather than detects.)
3. **Operators are universally present.** No operator ever shows predicted absence; everything appears everywhere. (Rorschach test, not grammar.)
4. **Granularity-dependence.** Convergence exists at exactly one hand-tuned description grain and evaporates if you perturb it. (Overfit to a chosen decomposition.)
5. **No blind predictive success.** The registry can describe seen texts but can't predict operator presence in held-out texts above chance. (Filing system, not theory.)

> **A filing system is not a theory.** The Museum earns the name "theory" only when it predicts. Prediction means: telling you what you'll find before you look, and being right.

---

## Origin

This project emerged from a NotebookLM extraction of Adlam & Barandes (New_8_Cognative_Physics). The prompts were designed to force NotebookLM to operate as a structural philosopher rather than a summarizer. The result: NotebookLM independently rediscovered several abstractions we had built months earlier (Master→DBEP, FUT's representation→evaluation flow, "rationality serves goals, never chooses them").

Nova's observation: thinkers across our reading list perform the same small set of reasoning operations. Our hypothesis — **an underexplored synthesis, not a claim of novelty** — is that nobody has unified these into one operator framework. That hypothesis is testable: if new thinkers consistently rediscover the same operators, the synthesis is real. The H-baseline result (Phase 0B) established that operator *presence* saturates at the level of competent argumentation — the discriminating signature lives in operator *selection, ordering, and omission*, not in the operator set itself. Adjacent work may exist in cognitive science, AI interpretability, philosophy of reasoning, or argumentation theory. If found, those become evidence, not threats.

---

## Methodology

### Excavation (Dig Sites)

Each source thinker gets a **Dig Site**. A dig site is not a book report — it is a structured excavation producing four outputs:

1. **Recovered operators** — reasoning moves the thinker performs repeatedly
2. **Recovered failure modes** — what goes wrong when the operator is misapplied or absent
3. **Recovered assumptions** — hidden premises the thinker relies on
4. **Recovered relationships** — how operators connect, cause, or oppose each other

### Cataloguing (Museum)

Recovered operators are registered in the **Operator Museum** — one page per operator with definition, examples, failure modes, duals, related operators, and a provenance chain showing every dig site where it was independently recovered.

### Comparison (Ledger)

The **Confidence Ledger** tracks how many independent thinkers confirm each operator:

| Level | Criteria | Meaning |
|-------|----------|---------|
| GREEN — Confirmed | 5+ independent thinkers | Structural primitive |
| YELLOW — Candidate | 2-4 independent thinkers | Promising, needs more excavation |
| RED — Hypothesis | 1 thinker only | Needs independent confirmation |

### Stopping Condition

This project has an objective stopping condition: when new thinkers stop producing genuinely new operators and instead keep rediscovering existing ones, we have probably discovered something real. Not complete, but real.

### Second Law

> **A filing system is not a theory.**

The museum is not the goal. Prediction is the goal. An operator registry that only describes texts you've already read is a well-organized cabinet. A theory earns the name by predicting operator presence in unseen texts, predicting where operators will be absent, and predicting what goes wrong when specific operators are missing. The museum is the means; prediction is the test.

---

## Architecture

```
New_9_Cognitive_Archaeology/
├── README.md                  # This file
├── DISCOVERY_ARCHITECTURES.md # Museum B: discovery engines (Level 4)
├── LEDGER.md                  # Operator confidence tracking
├── FIELD_MANUAL.md            # Excavation workflow, admission criteria
├── RESEARCH_QUESTIONS.md      # What the infrastructure exists to answer (16 questions)
├── DIG_SITES/
│   ├── 000_Extractor_Calibration/  # Phase 0: instrument calibration
│   │   ├── extractions/       # 280+ extraction files (17 extractors x 8 sources + positives)
│   │   ├── PRE_REGISTRATION.md     # Frozen predictions, PI declaration, phase status
│   │   ├── ADMISSION_EVALUATIONS.md  # Formal operator admission tests
│   │   ├── ARM_1_ANALYSIS.md  # Extractor agreement matrix
│   │   └── BLIND_PAIRS_TIER1.txt   # 27 blinded pairs for matching protocol
│   ├── 001_Adlam_Barandes/    # First dig site (seeded from New_8) — COMPLETE
│   ├── 002_Barandes/           # Barandes solo (New_8 Round 2) — COMPLETE
│   ├── 003_Dirac/              # Q50 #1 — forward-generative, RCI stress test — PLANNING
│   ├── 004_Wolfram/            # Q50 #2 — deterministic architecture
│   ├── 005_Hermann/            # Q50 #3 — philosophical auditing, Noether lineage
│   ├── 006_Pearl/              # Original list — highest convergence potential
│   ├── 007_Dennett/            # Original list — Nyquist/consciousness link
│   ├── 008_Jaynes/             # Original list — ISP lineage, MaxEnt
│   └── (each self-contained: _IN/, _OUT/, chat.md, STATUS.md)
├── MUSEUM/                    # Operator catalog
│   ├── INDEX.md               # Master operator list (15 registered)
│   ├── GRAPH.md               # Operator relationships + Failure Atlas
│   ├── RETIRED.md             # Operator retirement records
│   └── operators/             # Individual operator pages (OP-001 through OP-015)
├── TOOLS/                     # Analysis scripts
│   ├── extract_operators.py   # Extraction pipeline
│   └── sequence_analysis.py   # Test B + blinded matching tooling
├── compression_candidates/    # Mathematical framework quarantine
│   ├── README.md              # Third Law, promotion pathway
│   └── category_theory/       # First UCC — predictions registered, 0 tests run
│       └── status.md
├── TEMPLATES/                 # Reusable templates
├── _IN/                       # Source materials
├── _OUT/                      # NotebookLM outputs
└── _ROUND_1/                  # Standard LLM Book analysis
```

---

## Relationship to Other Projects

| Project | What It Studies | How CA Relates |
|---------|----------------|----------------|
| Nyquist | Consciousness | CA excavates the reasoning operators used to study consciousness |
| CFA | Worldview evaluation | CA is the meta-methodology — CFA is one application of the operators. CFA's Diagnostic Interrogation and Coupling Probe are operator-recovery instruments in vivo: they force auditors to articulate reasoning operations under metacognitive pressure. CFA's CRUX declarations are operator failure-mode events (see Failure Atlas). |
| FUT | Structural qualification | FUT's representation→evaluation flow IS an operator (recovered in Dig Site 001) |
| EOS | Institutional reasoning | EOS applies operators in organizational contexts |
| LLM Book | Knowledge extraction | NotebookLM becomes the excavation assistant, not a summarizer |

Nova's observation: CFA, FUT, EOS, and Nyquist all use the same cognitive machinery. Cognitive Archaeology studies that machinery directly.

If CFA is discovering a periodic table of worldviews, Cognitive Archaeology asks whether there is a **finite grammar of reasoning operators**. That question operates at a different level of abstraction than everything that came before. The motivating metaphor is a "periodic table of reasoning" — but the actual hypothesis is agnostic about form. Operators might behave like discrete atoms, or like genes, or like circuits, or like grammatical rules. The structure of the answer is part of what we're discovering. If the answer is "yes, there is reusable structure," the implications reach beyond philosophy into education, AI, scientific methodology, and the design of future reasoning systems. If the answer is "no," that result is still profoundly interesting — it would mean reasoning is irreducibly context-dependent, which itself constrains every project above.

---

## Mathematical Structure (Theoretical — Not Yet Operational)

> **We are not searching for Category Theory inside reasoning. We are searching for the simplest mathematics capable of compressing whatever stable reasoning structures survive empirical excavation.**
> — Nova, 2026-07-08

### Third Law

> **A mathematical framework earns the right to describe the project only after it successfully compresses independently recovered empirical regularities and makes novel, testable predictions.**

Three requirements, all mandatory: (1) compresses, (2) independently recovered, (3) predicts something new. If it fails any one, it stays philosophy.

### The Invariant Question

The deepest connection between Cognitive Archaeology and mathematics is not any specific mathematical framework. It is that CA is an **invariant-finding machine**. Every design choice eliminates observer-dependent structure to find what survives:

| What changes | What survives? | CA mechanism |
|-------------|---------------|-------------|
| Framework | Stable operators | Cross-thinker recurrence |
| Extractor model | Same operators | Multi-extractor agreement (Dig Site 000) |
| Extraction prompt | Same operators | Granularity calibration |
| Auditor pairing | Same scores | CFA control batches |
| Advocate model | (untested) | Advocate variability experiment |
| Diagnostic intervention | Behavioral arc | DI/CP architecture |

This is the real question: **what are the invariant objects of Cognitive Archaeology?** Not "can we use Category Theory?" — but "if CA is discovering something real, what mathematics should eventually describe it?"

That question deliberately leaves the answer open. The mathematics that earns the privilege of describing what we find might be category theory, graph theory, information theory, algebra, topology, or something entirely new. The answer is part of what we're discovering.

### Candidate Interpretations (Unearned Compression Candidates)

**"Unearned Compression Candidate"** is a formal status for mathematical frameworks that appear to rhyme with what we're building but have not yet satisfied the Third Law. They are applicants, not descriptions. They earn their place by making predictions the data confirms — through the same adversarial, empirical process every other idea must survive.

Category Theory has surfaced as one candidate lens because it shares CA's obsession with invariants and transformations. Several mappings have been noted:

- **Operators as morphisms** — operators are transformations between reasoning states, not static objects. They have domains, codomains, and may compose.
- **CRUX as categorical failure** — "there exists no structure-preserving morphism between these two reasoning systems" is stronger and more precise than "they disagree."
- **Coupling Probe as functor-like** — Nova checks whether one auditor's reasoning can be faithfully mapped into the other's. CRUX fires when the mapping fails.
- **Four-way extraction convergence as natural transformation** — two independent extractors recovering the same operators is evidence that the operators are intrinsic to the transcript, not artifacts of who reads it. This is precisely what Dig Site 000 tests.
- **Universal operators** — Category Theory predicts that certain constructions must exist regardless of domain. If Dig Site excavation discovers operators that appear in Plato, Feynman, Grant, Buddhism, and ML alignment, that resembles a universal construction — but the discovery comes first, the mathematics follows.

**These are observations, not commitments.** They become meaningful only if and when empirical data independently confirms the structures they predict.

### Active Tests

Two experiments are in progress. Neither requires committing to any mathematical framework.

**Test B: Operator Sequence Statistics (LOAD-BEARING)**

The H-baseline proved that operator *presence* saturates at competence. If operator *ordering* on dig sites is also indistinguishable from matched-difficulty controls, the Museum catalogues competence. If the ordering differs — that's the fossil.

Tooling: `TOOLS/sequence_analysis.py` (inventory, extract, stats, blind commands). Preliminary results: dig-site extractions average 12.5 operators vs neg-H 5.7. Dig-site vocabulary is more domain-specific (251 unique words vs 103 neg-H-only). Semantic matching is the bottleneck for authoritative results.

Blinded matching protocol (Opus pre-registration section 4): 27 pairs generated in `BLIND_PAIRS_TIER1.txt` — source labels stripped, shuffled with seed=42. A matcher who cannot see which pair came from the dig site classifies them. If dig-site pairs are inseparable from neg-H pairs, MEC measures vocabulary, not Barandes.

**Status:** Tooling complete. Blinded matching run PENDING.

**Test A: Composition Regimes (CFA Trinity)**

Do worldview transitions compose? For every triple (A, B, C), classify the relationship between A→B, B→C, and A→C into regimes: composes exactly, composes approximately, fails composition, generates obstruction, or generates novelty.

Data: 702 CFA Trinity runs (G=212, PT=131, MdN=94). Need to parse JSON files for framework pairings, extract exit survey score vectors, compute composition statistics.

**Status:** PLANNED. Awaiting structural framing from CFA Claude on what vectors define "composition signature."

### The Convergence Prediction

Different frameworks may use different objects but the **same transformations**. If true, the 0.98+ convergence across Buddhism matchups (zero CRUXes, 1.6 average rounds) is not surprising — it's expected. Buddhism doesn't introduce any transformation that fails to translate between auditors. CT does (the grounding gate), which is why CT produces CRUX and Buddhism does not. Both outcomes are retrodicted by this framing — but retrodiction is not prediction.

### Placement

This section records theoretical observations for future testing. It does not inform any extraction prompt, YAML schema, operator definition, or code change. The empirical engine (adversarial deliberation, extraction, DI, coupling probe, Failure Atlas) stays exactly as built. Mathematics earns its place by compressing what the engine finds, not by telling the engine what to look for.

Dig Site 000 is complete (Phases 0A/0B/0C + H-baseline). The proper sequence remains: excavate reasoning, discover stable structures, then ask mathematicians what those structures resemble. Not: adopt a mathematical language, then look for it in reasoning.

---

## Instrument Validation Results (Phase 0)

Phase 0 is the instrument calibration — testing whether the extraction pipeline deserves to measure anything at all. It ran in four phases plus a null-distribution test.

### Phase 0A: Positive Control (2 extractors)

Two extractors (Claude + Grok) independently extracted operators from the same CFA transcript (Framework-G v2.1, 66K chars, MS-only with DI/CP). Neither saw the Museum.

**Result:** 7 exact matches + 2 strong matches out of 9 Grok operators = 100% Grok-to-Claude match rate. Five stable operators recovered across all extractions. Two new operators admitted to Museum (OP-008, OP-009). Two OP-007 rediscoveries confirmed. Exceeds pre-committed 40% pairwise agreement threshold.

**Methodological finding:** "Shorter is richer" — stall-induced metacognitive pressure forces auditors to explicitly articulate reasoning operations. Concentrated single-metric deliberation with impasses produces richer extraction material than broad multi-metric convergence runs.

### Phase 0B: Negative Control Battery (17 extractors)

17 LLM extractors ran museum-blind on 8 negative control texts: shopping list (neg_A), weather forecast (neg_B), Reddit comments (neg_C), pseudo-profound nonsense (neg_D), confident hallucination (neg_E), instruction manual (neg_F), philosophical dialogue (neg_G), and matched-difficulty philosophy seminar (neg_H).

**Result:** Clean discrimination gradient. Tier 1 extractors cleanly refused to extract operators from trivial controls (shopping list, weather forecast). Lower-tier extractors showed false positives. This established the extractor tiering system:

| Tier | Models | Criterion |
|------|--------|-----------|
| Tier 1 | DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B | Clean discrimination: refuse trivial, extract genuine |
| Tier 2 | Grok, GPT, Kimi K26/K27, Qwen3 235B, Llama 33 70B | Moderate discrimination, some false positives |
| Tier 4 | LFM2, GLM, Gemini 2.5 Pro, Nemotron Ultra, MiniMax M3, GPT-OSS variants | Poor discrimination or hallucinated operators |

### Phase 0C: Tier 1 Positive Control (4 extractors)

All four Tier 1 extractors ran on the same Framework-G v2.1 transcript used in Phase 0A. Museum-blind.

**Result:** 91-100% match with Phase 0A ground truth. All four extractors found operators mapping to known Museum entries. Pre-registered pass criteria met on all dimensions (detection, ground truth match, Museum match).

### H-Baseline: MEC Null Distribution (Opus)

Opus proposed, pre-registered, and scored this test. The question: does Multi-Extractor Convergence (MEC) measure the source text or just the extractor ecology's shared vocabulary?

**Design:** Run Tier 1 extractors on neg_H (a philosophy seminar dialogue of matched difficulty but no disciplined reasoning structure). Compare inter-extractor agreement on neg_H vs dig-site.

**Result:** ~80% agreement on neg_H vs ~78% on dig-site. MEC excess ~ 0. Opus scored 1/5 on his own pre-registered predictions. OP-008 and OP-009 both found in neg-H, blocking GREEN promotion. Full results in `REPO-SYNC/CFA/Opus/RESULTS_OPUS_H_BASELINE.md`.

**Implication:** Operator presence is a threshold signal (reasoning vs non-reasoning), not a gradient signal (competent vs exceptional). The discriminating fossil — if it exists — must live in operator ordering, selection patterns, and omission. This is what Test B investigates.

---

## Target Thinker List

### Completed Dig Sites

1. **Adlam & Barandes** — representation dependence, hidden selection, emergence circularity *(DONE — Dig Site 001, 6 new operators: OP-001 through OP-006)*
2. **Barandes (solo)** — ISP theory, subtractive discovery, pedagogical forcing, Noether extraction *(DONE — Dig Site 002, 6 new operators: OP-010 through OP-015, 3 rediscoveries: OP-001/004/006, 40 insights, 14 connections, 11 experiments, operator family classifications introduced, Discovery Architectures emerged)*
3. **Extractor Calibration** — instrument validation, not a thinker dig *(DONE — Dig Site 000, Phases 0A/0B/0C + H-baseline complete, 2 new operators: OP-008/009, 2 OP-007 rediscoveries, 17 extractors tested, tiering established)*

### Q50-Recursive Queue (self-evolving from Dig Site 002)

3. **Dirac** — playful mathematical deformity, beauty as selection, forward-generative discovery *(PLANNING — Dig Site 003, Q50 rank #1)*
4. **Wolfram** — computational irreducibility, deterministic vs probabilistic architecture *(Q50 rank #2, pending Dig Site 003 Q50 output)*
5. **Grete Hermann** — philosophical auditing of consensus math, Noether lineage *(Q50 rank #3, pending)*

### Original Target List (deferred — may re-enter via Q50 recursion)

- **Pearl** — causal separation, intervention vs observation, counterfactual construction
- **Dennett** — intentional stance, heterophenomenology, competence without comprehension
- **Jaynes** — inferential vs physical information, maximum entropy, plausible reasoning
- **Lakoff** — conceptual metaphor, embodied cognition, framing effects
- **Deutsch** — constructor theory, explanatory depth, fallibilism
- **Popper** — falsifiability, demarcation, conjectures and refutations
- **Hofstadter** — strange loops, analogy as cognition, levels of description
- **Marr** — computational/algorithmic/implementational levels
- **Simon** — bounded rationality, satisficing, near-decomposability
- **Kuhn** — paradigm structure, normal vs revolutionary science, incommensurability

> **Note:** From Dig Site 003 onward, the thinker list is driven by Q50 recursion — each dig site's extraction recommends the next candidates ranked by expected operator yield. Original targets re-enter the queue when a Q50 output recommends them. Source material for Q50-recursive dig sites lives directly under `DIG_SITES/NNN_Thinker/` (self-contained LLM book projects) rather than as separate `New_N` projects in STAGING.

---

*Project initiated: 2026-07-06*
*Proposed by: Nova (2026-07-05)*
*Named by: Ziggy*
*Last updated: 2026-07-11 — Phase 0 results (0A/0B/0C + H-baseline) documented; extractor tiering (Tier 1/2/4) added; H-baseline finding and implications surfaced; Test A/B active tests documented; Museum count updated (9→15); TOOLS/ directory added to architecture; dig site yields added; claims language reflects H-baseline ("grammar of reasoning" not "grammar of genius")*
