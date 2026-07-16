# Questions the Project Can Now Ask

> *Not hypotheses. Questions.*

The infrastructure is built. These are the questions it exists to answer. Each is testable with the existing pipeline. None require new architecture.

> **Question formulation — carry the context with the question.** Many of these are answered by pushing a tool (NotebookLM / the LLM Book, an extractor, a fresh model) that only knows what it was *given*. Such a tool has no access to our Museum, our operator IDs (OP-xxx), our named protocols, or other thinkers. **Any question that references our internal framework must inline the definitions it needs** — otherwise the answer is a hallucination you can't distinguish from a real finding. Write every outward-facing question to stand on its own, especially when it pushes the tool into new territory. Canonical statement + worked examples: `TEMPLATES/EXTRACTION_PROTOCOL.md` → "The Self-Contained Question Principle."

---

## Instrument Calibration (Phase 0 — gates everything)

### Q1: Does the extraction pipeline detect or generate?

**The question:** When fed text with no disciplined reasoning (shopping lists, pseudo-profound nonsense), does the extractor produce operator structures indistinguishable from real reasoning?

**Why it matters:** If the pipeline generates operators from noise, every finding is an artifact. This is the single most important question in the project.

**How to test:** Phase 0B negative control battery (graduated A–H). Measure the response curve, not a binary pass/fail.

**Status:** TESTED (Phase 0B). 17 extractors x 8 negative controls (136 extractions). Result: clean discrimination gradient. Tier 1 extractors (DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B) cleanly refuse trivial controls. The pipeline detects, not generates — for non-reasoning text. H-baseline caveat: matched-difficulty philosophical text (neg-H) produces operator structures comparable to dig-site text, meaning the pipeline detects *competent reasoning*, not *exceptional reasoning*. Gate: PASSED for reasoning vs non-reasoning discrimination. OPEN for exceptional vs competent discrimination (Test B in progress).

### Q2: Do operators survive human extraction?

**The question:** When a human philosopher, working blind (no Museum, no prompts beyond "identify reasoning operations"), excavates the same text that LLMs extracted from — do they find the same operators?

**Why it matters:** Claude and Grok may share training-induced biases that produce the same descriptive vocabulary. A human breaks exactly that confound.

**How to test:** Phase 0C. Recruit 1-2 human extractors (philosophy background, STEM background). Same source text as Arm 1. Compare pairwise.

**Status:** PARTIALLY TESTED. Phase 0C ran 4 Tier 1 LLM extractors (91-100% ground truth match), establishing cross-LLM agreement. Human extraction NOT YET TESTED — the LLM-shared-bias confound remains live. This is the most important remaining confound.

---

## Operator Behavior

### Q3: Do operators have preferred ordering?

**The question:** Across CFA transcripts, do the five stable operators appear in a consistent sequence? Does metric separation reliably precede symmetry testing, which precedes meta-dispute identification?

**Why it matters:** After the H-baseline result, this is now the LOAD-BEARING question. Operator presence saturates at competence — the discriminating signal must live in ordering, selection, and omission. If dig-site ordering is indistinguishable from neg-H ordering, the Museum catalogues competence. If ordering differs, that's the fossil.

**How to test:** Test B — sequence statistics across extracted transcripts. Tooling: `TOOLS/sequence_analysis.py`. Compare dig-site operator sequences vs neg-H sequences.

**Data needed:** Existing Phase 0A/0B/0C extractions (available now). Semantic matching is the bottleneck.

**Status:** IN PROGRESS. Preliminary: dig-site avg 12.5 operators vs neg-H 5.7. COUNT discriminates. Blinded matching run PENDING.

### Q4: Do operators inhibit one another?

**The question:** Does the presence of one operator suppress the appearance of another? Does symmetry testing make concession pricing unnecessary? Does meta-dispute identification terminate the need for contested≠defeated?

**Why it matters:** Inhibition is a stronger structural claim than co-occurrence. If operator A makes operator B unnecessary, they're not independent — there's a causal relationship.

**How to test:** Look for negative co-occurrence in extraction data. Operators that never appear together in the same deliberation segment despite both appearing across the corpus.

**Data needed:** Larger extraction corpus (10+ transcripts).

### Q5: Do operators cluster?

**The question:** Do certain operators always appear together as a package? Is there a "evaluation cluster" (symmetry testing + contested≠defeated + meta-dispute) that activates as a unit?

**Why it matters:** Clusters suggest higher-order structure — the cluster itself might be a meta-operator, or the components might be facets of a single deeper operation.

**How to test:** Co-occurrence analysis. Look for operators with correlation > 0.8 across transcripts.

**Data needed:** 15+ extracted transcripts.

### Q6: Does operator density predict transcript quality?

**The question:** Do transcripts with more operators per kilochar produce better reasoning outcomes? Does the "shorter is richer" finding generalize — does metacognitive pressure (stalls, DI/CP) increase operator density?

**Why it matters:** If density correlates with quality, operator count becomes a quality metric for reasoning. If stalls increase density, the implication is that difficulty forces explicit reasoning.

**How to test:** Correlate operator count (from extraction) with convergence scores, CRUX rates, and round counts across existing CFA runs.

**Data needed:** Extraction on 5+ transcripts with varying deliberation profiles (convergent, stalled, CRUX).

---

## Predictive Power

### Q7: Do operators predict convergence?

**The question:** Can the operator set present in early rounds of a deliberation predict whether the deliberation will converge or stall?

**Why it matters:** This is the transition from archaeology to modeling. If early operator signatures predict outcomes, the operator framework becomes a diagnostic tool, not just a catalog.

**How to test:** Extract operators from rounds 1–3 only. Predict final convergence. Compare prediction accuracy to chance.

**Data needed:** 20+ transcripts with known outcomes.

### Q8: Do operators predict CRUX?

**The question:** Does the absence of specific operators in early rounds predict which metrics will produce CRUX declarations?

**Why it matters:** CRUX is currently diagnosed post-hoc. If operator absence predicts CRUX before it happens, the operator framework earns genuine predictive power — the Second Law is satisfied.

**How to test:** For each CRUX declaration in existing data, check which operators were absent from the pre-CRUX rounds. Is the absent set consistent? Does it match the Failure Atlas predictions?

**Data needed:** Extraction on 5+ CRUX-producing transcripts + the Failure Atlas mapping.

### Q9: Can operator sequences forecast concessions?

**The question:** Does the appearance of symmetry testing in round N predict a concession in round N+1 or N+2?

**Why it matters:** If specific operators reliably precede specific deliberation events, the operators are not just descriptive — they're mechanistically connected to reasoning outcomes.

**How to test:** Event-triggered analysis. For each instance of symmetry testing in the corpus, check whether a concession follows within 2 rounds. Compare base rate.

**Data needed:** 10+ extracted transcripts with concession tracking.

### Q10: Does operator entropy vary by framework?

**The question:** Do some frameworks (CT, Gnosticism) produce richer, more varied operator usage than others (Buddhism)? Does the zero-CRUX Buddhism finding correspond to lower operator entropy?

**Why it matters:** If operator entropy correlates with framework difficulty, it's evidence that operators respond to genuine structural properties of the frameworks, not just to extraction prompts.

**How to test:** Extract operators from Buddhism transcripts and CT transcripts. Compare diversity (unique operators per transcript), density, and entropy.

**Data needed:** Extraction on 2+ Buddhism transcripts + 2+ CT transcripts.

---

## Cross-Domain Generalization

### Q11: Do OP-008 and OP-009 survive outside CFA?

**The question:** When we extract from legal reasoning, medical case discussion, engineering postmortems, or mathematical proofs — do Symmetry Testing of Standards and Contested≠Defeated appear?

**Why it matters:** If they only appear in CFA deliberation, they're CFA artifacts. If they appear in law and medicine and engineering, they're general reasoning operators. This is the difference between a domain-specific technique and a genuine cognitive primitive.

**How to test:** Run extraction on 3–5 non-CFA, non-philosophy source texts. Check for OP-008 and OP-009 by structure, not by name.

**Candidate domains:** Legal argument (Supreme Court opinions), medical case conferences, engineering failure analysis, mathematical proof commentary, political debate transcripts.

### Q12: Can operator ecology predict future reasoning?

**The question:** Given operator transition dynamics from 50+ transcripts, can you predict which operator will appear next in a held-out transcript?

**Why it matters:** This is the ultimate test. If the operator framework can predict unseen reasoning better than chance, it has earned the title "theory." If not, it's a well-organized filing cabinet (Second Law).

**How to test:** Train a simple transition model on extracted operator sequences. Evaluate on held-out transcripts. Measure accuracy vs baseline (random operator, most-frequent operator).

**Data needed:** 50+ extracted transcripts — far future.

---

## Methodology Questions

### Q13: Is the "shorter is richer" finding robust?

**The question:** Grok extracted 9 operators from 66K chars vs 5 from 423K chars. Is this a real effect of metacognitive pressure, or a sampling artifact from two transcripts?

**How to test:** Extract from 5+ transcripts of varying length and deliberation profile. Correlate operator density with transcript length and stall count.

### Q14: Does extraction grain affect operator identity?

**The question:** At coarse grain ("identify 3–5 strategies"), do the same operators appear as at standard grain ("identify recurring operations")? Or do operators only exist at one description resolution?

**How to test:** Phase 0C. Run same source through three grain levels. Check whether fine-grain operators decompose cleanly into coarse-grain ones.

---

## Horizon Questions (Far Future)

### Q15: Is there a finite grammar of reasoning operators?

The motivating question of the entire project. We cannot answer it yet. But every question above contributes evidence toward it.

### Q16: Which mathematical framework best compresses what we find?

Category Theory is the first Unearned Compression Candidate. Others will compete. The answer is discovered, not chosen.

---

*Created: 2026-07-08*
*Initial questions seeded from Nova's research agenda proposal*
*Last updated: 2026-07-11 — Q1 status updated (Phase 0B TESTED), Q2 partially tested (Phase 0C LLMs, no humans), Q3 reframed as load-bearing (Test B in progress)*
