<!---
FILE: DIG_SITES/000_Extractor_Calibration/README.md
PURPOSE: Protocol for Phase 0 of Cognitive Archaeology — calibrating the extractor before
         any real dig sites proceed. Addresses the foundational confound: operators recovered
         by a single LLM extractor may be artifacts of that extractor's representation of
         reasoning, not features of the thinkers being excavated.
STATUS: QUEUED — must run before Dig Site 002 (Pearl)
TRIGGERED_BY: Opus (EOS) critique, 2026-07-06 — "The confound is you [the pipeline]"
--->

# Dig Site 000: Extractor Calibration

> **"Can you separate operators that are in the thinkers from operators that are in the reader?"**
> — Opus (EOS), 2026-07-06

This is Phase 0 for Cognitive Archaeology. CFA has Phase 0 ("Who is judging?"). CA has Phase 0 ("Who is excavating?"). Every excavation has a hidden layer: Thinker → Extractor → Operators. If the extractor is not calibrated, all recovered operators may be artifacts of how the extractor represents reasoning — not features of the thinker.

Dig Site 000 runs BEFORE any new real dig sites. It is not a later refinement. It is the first experiment.

---

## The Foundational Confound

When Claude extracts "Operator X" from Barandes, the null hypothesis is not:

> "Barandes uses Operator X."

The null hypothesis is:

> "Claude, prompted this way, describes Barandes' text using Operator X vocabulary."

These are not the same. The confound is that the same model, prompted the same way, produces the same descriptive vocabulary for two different texts. That is not a discovery about cognition — it is a discovery about the instrument.

Nova's framing: the extractor is the hidden selector. OP-002 (Hidden Selection Audit) applied to the CA methodology itself yields: Claude is doing the selecting. The fix is declaring and calibrating the extractor before any confidence claims are made.

---

## Protocol

### Phase 0A: Same-Text Multi-Extractor Test

**Input:** Dig Site 001 (Adlam/Barandes) — the text most thoroughly excavated by Claude.

**Procedure:**

1. Take the source text (Adlam/Barandes podcast transcript)
2. Apply the standard extraction prompt from `TEMPLATES/NOTEBOOKLM_PROMPTS.md`
3. Run independently through at minimum:
   - Claude (baseline — already done)
   - GPT-4 or GPT-4o (different architecture, overlapping but different training)
   - Gemini (different architecture, different training weighting)
   - At least one human extractor (philosophy background, no prior exposure to the Museum)
4. **Do not show extractors the Museum.** They must work blind.
5. Record: which operators appear in which extractor's output?

**Comparison:** For each operator in Claude's Dig Site 001 output, ask:
- Which other extractors independently identified this operator?
- How did they name it? (Naming convergence is weak evidence; structural convergence is strong)
- Did any extractor find operators Claude did not?

**Gate:** Before any operator can leave RED status, it must appear in at least one extractor beyond Claude on this calibration text.

---

### Phase 0B: Sham Extraction (Negative Control)

**Purpose:** Determine whether extraction generates operators or detects them.

**Procedure:** Apply the same extraction prompt to text with no disciplined reasoning:
- A shopping list
- A weather report
- A Reddit comment thread (mixed quality)
- Generated pseudo-profound text (GPT asked to sound profound without saying anything)
- A well-argued piece of motivated nonsense

**Interpretation:**

| Result | Meaning |
| ------ | ------- |
| Sham text produces 0-1 operators matching Museum | Extraction detects, does not generate |
| Sham text produces rich operator structure | Extraction generates — the prompt is a lens that manufactures findings |
| Sham text produces operators Museum doesn't contain | Interesting — either false positives or real operators the Museum missed |

**Gate:** If sham text produces Museum operators at rates comparable to real dig sites, the extraction protocol must be revised before any confidence claims are made.

---

### Phase 0C: Granularity Calibration

**The risk:** "The same operator" is a claim that depends entirely on description grain. At coarse grain, everything is "inference." At fine grain, nothing matches. The temptation is to slide the grain until convergence appears.

**Procedure:**

Take one confirmed operator (OP-001: Representation ≠ Ontology) and describe it at three grain levels:
- Coarse: "Distinguish map from territory"
- Medium: "Separate representational choices from ontological claims"  
- Fine: "When encountering an ontological claim, translate it into an isomorphic representation; if it fails the translation, it was a feature of the representation, not reality"

For each grain level, ask: at this grain, how many of the sham texts light up? A real operator at the correct grain should discriminate. If the coarse version lights up everywhere and the fine version lights up nowhere, the medium formulation is correct. Fix this in the codebook before proceeding.

---

## Extractor Independence Status

The output of Dig Site 000 sets the **Ext-Indep** field in the LEDGER for all existing operators:

| Status | Meaning |
| ------ | ------- |
| Unknown | Not yet tested (all current operators) |
| Pending | Dig Site 000 queued |
| Partial (N) | Confirmed by N extractors — not yet 3+ |
| Confirmed | ≥3 independent extractors agree above chance |

---

## On Human Extractors

Opus argued humans are required. Nova argued humans are not privileged — they have their own extractors, biases, and training distributions.

Both are correct about different things. The resolution:

**No extractor gets privileged status.** Human philosophers, mathematicians, engineers, LLMs — all are extractors. Agreement across *maximally heterogeneous* extractors is the signal. Humans break one specific confound: shared LLM training corpora. If GPT, Claude, and Gemini all find the same operator, that convergence may reflect shared textbook framing rather than real structure. A human extractor who has never trained on an LLM corpus breaks exactly that confound — and therefore contributes information the LLM agreement can't provide, even if the human is "worse" in other ways.

The heterogeneous extractor ecology is the standard. Humans are not the gold standard; they're a necessary component of the heterogeneous ensemble.

---

## Expected Outputs

After Dig Site 000:

1. **Extractor Agreement Map** — for each of the 7 existing operators, which extractors independently identified it, and in what form
2. **Sham Extraction Report** — does the Museum light up on negative controls?
3. **Granularity Codebook** — fixed description grain for each operator, committed before any new digs
4. **Revised LEDGER Ext-Indep fields** — all 7 operators moved from Unknown to their calibrated status

---

## Connection to CFA Phase 0

CFA's Phase 0 declares the evaluator before evaluation begins. CA's Dig Site 000 declares the extractor before extraction begins.

CFA's PHASE_1A_ISOMORPHISM_CALIBRATION tests whether an auditor's Phase 1 reconstruction is representation-neutral — it's already a prototype for extractor calibration. The same design logic applies here: give the "auditor" (extractor) the same material described in two different ways and check whether they find the same operators. If they don't, they're representation-dependent, not operator-detecting.

---

*Protocol designed: 2026-07-06*
*Triggered by: Opus (EOS) critique — "The confound is you [the pipeline]"*
*Status: QUEUED — run before Dig Site 002*
