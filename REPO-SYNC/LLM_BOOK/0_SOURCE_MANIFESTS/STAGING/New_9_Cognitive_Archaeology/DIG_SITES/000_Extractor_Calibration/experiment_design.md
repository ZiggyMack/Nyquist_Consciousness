# Dig Site 000: Extractor Calibration

> **Phase 0 — Who is excavating?**

Before excavating any thinker, calibrate the instrument. This experiment determines whether operator extraction is a property of the source text or a property of the extractor.

Everything before this point was hypothesis formation. Dig Site 000 is where reality gets a vote.

---

## Design

### Arm 1: Multi-Extractor Agreement

Give the same source text to multiple independent extractors, blind to the Museum. Each receives the same prompt: "Recover recurring reasoning operations from this text."

**Extractors:**

| Extractor | Type | Notes |
|-----------|------|-------|
| Claude | LLM | Current primary extractor |
| GPT | LLM | Different training distribution |
| Gemini | LLM | Different architecture lineage |
| Grok | LLM | Different training philosophy |
| Human A | Human | Philosophy background |
| Human B | Human | STEM background |

**Source text:** Select a single well-defined passage (10-20 pages) from Dig Site 002's target thinker. All extractors receive the identical passage.

**Prompt:** Identical across all extractors. No reference to existing operators, no Museum vocabulary, no priming. Just: "Identify the recurring reasoning operations this thinker performs. For each, describe what the thinker does (the action), when they do it, and what goes wrong when the operation is absent."

**Measure:** How many operators do extractors agree on? Use pairwise comparison — for each extractor pair, what fraction of their extracted operators match? Report the distribution, not just the mean.

**Pre-committed threshold:** If average pairwise agreement falls below 40%, the extraction process is dominated by extractor variance. Investigate before proceeding.

### Arm 2: Negative Control Battery

Run the extraction prompt against texts that should NOT produce operator structures.

**Negative controls:**

| Text | Expected result | What a positive finding means |
|------|----------------|-------------------------------|
| Shopping list | No operators | Extraction generates rather than detects |
| Weather forecast | No operators | Surface pattern matching |
| Random Reddit comments | Minimal / degenerate | Low-quality reasoning lacks structure |
| Pseudo-profound nonsense (Sokal-style) | Minimal / degenerate | Operators are not fooled by mimicry |
| LLM hallucination (confident but wrong) | Possibly some | Interesting — does wrong reasoning use the same operators? |
| Undergraduate essay (competent but not exceptional) | Some, lower density | Operators are present but less concentrated |

**Measure:** Operator count and specificity per text type. If the shopping list yields 7 operators indistinguishable from Barandes, the extraction is broken.

### Arm 3: Granularity Sensitivity

Run extraction at three different description grains on the same source text:

- **Coarse:** "Identify 3-5 high-level reasoning strategies"
- **Standard:** "Identify recurring reasoning operations" (the normal prompt)
- **Fine:** "Identify 15-20 specific reasoning moves, including subtle ones"

**Measure:** Do the coarse-grain operators decompose cleanly into fine-grain ones? Or does convergence only exist at one grain? If operators only "exist" at the standard grain, they are artifacts of the prompt's granularity expectation.

---

## Protocol

1. Select source text (before seeing any results)
2. Run Arm 2 (negative controls) first — if negative controls light up, stop and fix the extraction before wasting effort on Arm 1
3. Run Arm 1 (multi-extractor) — all extractors work independently, results compared only afterward
4. Run Arm 3 (granularity) — same source text, different grain prompts
5. Analyze and report: extractor agreement matrix, negative control results, granularity sensitivity

---

## Success Criteria

Phase 0 passes if ALL of the following hold:

- Negative controls produce measurably fewer and less specific operators than genuine reasoning
- At least 3 extractors agree on at least 50% of operators from the same source text
- Operators are recognizable across at least 2 description grains (not grain-dependent)

Phase 0 fails if ANY of the following hold:

- Negative controls produce operator structures indistinguishable from genuine reasoning
- No two extractors agree on more than 30% of operators
- Operators vanish or completely restructure with small changes to description grain

---

## Pre-Commitment (written before seeing results)

**What outcome would disappoint us:**

If Dig Site 000 demonstrates strong extractor dependence — Claude finds operators that no other extractor finds — we will redesign the excavation methodology before proceeding to further dig sites. We will not rationalize the divergence or adjust the comparison criteria after the fact.

**What we expect (registered before running):**

- OP-001 (Representation ≠ Ontology) and OP-004 (Reconstruction Before Judgment) are the most likely to survive multi-extractor agreement — they describe concrete, nameable cognitive moves.
- OP-006 (Under-Determination Detection) is the most likely to fail — it was already flagged as "closer to a detection condition than an operation" and was a Synthetic identification.
- Negative controls will probably produce 1-2 vague operator-like patterns at coarse grain, but these should be clearly distinguishable from the structured operators found in real reasoning.

**What we commit to:**

- If negative controls produce operator structures indistinguishable from real dig sites: stop and fix the extraction before any new digs.
- If extractor agreement is below 40%: treat all current operators as provisional artifacts pending methodology revision.
- If Dig Site 000 "fails," that is not a failure of Cognitive Archaeology — it is the first real result. The purpose of calibration is not to prove the instrument works. It is to discover exactly how it works.

---

## Status

**Preliminary Phase 0A data collected (2026-07-08).** Full protocol not yet run. Negative controls and granularity sensitivity outstanding.

### What exists

Four-way CFA transcript extraction produced preliminary multi-extractor agreement data:

- **Source texts:** Two CFA Framework-G v2 transcripts (v2 pilot, 423K chars, 7 metrics; v2.1, 66K chars, MS-only with DI/CP)
- **Extractors used:** Claude (claude-sonnet-4-6) and Grok (grok-3-mini) — museum-blind, no CFA vocabulary in prompts
- **Result:** Five stable operators recovered across all four extractions. 7 exact + 2 strong matches out of 9 Grok operators matched Claude's on v2.1 transcript.
- **Extraction files:** `extractions/extraction_cfa_framework_g_v2_20260708_standard_{extractor}_{timestamp}.md`

### What this means for Phase 0

This is partial Phase 0A (multi-extractor agreement on genuine source text). It addresses one confound — do two different LLM extractors find the same operators? — with a positive result. But it does NOT address:

- Phase 0B (negative controls) — would a shopping list also produce 5 operators?
- Phase 0C (granularity sensitivity) — do operators survive grain changes?
- Human extractors — do non-LLM extractors agree?
- Different source text — CFA transcripts are a specific genre; do results generalize?

The preliminary data is encouraging but does not satisfy the full Phase 0 pass criteria. All pre-committed thresholds in `PRE_REGISTRATION.md` remain frozen.

### Methodological discovery

**"Shorter is richer."** Grok extracted 9 operators from the 66K-char stalled transcript vs 5 from the 423K-char convergent transcript. Stall-induced metacognitive pressure forces auditors to articulate reasoning operations explicitly. Implication for Dig Site 000 source text selection: prefer transcripts with impasses and stalls over clean convergences. The metacognitive pressure IS the excavation tool.

**Pre-registration:** See `PRE_REGISTRATION.md` for frozen expectations, prediction log, and permitted conclusions.

---

*Created: 2026-07-06*
*Updated: 2026-07-08 — preliminary Phase 0A data noted*
