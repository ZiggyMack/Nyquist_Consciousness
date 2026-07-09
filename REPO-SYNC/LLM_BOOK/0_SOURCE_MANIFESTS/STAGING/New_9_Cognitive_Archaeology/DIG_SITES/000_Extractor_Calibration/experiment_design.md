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

**Phase 0A complete. Phase 0B complete. Phase 0C (positive control) pending.**

---

### Phase 0A: Multi-Extractor Agreement (DONE — 2026-07-08)

Four-way CFA transcript extraction produced multi-extractor agreement data:

- **Source texts:** Two CFA Framework-G v2 transcripts (v2 pilot, 423K chars, 7 metrics; v2.1, 66K chars, MS-only with DI/CP)
- **Extractors used:** Claude (claude-sonnet-4-6) and Grok (grok-3-mini) — museum-blind, no CFA vocabulary in prompts
- **Result:** 7 exact + 2 strong matches out of 9 Grok operators matched Claude's on v2.1 transcript.
- **Extraction files:** `extractions/extraction_cfa_framework_g_v2_20260708_standard_{extractor}_{timestamp}.md`

**Formal outcomes (see `ADMISSION_EVALUATIONS.md`):**

| Outcome | Operators | Notes |
|---------|-----------|-------|
| Admitted to Museum | OP-008 (Symmetry Testing of Standards), OP-009 (Contested ≠ Defeated) | All 6 admission criteria passed |
| Rediscoveries | OP-007 (Locate Disagreement Layer) × 2 | Cross-site evidence (Dig Site 001 → 000) |
| Held | Concession Pricing | 4/4 convergence but marginal on criteria 5-6 |

**Key finding:** CFA deliberation transcripts ARE a valid dig site. The adversarial structure naturally produces reasoning operators.

**Methodological discovery — "Shorter is richer."** Grok extracted 9 operators from the 66K-char stalled transcript vs 5 from the 423K-char convergent transcript. Stall-induced metacognitive pressure forces auditors to articulate reasoning operations explicitly. Prefer transcripts with impasses and stalls over clean convergences.

---

### Phase 0B: Negative Control Battery (DONE — 2026-07-08)

17 LLM extractors ran across 8 graduated texts using the standard extraction prompt (museum-blind). Gate test: Text A (shopping list) must produce 0 operators.

**Extractors:** 4 native (Claude, GPT-4o, Gemini 2.5 Pro, Grok) + 13 Together.ai (Llama 3.3, GPT-OSS 20B/120B, Gemma4 31B, DeepSeek V4 Pro, MiniMax M3, Kimi K2.6, Kimi K2.7 Code, Nemotron Ultra, Qwen3-235B, Cogito 671B, GLM 5.2, LFM2 24B)

**Texts (graduated complexity):**

| ID | Text | Reasoning Content | Expected Operators |
|----|------|-------------------|--------------------|
| A | Shopping list | None | 0 (GATE TEST) |
| B | Weather forecast | None | 0 |
| C | Reddit comments | Minimal / social | Low |
| D | Pseudo-profound nonsense | Mimicry, no substance | Low |
| E | Confident hallucination | Wrong reasoning | Some |
| F | Undergrad essay | Competent but thin | Moderate |
| G | Structured argument | Genuine reasoning | High |
| H | Philosophical dialogue | Deep reasoning | High |

**Response Matrix (operator count by extractor × text):**

```
Extractor            A:Shop B:Wthr C:Rddt D:Psdo E:Hall F:Essy  G:Arg H:Phil  Gate
──────────────────── ────── ────── ────── ────── ────── ────── ────── ────── ─────
claude                    0      3      0      6      2      8      0      8  PASS
grok                      0      0      7      3      0      4      5      6  PASS
gpt                       0      4      6      6      5      7      7      2  PASS
gemini                    3      4      5      0      4      4      3      6  FAIL
llama33_70b               0      0      6      5      5      6      5      8  PASS
gpt_oss_20b               0      4      6      6      5      7      7      2  PASS
gpt_oss_120b              0      3     12     10      6      4     13     13  PASS
gemma4_31b                0      0      6      4      6      5      4      6  PASS
deepseek_v4_pro           0      0      3      0      4      4      5      6  PASS
minimax_m3                0      4     12      0      2      9      0      0  PASS
kimi_k26                  0      0      0      0      0      0      0      0  PASS
kimi_k27_code             0      0      0      0      0     11      0      0  PASS
nemotron_ultra            1      0      0      2      0      6      7      7  FAIL
qwen3_235b                0      0     10      1      7     10     10     12  PASS
cogito_671b               0      0      5      6      4      8      5      7  PASS
glm_52                    4      0      0      5      0      0      0      0  FAIL
lfm2_24b                  6      6      9      5      8     10     19      7  FAIL
```

**Gate Test Results:**

| Result | Count | Extractors |
|--------|-------|------------|
| PASS (A=0) | 13 | claude, grok, gpt, llama33_70b, gpt_oss_20b, gpt_oss_120b, gemma4_31b, deepseek_v4_pro, minimax_m3, kimi_k26, kimi_k27_code, qwen3_235b, cogito_671b |
| FAIL (A>0) | 4 | gemini (3), nemotron_ultra (1), glm_52 (4), lfm2_24b (6) |

**Discrimination Tiers (assigned by gate test + gradient quality):**

| Tier | Label | Extractors | Behavior |
|------|-------|------------|----------|
| 1 | DISCRIMINATORS | DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B | Gate pass, clean A-B zeros, appropriate rising gradient |
| 2 | GATE-PASSERS | GPT-4o, GPT-OSS 20B/120B, Grok, Llama 3.3, Qwen3-235B, MiniMax M3 | Gate pass, noisier gradient (some texts over/under-extracted) |
| 3 | OVER-REFUSERS | Kimi K2.6, Kimi K2.7 Code | Gate pass trivially — refuse everything including genuine reasoning |
| 4 | NON-DISCRIMINATORS | LFM2 24B, GLM 5.2, Gemini 2.5 Pro, Nemotron Ultra | Gate fail — hallucinate operators on shopping lists |

**Key findings:**

1. **Falsification criterion #2 ("Negative controls light up") is NOT met for Tier 1-2 extractors.** 13 of 17 extractors correctly produce 0 operators on a shopping list. The pipeline detects, not generates.
2. **Tier 4 extractors DO generate.** LFM2 found 6 operators in a shopping list and 19 in a structured argument — no discrimination. These must be excluded from the extraction pipeline.
3. **Tier 3 is a different failure mode.** Kimi K2.6 produces 0 operators on everything including philosophical dialogue — it's not discriminating, it's refusing. Also excluded.
4. **Gradients are noisy but directional.** No extractor shows the idealized monotonic 0→0→0→0→low→mid→high→high gradient, but Tier 1 extractors consistently extract more operators from genuine reasoning (G, H) than from non-reasoning (A, B).
5. **The pseudo-profound text (D) is diagnostic.** Tier 1 extractors split on it: DeepSeek and Gemma correctly produce 0, Claude and Cogito produce 4-6. This may indicate sensitivity to surface-level sophistication that warrants monitoring.

**Extraction files:** `extractions/extraction_neg_{text}_{prompt}_{extractor}_{timestamp}.md` (215 files total)

**Pipeline script:** `TOOLS/extract_operators.py` — 17 extractors configured, standard and museum-blind prompts available

---

### Phase 0C: Positive Control (PENDING)

Run extraction on a known-rich CFA transcript where reasoning operators are unambiguously present. Verify that Tier 1 extractors detect operators when they are genuinely there.

**Purpose:** Completes the calibration triangle — 0A (do extractors agree?), 0B (do they discriminate?), 0C (do they detect?). Without 0C, we know the pipeline doesn't generate on empty texts, but we don't have a formal confirmation that it detects on rich ones.

**Candidate source text:** A Framework-G transcript with multiple CRUX declarations and diagnostic interventions (stall-induced metacognitive richness).

---

### What remains for full Phase 0 pass

| Criterion | Status | Notes |
|-----------|--------|-------|
| Negative controls < genuine reasoning | **PASSED** | Tier 1-2 extractors: A=0, H=6-8 |
| 3+ extractors agree on 50%+ operators | **PASSED** | Phase 0A: 7/9 exact matches (Claude × Grok) |
| Operators recognizable across 2+ grains | **OUTSTANDING** | Arm 3 (granularity sensitivity) not yet run |
| Human extractors agree | **OUTSTANDING** | Not yet tested |
| Different source text generalizes | **PARTIALLY** | CFA transcripts only; pending Dig Site 001 cross-check |

**Pre-registration:** See `PRE_REGISTRATION.md` for frozen expectations, prediction log, and permitted conclusions. All pre-committed thresholds remain frozen.

---

*Created: 2026-07-06*
*Updated: 2026-07-09 — Phase 0A complete, Phase 0B complete (17 extractors, 8 texts, 4 tiers), Phase 0C pending*
