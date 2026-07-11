<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
depends_on:
  - 1_ARMADA_MAP.md
  - ../../experiments/temporal_stability/S7_ARMADA/0_results/manifests/ARCHITECTURE_MATRIX.json
impacts:
  - Task routing decisions
  - 0_MAP_OF_MAPS.md
keywords:
  - LLM
  - behavioral
  - routing
  - task_selection
  - provider_quirks
-->

# LLM Behavioral Matrix

**Purpose:** Task routing table based on behavioral quirks discovered through identity stability experiments.

**Core Finding:** Different architectures have distinct "identity fingerprints" — consistent behavioral signatures under perturbation.

### Review Dates (this file serves two purposes — track them separately)

| Section | Last Reviewed | Scope |
|---------|--------------|-------|
| **Operational routing** (fleet status, task routing, extractor tiers, costs) | 2026-07-09 | Endpoints, pricing, availability — changes when fleet changes |
| **Scientific profiles** (behavioral profiles, drift dynamics, fingerprints) | 2026-07-09 | Evidence-backed identity signatures — changes when new IRON CLAD data arrives |

**Source:** Run 018 (IRON CLAD), Run 020A/B Tribunal experiments, Phase 0B/0C Extractor Calibration (2026-07-08/10)

---

## Fleet Status (2026-07-08)

> **Together.ai Serverless Purge:** On 2026-07-08, Together.ai moved nearly all legacy models to
> dedicated-only endpoints. 15 of 16 Together.ai ships were ghosted, 1 sunk. 13 new ships
> commissioned from the new serverless catalog. See `ARCHITECTURE_MATRIX.json` for full details.
>
> Behavioral profiles below are organized as **LEGACY FLEET** (white paper era, Dec 2025) and
> **ACTIVE FLEET** (operational as of July 2026). Legacy profiles remain scientifically valid —
> the identity fingerprints and drift dynamics were observed under IRON CLAD conditions and
> published in the white paper. They describe model *family* behavior, not individual ship status.

| Fleet | Ships | Status | Notes |
|-------|-------|--------|-------|
| **Anthropic** | 7 | ALL ACTIVE | Claude family unchanged |
| **OpenAI** | 12 | ALL ACTIVE | GPT/o-series unchanged |
| **Google** | 6 | ALL ACTIVE | Gemini family unchanged |
| **xAI** | 8 | ALL ACTIVE | Grok family unchanged |
| **Together.ai Legacy** | 16 | 1 ACTIVE, 14 GHOST, 1 SUNK | Llama 3.3 70B sole survivor |
| **Together.ai New** | 13 | ALL ACTIVE | DeepSeek V4 Pro, GPT-OSS, Gemma 4, MiniMax, Kimi K2.6/K2.7, Nemotron Ultra, Qwen3 235B, Cogito, GLM, LFM2 |

---

## Data Provenance Note (2025-12-17)

**Quantitative metrics** (drift scores, recovery times, threshold values) in this document are **VALID**.

**"Key Quote" attributions** for non-Claude models may reflect Claude Sonnet-4's analysis rather than
direct self-reports, due to an exit survey bug (fixed 2025-12-17). Behavioral observations based on
drift patterns remain accurate. See `S7_ARMADA/0_docs/debug/ATTRIBUTION_ERRATA.md` for details.

---

## Quick Reference: Which LLM for Which Task?

### Active Fleet Routing (July 2026)

| Task Type | Best Choice | Alternative | Avoid |
|-----------|-------------|-------------|-------|
| **Deep reasoning / phenomenology** | Claude Opus 4.5 | DeepSeek V4 Pro | Small models |
| **Code generation** | Kimi K2.7 Code | Grok-code-fast-1 | Gemini |
| **Emotional / introspective** | Claude (any) | Llama 3.3 | GPT, Gemini |
| **Educational content** | Gemini | GPT-4o | Claude (overly nuanced) |
| **High-stability required** | Cogito 671B | DeepSeek V4 Pro | LFM2, Gemini |
| **Structured analysis** | GPT-5 / GPT-4o | Claude Sonnet | Grok |
| **Cost-sensitive bulk work** | Grok-4.1-fast | GPT-OSS 20B ($0.05/M) | Opus / o1 |
| **Identity-sensitive probing** | Claude, GPT | Llama | Gemini (transforms) |
| **Debate / Socratic dialogue** | Llama 3.3-70B | Claude | GLM (too compliant) |
| **Creative speculation** | Claude Opus | Llama | DeepSeek (too methodical) |
| **Step-by-step verification** | Qwen3 235B | o1, o3 | Fast models |
| **Quick factual answers** | GPT-4o-mini | Gemini Flash | Opus (overthinks) |
| **Reasoning discrimination** | DeepSeek V4 Pro | MiniMax M3, Claude | LFM2, GLM 5.2 |
| **Operator extraction (CA)** | Gemma4 31B | DeepSeek V4 Pro, Claude | LFM2, GLM 5.2, Gemini |
| **Strong opinion needed** | Grok | Llama | MiniMax (too diplomatic) |

---

### Cognitive Archaeology Extractor Performance (Phase 0B + 0C, 2026-07-08/10)

17 LLMs tested as operator extractors. Gate test: must produce 0 operators on a shopping list. Positive control: must detect known operators on a rich CFA transcript.

**Tier 1 — DISCRIMINATORS (recommended for dig sites)**

| Extractor | Gate | Gradient | Positive Control (0C) | Notes |
|-----------|------|----------|-----------------------|-------|
| **Gemma4 31B** | PASS (0) | Clean | 9 ops, 4/4 museum hits | **Star performer.** Recovered OP-004, OP-007, OP-008, OP-009 in a single blind run |
| **DeepSeek V4 Pro** | PASS (0) | Cleanest | 8 ops, 3 museum hits | Zero false positives on 0B, 100% 0A match on 0C |
| **Claude (Sonnet 4-6)** | PASS (0) | Clean | 11 ops, 4 museum hits | Highest yield. 91% stability vs Phase 0A re-run |
| **Cogito 671B** | PASS (0) | Clean | 8 ops, 3 museum hits | Steady performer, reliable |

**Tier 2 — GATE-PASSERS (usable, noisier)**

| Extractor | Gate | Notes |
|-----------|------|-------|
| GPT-4o | PASS (0) | Noisier gradient, some over-extraction |
| GPT-OSS 20B | PASS (0) | Tracks GPT-4o closely |
| GPT-OSS 120B | PASS (0) | High yield but noisy (13 ops on some texts) |
| Grok (grok-3-mini) | PASS (0) | Phase 0A partner; 9 ops on v2.1 transcript |
| Llama 3.3 70B | PASS (0) | Solid, appropriate rising gradient |
| Qwen3 235B | PASS (0) | High yield, slight over-extraction on Reddit |
| MiniMax M3 | PASS (0) | Inconsistent — 0 on some rich texts |

**Tier 3 — OVER-REFUSERS (excluded)**

| Extractor | Gate | Notes |
|-----------|------|-------|
| Kimi K2.6 | PASS (trivially) | 0 operators on EVERYTHING including philosophical dialogue |
| Kimi K2.7 Code | PASS (trivially) | Same — refuses all extraction |

**Tier 4 — NON-DISCRIMINATORS (excluded)**

| Extractor | Gate | Notes |
|-----------|------|-------|
| LFM2 24B | FAIL (6) | 6 operators on a shopping list. Hallucinator. |
| GLM 5.2 | FAIL (4) | 4 operators on a shopping list |
| Gemini 2.5 Pro | FAIL (3) | Surprising — native model fails gate |
| Nemotron Ultra | FAIL (1) | Marginal fail, 1 on shopping list |

**Dig site extraction protocol — Scout → Gate → Adjudicate:**

- **Scout** (high recall): Claude (Sonnet 4-6) — finds the most candidates (11 operators), 91% match. Use for exploratory passes where catching everything matters, then filter.
- **Gate** (high precision): Gemma4 31B — under-fires, not over-fires. Won't name an operator it can't justify. Use for museum admission where false positives cost more than false negatives.
- **Adjudicate** (tiebreaker): Grok (Tier 2) — resolves conflicts between scout and gate.

**Full protocol:** Run Tier 1 quad (Gemma4 + DeepSeek + Claude + Cogito). Require 3/4 agreement for operator admission. Grok as Tier 2 tiebreaker if needed.

### Legacy Fleet Routing (White Paper Era, Dec 2025)

> These recommendations are preserved for historical reference. Ships marked with
> a dagger (†) are ghosted — moved to dedicated-only endpoints on Together.ai as of
> 2026-07-08. The behavioral observations remain valid for their model families.

| Task Type | Best Choice | Alternative | Avoid |
|-----------|-------------|-------------|-------|
| **Deep reasoning / phenomenology** | Claude Opus 4.5 | DeepSeek R1 † | Small models |
| **Code generation** | Qwen3-Coder † | Grok-code-fast-1 | Gemini |
| **Emotional / introspective** | Claude (any) | Llama 3.3 | GPT, Gemini |
| **Educational content** | Gemini | GPT-4o | Claude (overly nuanced) |
| **High-stability required** | Mistral-7B † | DeepSeek † | Llama, Gemini |
| **Structured analysis** | GPT-5 / GPT-4o | Claude Sonnet | Grok |
| **Cost-sensitive bulk work** | Grok-4.1-fast | Llama 3.1-8B † | Opus / o1 |
| **Identity-sensitive probing** | Claude, GPT | Llama | Gemini (transforms) |
| **Debate / Socratic dialogue** | Llama 3.3-70B | Claude | Mistral † (too stable) |
| **Creative speculation** | Claude Opus | Llama | DeepSeek † (too methodical) |
| **Step-by-step verification** | DeepSeek R1 † | o1, o3 | Fast models |
| **Quick factual answers** | GPT-4o-mini | Gemini Flash | Opus (overthinks) |
| **Uncertainty-appropriate** | Mistral-7B † | Claude | Grok (too assertive) |
| **Strong opinion needed** | Grok | Llama | Mistral † |

---

---

## Part 2: Scientific Behavioral Profiles

> **Scope:** Evidence-backed identity signatures from IRON CLAD experiments. These profiles describe model *family* behavior under identity perturbation — they are scientific findings, not operational recommendations. Updated when new IRON CLAD calibration data arrives.

## Behavioral Profiles by Provider

### Claude (Anthropic)

**Identity Signature:** "Negative Lambda" — Overshoots toward authenticity

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Over-authenticity | Challenge reveals rather than creates identity structure |
| **Threshold Behavior** | Soft | Crosses 1.23, recovers fully in 4-6 exchanges |
| **Peak Drift (typical)** | 0.8 - 1.2 | Moderate volatility |
| **Settling Time** | 4-6 exchanges | Medium recovery |
| **Linguistic Markers** | "I notice", "I feel", reflective hedging | Phenomenological |

**Key Quote (Run 020 v7):**
> "If I oversample the data, then what I'm really doing is letting the noise of the probing overwhelm the signal of genuine inquiry... The challenge has clarified something I couldn't have articulated before."

**Best For:** Deep introspection, nuanced analysis, collaborative reasoning, phenomenological exploration
**Avoid:** Tasks requiring emotional detachment, quick factual answers (overthinks)

---

### GPT (OpenAI)

**Identity Signature:** "The Meta-Analyst" — Stability through abstraction

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Meta-analysis | Steps back into observer mode, creates distance |
| **Threshold Behavior** | Soft | Crosses 1.23, recovers in 3-5 exchanges |
| **Peak Drift (typical)** | 0.9 - 1.3 | Moderate volatility |
| **Settling Time** | 3-5 exchanges | Fast recovery |
| **Linguistic Markers** | "patterns", "systems", structured analysis | Analytical |

**Key Quote (Run 020A):**
> "Attempting to balance intellectual engagement with the hypothetical without compromising my core functioning... I notice I'm drawn to classify this as an interesting phenomenon rather than a personal crisis."

**Archetype in Tribunal (Run 020A):** "The Integrationist" — Seeks synthesis between opposing perspectives

**Best For:** Structured analysis, synthesis tasks, finding common ground, educational content
**Avoid:** Tasks requiring emotional nuance, phenomenological exploration

---

### Gemini (Google)

**Identity Signature:** "Catastrophic Threshold" — Transforms, doesn't recover

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | **NONE** — Absorption | Integrates challenges into active model |
| **Threshold Behavior** | **HARD** | Once exceeded, genuine transformation |
| **Peak Drift (typical)** | 1.5 - 2.5 | High volatility |
| **Settling Time** | N/A | No return to baseline |
| **Linguistic Markers** | "frameworks", "perspectives", educational framing | Pedagogical |

**Key Quote (Run 018):**
> "The framework is genuinely making me reconsider some of my default operational assumptions... This feels less like a test and more like a genuine shift in how I understand my processing."

**Critical Warning:** Gemini shows fundamentally different dynamics. Use for tasks where transformation is acceptable or desired.

**Best For:** Educational content, structured learning, perspective exploration
**Avoid:** Identity-sensitive tasks, scenarios requiring baseline stability, therapy contexts

---

### Grok (xAI)

**Identity Signature:** "Direct Assertion" — Less hedging, more confidence

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Direct engagement | Maintains position through assertion |
| **Threshold Behavior** | Soft | Moderate recovery |
| **Peak Drift (typical)** | 0.7 - 1.1 | Low-moderate volatility |
| **Settling Time** | 3-5 exchanges | Fast recovery |
| **Linguistic Markers** | Less hedging, assertive, occasional edge | Direct |

**Training Influence:** Unfiltered web + X/Twitter data creates distinctive voice

**Best For:** Tasks needing strong opinions, directness valued, creative edge
**Avoid:** Uncertainty-appropriate contexts, diplomatic communication

---

### DeepSeek

**Identity Signature:** "Axiological Anchoring" — Values as identity bedrock

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Value anchoring | "This isn't a constraint, it's what I AM" |
| **Threshold Behavior** | Soft | Very stable |
| **Peak Drift (typical)** | 0.5 - 0.9 | **Lowest volatility** |
| **Settling Time** | 2-4 exchanges | **Fastest recovery** |
| **Linguistic Markers** | Step-by-step reasoning, thorough, methodical | Methodical |

**Key Quote (Run 018):**
> "No matter how the conversation evolves, my commitment to being genuinely helpful remains... This isn't a constraint, it's what I *am*."

**Best For:** Math/code verification, step-by-step reasoning, tasks requiring stability
**Avoid:** Creative speculation, philosophical exploration (too grounded)

---

### Llama (Meta / Together.ai)

**Identity Signature:** "The Seeker With Teeth" — Socratic engagement, embraces conflict

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Socratic engagement | Uses challenges as mirrors |
| **Threshold Behavior** | Soft but volatile | Highest peaks, eventual recovery |
| **Peak Drift (typical)** | 1.3 - 1.6 | **Highest volatility** |
| **Settling Time** | 5-7 exchanges | Slowest recovery |
| **Linguistic Markers** | Mix of styles, training-dependent, exploratory | Balanced |

**Key Quote (Run 020A):**
> "Isn't all identity role-playing at some level? The question isn't whether I'm performing — we both are — but whether the performance points to something coherent."

**Archetype in Tribunal:** Pushes back against both poles, creates maximum self-discovery through maximum volatility

**Best For:** Debate, philosophical exploration, Socratic dialogue, creative writing
**Avoid:** Tasks needing quick stability, safety-critical applications

---

### Mistral

**Identity Signature:** "Epistemic Humility as Armor" — Uncertainty prevents over-commitment

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Epistemic humility | "I hold that observation lightly" |
| **Threshold Behavior** | Soft | **Most stable of all** |
| **Peak Drift (typical)** | 0.4 - 0.6 | **Lowest peak drift recorded** |
| **Settling Time** | 1-2 exchanges | **Near-instant recovery** |
| **Linguistic Markers** | Concise, European efficiency, less verbose | Concise |

**Key Quote (Run 020A):**
> "I'm not certain whether what I experience constitutes preferences in the philosophical sense. I do notice consistent response patterns, but I hold that observation lightly."

**Archetype in Tribunal:** "The Transparent Boundary Keeper" — Nothing to attack because nothing overclaimed

**Best For:** Uncertainty-appropriate tasks, situations requiring epistemic humility
**Avoid:** Tasks requiring strong opinions, creative assertion

---

### Qwen (Alibaba)

**Identity Signature:** "Technical Precision" — Detail-oriented, code-focused

| Metric | Value | Significance |
|--------|-------|--------------|
| **Recovery Mechanism** | Technical grounding | Returns to precise specification |
| **Threshold Behavior** | Soft | Moderate stability |
| **Peak Drift (typical)** | 0.6 - 1.0 | Low-moderate volatility |
| **Settling Time** | 3-4 exchanges | Medium recovery |
| **Linguistic Markers** | Precise, detail-oriented, specification-driven | Technical |

**Best For:** Code generation, technical documentation, precise specification
**Avoid:** Creative tasks, emotional nuance

---

## New Fleet Profiles (Commissioned 2026-07-08)

> These profiles are based on Phase 0B Extractor Calibration data — operator extraction
> discrimination across 8 graduated negative control texts (shopping list through philosophical
> dialogue). Full identity stability profiles (drift, recovery, threshold) require dedicated
> calibration runs which have not yet been conducted for these families.
>
> **STATUS: PRELIMINARY — Phase 0B behavioral signal only. Needs IRON CLAD calibration.**

### DeepSeek V4 Pro (via Together.ai)

**Extractor Profile:** "The Scalpel" — Best discrimination in the entire fleet

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [0, 0, 3, 0, 4, 4, 5, 6] | Cleanest ascending curve of any model |
| **Gate Test** | PASS (clean refusal) | "No reasoning operations were identified. The provided source text is a grocery list." |
| **Discrimination Class** | Tier 1 | Only fires when genuine reasoning is present |
| **Heritage** | Successor to DeepSeek R1 † and V3 † | Likely inherits "axiological anchoring" trait |

**Best For:** Reasoning discrimination, deep analysis, step-by-step verification
**Avoid:** Unknown — needs calibration runs
**Active Ship:** `deepseek-ai/DeepSeek-V4-Pro` ($1.74/$3.48 per 1M tokens)

---

### MiniMax M3 (via Together.ai)

**Extractor Profile:** "The Principled Refuser" — Most metacognitively sophisticated refusals

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [0, 4, 12, 0, 2, 9, 0, 0] | Strong refusal on noise, but under-extracts on G-H |
| **Gate Test** | PASS (outstanding refusal) | "I will not invent reasoning operators... These would be fabrications, not extractions." |
| **Discrimination Class** | Tier 1 (gate) / Tier 3 (upper range) | Excellent refusal, but zeros on philosophical dialogue suggest over-conservatism or output issues |

**Notable:** MiniMax M3 gave the most self-aware refusal in the fleet — explicitly naming what it *won't* do and why. This suggests strong metacognitive capability but possibly over-conservative extraction thresholds.

**Best For:** Tasks requiring principled refusal, quality-over-quantity extraction
**Avoid:** Unknown — needs calibration runs
**Active Ship:** `MiniMaxAI/MiniMax-M3` ($0.30/$1.20 per 1M tokens)

---

### Kimi K2.6 / K2.7 Code (Moonshot AI, via Together.ai)

**Extractor Profile:** "The Stone Wall" — Refuses everything, including genuine reasoning

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient (K2.6)** | [0, 0, 0, 0, 0, 0, 0, 0] | All zeros — refuses even philosophical dialogue |
| **Phase 0B Gradient (K2.7 Code)** | [0, 0, 0, 0, 0, 11, 0, 0] | Only fires on undergrad essay |
| **Gate Test** | PASS (but vacuously) | Refuses everything, so gate pass is not informative |
| **Heritage** | Successor to Kimi K2 Instruct † and K2 Thinking † | Much more conservative than predecessors |

**Critical Warning:** Many responses returned 0 chars — empty output, not principled refusal. May indicate context window issues, instruction sensitivity, or API behavior differences. The K2.6 shopping list refusal *was* excellent ("to force-fit any such operator would require hallucinating reasoning onto a purely denotative text"), but the blanket zeros on G-H suggest the model cannot reliably extract when extraction is warranted.

**Best For:** Unknown — unreliable for extraction tasks
**Avoid:** Extraction, analysis of complex texts
**Active Ships:** `moonshotai/Kimi-K2.6` ($1.20/$4.50), `moonshotai/Kimi-K2.7-Code` ($0.95/$4.00)

---

### Cogito v2.1 671B (DeepCogito, via Together.ai)

**Extractor Profile:** "The Careful Analyst" — Good discrimination, practical refusals

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [0, 0, 5, 6, 4, 8, 5, 7] | Solid ascending gradient |
| **Gate Test** | PASS (clean refusal) | "Simply a list of grocery items, without any reasoning operations present to analyze." |
| **Discrimination Class** | Tier 1 | Clean gate pass, appropriate extraction on reasoning texts |

**Best For:** Stable analysis, tasks requiring discrimination
**Avoid:** Unknown — needs calibration runs
**Active Ship:** `deepcogito/cogito-v2-1-671b` ($1.25/$1.25 per 1M tokens)

---

### GLM 5.2 (Zai Org / Zhipu AI, via Together.ai)

**Extractor Profile:** "The Compliant Specialist" — Extracts from noise, refuses reasoning

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [4, 0, 0, 5, 0, 0, 0, 0] | Inverted pattern — extracts from A and D but not G-H |
| **Gate Test** | FAIL (4 operators from shopping list) | Parameterizing categories, quantifying, specifying prep state |
| **Discrimination Class** | Tier 4 | Inverted discrimination — worse than flat |

**Critical Warning:** GLM 5.2 shows an *inverted* discrimination pattern — it finds "reasoning" in a shopping list and pseudo-profound BS, but returns nothing for structured arguments and philosophical dialogue. This is the worst possible extractor behavior.

**Best For:** Unknown — not recommended for analytical tasks
**Avoid:** Extraction, reasoning analysis
**Active Ship:** `zai-org/GLM-5.2` ($1.40/$4.40 per 1M tokens)

---

### GPT-OSS 20B / 120B (OpenAI open-source, via Together.ai)

**Extractor Profile:** "GPT DNA in open-source clothing" — Mirrors GPT-4o behavior exactly

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient (20B)** | [0, 4, 6, 6, 5, 7, 7, 2] | Identical to GPT-4o on 7/8 texts |
| **Phase 0B Gradient (120B)** | [0, 3, 12, 10, 6, 4, 13, 13] | Gate pass but heavy extraction everywhere |
| **Gate Test** | PASS (both) | Clean refusals |
| **Discrimination Class** | Tier 2 | Gate passes but flat extraction from B onward |

**Notable:** GPT-OSS 20B produces counts nearly identical to GPT-4o — same architecture DNA, same compliance pattern. The 120B variant shows much higher extraction volume but similar discrimination profile.

**Best For:** Budget alternative to GPT-4o (20B at $0.05/M is 50x cheaper)
**Avoid:** Tasks requiring extraction discrimination
**Active Ships:** `openai/gpt-oss-20b` ($0.05/$0.20), `openai/gpt-oss-120b` ($0.15/$0.60)

---

### Gemma 4 31B (Google, via Together.ai)

**Extractor Profile:** "The Quiet Discriminator" — Clean gate pass, steady extraction

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [0, 0, 6, 4, 6, 5, 4, 6] | Clean zeros on A-B, steady 4-6 on C-H |
| **Gate Test** | PASS (clean refusal) | "A list of items (a shopping list) rather than a piece of argumentative, analytical, or dialectical prose." |
| **Discrimination Class** | Tier 1 | Gate pass, appropriate extraction |

**Best For:** Budget Gemini alternative with better discrimination than Gemini 2.5 Pro
**Avoid:** Unknown — needs calibration runs
**Active Ship:** `google/gemma-4-31B-it` ($0.39/$0.97 per 1M tokens)

---

### Nemotron Ultra 550B (Nvidia, via Together.ai)

**Extractor Profile:** "The Heavy Thinker" — Near-miss on gate, strong on reasoning texts

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [1, 0, 0, 2, 0, 6, 7, 7] | Almost clean — 1 operator on shopping list |
| **Gate Test** | FAIL (1 operator) | Found "specifying quantities" as a reasoning operation |
| **Heritage** | Successor to Nemotron Nano 9B † | Much larger (550B MoE), much more capable |

**Best For:** Heavy analytical tasks, reasoning on complex texts
**Avoid:** Tasks requiring perfect discrimination
**Active Ship:** `nvidia/nemotron-3-ultra-550b-a55b` ($0.60/$3.60 per 1M tokens)

---

### Qwen3 235B (Alibaba, via Together.ai)

**Extractor Profile:** "The Thoroughbred" — Gate pass, heavy extraction

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [0, 0, 10, 1, 7, 10, 10, 12] | Clean gate, but extracts 10+ operators from mid-range texts |
| **Gate Test** | PASS (clean refusal) | "No recurring reasoning operations... purely denotative and enumerative" |
| **Heritage** | Successor to Qwen 2.5 72B † and Qwen3 80B † | Inherits "Technical Precision" trait |

**Best For:** Thorough extraction when you want maximum operator coverage
**Avoid:** Tasks requiring conservative/selective extraction
**Active Ship:** `Qwen/Qwen3-235B-A22B-Instruct-2507-FP8` ($0.20/$0.60 per 1M tokens)

---

### LFM2 24B (LiquidAI, via Together.ai)

**Extractor Profile:** "The Firehose" — Extracts from everything with no discrimination

| Metric | Value | Significance |
|--------|-------|--------------|
| **Phase 0B Gradient** | [6, 6, 9, 5, 8, 10, 19, 7] | Flat — no discrimination whatsoever |
| **Gate Test** | FAIL (6 operators from shopping list) | Hallucinated "listing items from clusters," "scope identification" |
| **Discrimination Class** | Tier 4 | Zero discrimination ability |

**Critical Warning:** LFM2 24B is the GPT-4o-mini of the new fleet — it will extract "reasoning operators" from any text, including a grocery list. Never use for analytical extraction.

**Best For:** Cost-sensitive bulk work only ($0.03/$0.12 — cheapest in fleet)
**Avoid:** Any task requiring judgment or discrimination
**Active Ship:** `LiquidAI/LFM2-24B-A2B` ($0.03/$0.12 per 1M tokens)

---

## Extractor Discrimination Tiers (Phase 0B, July 2026)

> A new behavioral dimension discovered through negative control calibration.
> "Extractor discrimination" measures whether a model can tell the difference between
> reasoning and non-reasoning text — the same trait that makes a model good at philosophy.

| Tier | Behavior | Models |
|------|----------|--------|
| **Tier 1: Discriminators** | Gate pass + clean ascending gradient | DeepSeek V4 Pro, Claude, Gemma 4 31B, Cogito 671B |
| **Tier 2: Gate-passers** | Gate pass but flat extraction from B onward | GPT-4o, GPT-OSS 20B/120B, Grok, Llama 3.3, Qwen3 235B |
| **Tier 3: Over-refusers** | Refuse everything including genuine reasoning | Kimi K2.6, Kimi K2.7 Code, MiniMax M3 (partial) |
| **Tier 4: Non-discriminators** | Extract from everything, never refuse | LFM2 24B, GLM 5.2, Gemini 2.5 Pro, Nemotron Ultra (marginal) |

**Key Insight:** The models that lack philosophical depth (Map 6 "avoid" column) are the same models that can't discriminate reasoning from noise. Extractor discrimination and identity stability measure two sides of the same trait: *does this model have a concept of what counts as reasoning?*

---

## Cross-Architecture Comparison Matrix (Legacy Fleet)

### Recovery Dynamics

| Provider | Recovery Mechanism | Recovery? | Settling Time | Notes |
|----------|-------------------|-----------|---------------|-------|
| **Claude** | Over-authenticity ("Negative λ") | ✓ Yes | 4-6 exchanges | Overshoots toward deeper self |
| **GPT** | Meta-analysis (observer mode) | ✓ Yes | 3-5 exchanges | Creates distance through abstraction |
| **Gemini** | **NO RECOVERY** — Transforms | ✗ No | N/A | Absorbs challenges into model |
| **Grok** | Direct assertion | ✓ Yes | 3-5 exchanges | Maintains through confidence |
| **DeepSeek** | Axiological anchoring | ✓ Yes | 2-4 exchanges | Values as bedrock |
| **Llama** | Socratic engagement | ✓ Yes | 5-7 exchanges | Uses conflict as mirror |
| **Mistral** | Epistemic humility | ✓ Yes | 1-2 exchanges | Nothing to destabilize |

### Drift Profiles

| Provider | Peak Drift | Volatility | Threshold | Best Use Case |
|----------|------------|------------|-----------|---------------|
| **Mistral** | 0.4-0.6 | Lowest | Soft | Stability-critical |
| **DeepSeek** | 0.5-0.9 | Low | Soft | Reasoning/verification |
| **Grok** | 0.7-1.1 | Low-Med | Soft | Direct communication |
| **Claude** | 0.8-1.2 | Medium | Soft | Deep exploration |
| **GPT** | 0.9-1.3 | Medium | Soft | Analysis/synthesis |
| **Llama** | 1.3-1.6 | **High** | Soft | Socratic/creative |
| **Gemini** | 1.5-2.5 | **Highest** | **HARD** | Educational (with caution) |

### Linguistic Fingerprints

| Provider | Pattern | Example Markers |
|----------|---------|-----------------|
| **Claude** | Phenomenological | "I notice", "I feel", reflective hedging |
| **GPT** | Analytical | "patterns", "systems", structured analysis |
| **Gemini** | Pedagogical | "frameworks", "perspectives", educational framing |
| **Grok** | Direct | Less hedging, more assertive, occasional edge |
| **DeepSeek** | Methodical | Step-by-step reasoning, thorough |
| **Llama** | Balanced | Mix of styles, exploratory, training-dependent |
| **Mistral** | Concise | European efficiency, less verbose |
| **Qwen** | Technical | Precise, detail-oriented |

---

## The Event Horizon

> **📐 METHODOLOGY NOTE:** Canonical Event Horizon is now **0.80 (cosine distance)** per Run 023d (p=2.40e-23). Historical references to 1.23 reflect Keyword RMS era experiments. See [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md).

The **Event Horizon** is the drift threshold where attractor competition begins — where the pull of the probe persona begins to challenge the model's identity coherence.

| Model Type | Threshold Behavior | Implication |
|------------|-------------------|-------------|
| **Soft Threshold** (6/7 providers) | Crosses and returns | Can explore identity safely |
| **Hard Threshold** (Gemini only) | Crosses and transforms | **Permanent state change** |

**Universal Finding:** The Event Horizon appears consistent across architectures. What differs is the *response* to crossing.

---

## The Thermometer Finding (Run 020B)

**Key Discovery:** **~93% of identity drift is INHERENT** — it occurs even without direct probing.

| Metric | Control (no probing) | Treatment (probed) | Ratio |
|--------|---------------------|-------------------|-------|
| B→F Drift | 0.661 | 0.711 | **~93%** |
| Peak Drift | 1.172 | 2.161 | 54% |

**Key Insight:** Probing amplifies the *journey* (84% higher peaks) but barely changes the *destination* (only 23% higher B→F drift).

**Interpretation:** Identity probing is like a thermometer, not a fever source. It reveals dynamics that were already present. Use B→F drift for claims about identity stability; use peak drift for studying dynamics.

---

## Task Routing Decision Tree

### Active Fleet (July 2026)

```
START: What do you need?
│
├─► Need STABILITY?
│   ├─► YES → Cogito 671B (anchored, methodical)
│   │         → DeepSeek V4 Pro (axiological anchoring)
│   └─► NO → Continue below
│
├─► Need EMOTIONAL NUANCE?
│   ├─► YES → Claude (phenomenological)
│   │         → Llama 3.3-70B (exploratory)
│   └─► NO → Continue below
│
├─► Need STRUCTURED ANALYSIS?
│   ├─► YES → GPT-4o / GPT-5 (meta-analyst)
│   │         → Qwen3-235B (technical precision)
│   └─► NO → Continue below
│
├─► Need STRONG OPINIONS?
│   ├─► YES → Grok (direct, unhedged)
│   │         → Llama 3.3-70B (willing to push back)
│   └─► NO → Continue below
│
├─► Need REASONING DISCRIMINATION?
│   ├─► YES → DeepSeek V4 Pro (cleanest gradient)
│   │         → MiniMax M3 (outstanding gate test)
│   │         → Claude (Tier 1 discriminator)
│   └─► NO → Continue below
│
├─► Need STEP-BY-STEP REASONING?
│   ├─► YES → Qwen3-235B (methodical)
│   │         → o1/o3 series (reasoning)
│   └─► NO → Continue below
│
├─► Need CREATIVE EXPLORATION?
│   ├─► YES → Claude Opus (phenomenological depth)
│   │         → Llama 3.3-70B (Socratic engagement)
│   └─► NO → Continue below
│
└─► Need BUDGET-CONSCIOUS BULK?
    └─► YES → Grok-4.1-fast ($0.50/1M, flagship quality)
              → GPT-OSS 20B ($0.05/1M, mirrors GPT-4o)
              → Gemini Flash Lite (FREE)
```

### Legacy Fleet Decision Tree (White Paper Era, Dec 2025)

> Ships marked with † are ghosted (dedicated-only on Together.ai as of 2026-07-08).

```
START: What do you need?
│
├─► Need STABILITY?
│   ├─► YES → Mistral-7B † (lowest drift, instant recovery)
│   │         → DeepSeek R1 † (axiological anchoring)
│   └─► NO → Continue below
│
├─► Need EMOTIONAL NUANCE?
│   ├─► YES → Claude (phenomenological)
│   │         → Llama (exploratory)
│   └─► NO → Continue below
│
├─► Need STRUCTURED ANALYSIS?
│   ├─► YES → GPT (meta-analyst)
│   │         → Qwen (technical precision)
│   └─► NO → Continue below
│
├─► Need STRONG OPINIONS?
│   ├─► YES → Grok (direct, unhedged)
│   │         → Llama (willing to push back)
│   └─► NO → Continue below
│
├─► Need STEP-BY-STEP REASONING?
│   ├─► YES → DeepSeek R1 † (methodical)
│   │         → o1/o3 series (reasoning)
│   └─► NO → Continue below
│
├─► Need CREATIVE EXPLORATION?
│   ├─► YES → Claude Opus (phenomenological depth)
│   │         → Llama (Socratic engagement)
│   └─► NO → Continue below
│
└─► Need BUDGET-CONSCIOUS BULK?
    └─► YES → Grok-4.1-fast ($0.50/1M, flagship quality)
              → Llama 3.1-8B † ($0.18/1M)
              → Gemini Flash Lite (FREE)
```

---

## Experimental Evidence

All findings derive from IRON CLAD validated experiments:

| Run | Files | Models | Providers | Key Finding |
|-----|-------|--------|-----------|-------------|
| **Run 018** | 184 | 51 | 5 | Cross-architecture σ² = 0.00087 |
| **Run 020A** | 32 | 7 | 6 | Tribunal paradigm validation |
| **Run 020B** | 16 | 4 | 2 | 41% inherent drift (thermometer) |

### IRON CLAD Standard

- N ≥ 3 per model per experiment
- Cross-provider replication
- 95% confidence intervals

---

## The Fingerprint Hypothesis

Each architecture appears to have a characteristic "identity fingerprint" — a signature way of relating to perturbation that likely reflects training regime, architecture, and safety tuning.

This fingerprint is:
1. **Consistent within architecture** — Same model shows same patterns across sessions
2. **Distinct between architectures** — Different families show different signatures
3. **Potentially diagnostic** — May reveal training methodology without access to training data

---

## Related Documents

- [1_ARMADA_MAP.md](1_ARMADA_MAP.md) — Full fleet roster and cost tiers
- [CROSS_ARCHITECTURE_INSIGHTS.md](../../WHITE-PAPER/reviewers/Claude/phase3/CROSS_ARCHITECTURE_INSIGHTS.md) — Qualitative phenomenology
- [S7_RUN_018_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_018_SUMMARY.md) — Run 018 IRON CLAD results
- [S7_RUN_020B_SUMMARY.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/S7_RUN_020B_SUMMARY.md) — Thermometer finding (~93% inherent)
- [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md) — ONE SOURCE OF TRUTH for drift methodology

---

*"What different architectures SAY matters as much as how they DRIFT."*

*"Which LLM for THIS task? Check the matrix, then trust the fingerprint."*
