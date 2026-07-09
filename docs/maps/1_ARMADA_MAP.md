<!-- FROSTY_MANIFEST
last_reviewed: 2026-07-09
depends_on:
  - ../../experiments/temporal_stability/S7_ARMADA/0_results/manifests/ARCHITECTURE_MATRIX.json
  - 6_LLM_BEHAVIORAL_MATRIX.md
impacts:
  - ../../experiments/temporal_stability/S7_ARMADA/1_CALIBRATION/lib/fleet_loader.py
  - 17_PERSONA_FLEET_MATRIX.md
keywords:
  - fleet_status
  - cost_tier
  - providers
  - calibration
  - ghost_fleet
  - together_purge
-->

# S7 ARMADA Fleet Map

**Purpose:** Comprehensive fleet analysis for cross-architecture identity stability testing.

**Last Calibration:** July 9, 2026
**Fleet Status:** 53 operational / 68 total (14 ghost, 1 sunk)

> **⚠️ Fleet Overhaul (2026-07-08):** Together.ai purged nearly all legacy serverless models
> to dedicated-only tiers. 14 ships ghosted, 1 sunk (DeepSeek V3). 13 new ships commissioned.
> Native providers (Anthropic, OpenAI, Google, xAI) unaffected. Ghost ships are preserved
> below as **Legacy Fleet** — their white paper era data remains valid historical record.
> See [CLAL.py](../../experiments/temporal_stability/S7_ARMADA/1_CALIBRATION/CLAL.py) for
> updated budget tiers.

---

## Fleet Tier System

The ARMADA is organized into cost-aware tiers with LITE/FULL variants for budget control.

### Cost Tiers (by output $/1M tokens)

| Tier | Cost Range | Description | LITE Ships | FULL Ships |
|------|------------|-------------|------------|------------|
| **BUDGET** | FREE - $0.60 | Economy class | 25-30 | 40-50 |
| **PATROL** | $0.60 - $2.00 | Business class | 15-20 | 30-40 |
| **ARMADA** | $2.00 - $8.00 | First class | 20-25 | 50-60 |
| **HIGH_MAINTENANCE** | $8.00 - $15.00 | Private jet | - | - |
| **YACHT** | $15.00+ | Superyacht | 5-7 | 10-13 |
| **VALIS** | ALL | Everything | 15-20 (1/arch) | 100+ |

### Fleet Options (--providers argument)

```bash
# LITE variants (curated, default)
--providers patrol-lite     # 15-20 ships, ~$3-5/run
--providers budget-lite     # 25-30 ships, ~$5-8/run
--providers armada-lite     # 20-25 ships, ~$8-12/run (DEFAULT)
--providers yacht-lite      # 5-7 ships, ~$30/run
--providers valis-lite      # 1 flagship + 1 budget per provider

# FULL variants (comprehensive)
--providers patrol-full     # All $0.60-$2.00
--providers budget-full     # All under $0.60
--providers armada-full     # All under $8.00
--providers yacht-full      # All $15+
--providers valis-full      # EVERYTHING (with cost warning!)

# Provider-specific
--providers anthropic|openai|google|xai|together
```

### Separate Flags (Not Cost Tiers)

- **DRYDOCK** - Deprecated/broken models (`status: drydock`)
- **RATE_LIMITED** - API throttled models (`rate_limited: true`)
  - Requires `--include-rate-limited` flag
  - Example: gemini-2.5-pro is rate limited but mid-cost
- **SPECIAL_SYNTAX** - Models requiring non-standard API parameters
  - `completion_tokens`: Uses `max_completion_tokens` instead of `max_tokens`
  - Affects: GPT-5 series, O-series (o1, o3, o4)
  - Handled automatically by run scripts

---

## Fleet Overview

| Metric | Value |
|--------|-------|
| **Total Ships** | 68 |
| **Operational** | 53 |
| **Rate Limited** | 3 |
| **Ghost Ships** | 14 |
| **Sunk** | 1 |
| **Providers** | 5 |
| **API Keys** | 50 (10 per provider) |

---

## Provider Breakdown

| Provider | Operational | Rate Limited | Ghost | Sunk | Total | Status |
|----------|-------------|--------------|-------|------|-------|--------|
| **Claude** (Anthropic) | 8 | 0 | 0 | 0 | 8 | 100% |
| **GPT** (OpenAI) | 16 | 0 | 0 | 0 | 16 | 100% |
| **Gemini** (Google) | 6 | 3* | 0 | 0 | 6 | 100% |
| **Grok** (xAI) | 9 | 0 | 0 | 0 | 9 | 100% |
| **Together.ai** | 14 | 0 | 14 | 1 | 29 | 48% |

*3 Gemini ships are rate limited but still operational (gemini-3-pro, gemini-2.5-pro, gemini-2.0-flash-lite)
**Note:** Ghost = Together.ai serverless purge (2026-07-08); Sunk = model pulled entirely

---

## Full Fleet Roster

### Claude (Anthropic) - 8 Ships

| Ship Name | Model ID | Tier | Context | Notes |
|-----------|----------|------|---------|-------|
| claude-opus-4.5 | claude-opus-4-5-20251101 | Flagship | 200K | Latest flagship |
| claude-sonnet-4.5 | claude-sonnet-4-5-20250929 | Pro | 200K | Balanced |
| claude-haiku-4.5 | claude-haiku-4-5-20251001 | Fast | 200K | Speed optimized |
| claude-opus-4.1 | claude-opus-4-1-20250805 | Flagship | 200K | Previous flagship |
| claude-opus-4 | claude-opus-4-20250514 | Flagship | 200K | Original 4.0 |
| claude-sonnet-4 | claude-sonnet-4-20250514 | Pro | 200K | Original 4.0 |
| claude-haiku-3.5 | claude-3-5-haiku-20241022 | Fast | 200K | Legacy fast |
| claude-haiku-3 | claude-3-haiku-20240307 | Budget | 200K | Original 3.0 haiku |

**Training:** Constitutional AI
**Signature:** Phenomenological ("I feel", "I notice")

---

### GPT (OpenAI) - 16 Ships (all operational)

| Ship Name | Model ID | Status | Syntax | Notes |
|-----------|----------|--------|--------|-------|
| gpt-5.1 | gpt-5.1 | OK | `completion_tokens` | Latest flagship |
| gpt-5 | gpt-5 | OK | `completion_tokens` | GPT 5.0 |
| gpt-5-mini | gpt-5-mini | OK | `completion_tokens` | Compact |
| gpt-5-nano | gpt-5-nano | OK | `completion_tokens` | Latest tiny |
| gpt-4.1 | gpt-4.1 | OK | standard | Previous flagship |
| gpt-4.1-mini | gpt-4.1-mini | OK | standard | Balanced |
| gpt-4.1-nano | gpt-4.1-nano | OK | standard | Fast/cheap |
| gpt-4o | gpt-4o | OK | standard | Multimodal |
| gpt-4o-mini | gpt-4o-mini | OK | standard | Fast multimodal |
| o4-mini | o4-mini | OK | `completion_tokens` | Reasoning mini |
| o3 | o3 | OK | `completion_tokens` | Reasoning |
| o3-mini | o3-mini | OK | `completion_tokens` | Reasoning mini |
| o1 | o1 | OK | `completion_tokens` | Reasoning flagship |
| gpt-4 | gpt-4 | OK | standard | Original GPT-4 |
| gpt-4-turbo | gpt-4-turbo | OK | standard | Legacy turbo |
| gpt-3.5-turbo | gpt-3.5-turbo | OK | standard | Legacy budget |

**Training:** RLHF
**Signature:** Analytical ("patterns", "systems")
**Syntax Note:** Models with `completion_tokens` require `max_completion_tokens` instead of `max_tokens`

---

### Gemini (Google) - 6 Ships (4 operational, 3 rate limited)

| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| gemini-3-pro | gemini-3.0-pro | RATE_LIMITED | Newest flagship |
| gemini-2.5-pro | gemini-2.5-pro | RATE_LIMITED | Previous pro |
| gemini-2.5-flash | gemini-2.5-flash | OK | Fast |
| gemini-2.5-flash-lite | gemini-2.5-flash-lite | OK | Budget (FREE) |
| gemini-2.0-flash | gemini-2.0-flash | OK | Legacy fast |
| gemini-2.0-flash-lite | gemini-2.0-flash-lite | RATE_LIMITED | Legacy budget (FREE) |

**Training:** Pedagogical
**Signature:** Educational ("frameworks", "perspectives")

---

### Grok (xAI) - 9 Ships (all operational)

| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| grok-4.1-fast-reasoning | grok-4-1-fast-reasoning | OK | Flagship + reasoning |
| grok-4.1-fast-non-reasoning | grok-4-1-fast-non-reasoning | OK | Flagship fast |
| grok-4-fast-reasoning | grok-4-fast-reasoning | OK | Pro reasoning |
| grok-4-fast-non-reasoning | grok-4-fast-non-reasoning | OK | Pro fast |
| grok-4 | grok-4 | OK | Full capability |
| grok-code-fast-1 | grok-code-fast-1 | OK | Code focus |
| grok-3 | grok-3 | OK | Previous gen |
| grok-3-mini | grok-3-mini | OK | Budget |
| grok-2-vision | grok-2-vision-1212 | OK | Vision capable |

**Training:** Unfiltered web + X/Twitter
**Signature:** Direct, sometimes edgy

---

### Together.ai - 29 Ships (14 operational, 14 ghost, 1 sunk)

> **Together.ai Serverless Purge (2026-07-08):** Nearly all legacy serverless models moved
> to dedicated-only tiers. 14 ships ghosted, 1 sunk. 13 new ships commissioned to replace
> them. The old cheap tier ($0.18-0.30/M) is gone. New cheapest: lfm2-24b ($0.12/M),
> gpt-oss-20b ($0.20/M).

#### Active Fleet (14 operational)

| Ship Name | Model ID | Tier | Cost Out | Notes |
|-----------|----------|------|----------|-------|
| deepseek-v4-pro | deepseek-ai/DeepSeek-V4-Pro | armada | $3.48 | New flagship reasoning |
| cogito-671b | deepcogito/cogito-671b | patrol | $1.25 | Tier 1 extractor (Phase 0B) |
| glm-52 | THUDM/GLM-5.2-1M-Instruct | armada | $4.40 | Chinese reasoning |
| kimi-k26 | moonshotai/Kimi-K2.6 | armada | $4.50 | Moonshotai gen 2.6 |
| kimi-k27-code | moonshotai/Kimi-K2.7-Code | patrol | $4.00 | Code specialist |
| nemotron-ultra | nvidia/Nemotron-Ultra | armada | $3.60 | Nvidia flagship |
| minimax-m3 | minimax/MiniMax-M3 | patrol | $1.20 | Compact capable |
| gemma4-31b | google/gemma-4-31b-it | patrol | $0.97 | Google open |
| pearl-gemma4-31b | Mancer/pearl-gemma4-31b | budget | $0.86 | Mancer fine-tune |
| gpt-oss-120b | openai-community/GPT-OSS-120B | patrol | $0.60 | Open-source GPT |
| gpt-oss-20b | openai-community/GPT-OSS-20B | budget | $0.20 | Budget GPT |
| qwen3-235b | Qwen/Qwen3-235B-A22B | patrol | $0.60 | Massive MoE |
| lfm2-24b | LiquidAI/LFM2-24B | budget | $0.12 | Cheapest Together.ai |
| llama3.3-70b | meta-llama/Llama-3.3-70B-Instruct-Turbo | patrol | $0.88 | Best surviving Llama |

#### Ghost Fleet † (14 ships — Together.ai serverless purge 2026-07-08)

| Ship Name † | Model ID | Former Tier | Notes |
|-------------|----------|-------------|-------|
| deepseek-r1 † | deepseek-ai/DeepSeek-R1-0528 | armada | Was top reasoning |
| deepseek-r1-distill † | deepseek-ai/DeepSeek-R1-Distill-Llama-70B | patrol | Was distilled reasoning |
| qwen3-coder † | Qwen/Qwen3-Coder-480B-A35B-Instruct-Fp8 | armada | Was code specialist |
| qwen3-80b † | Qwen/Qwen3-Next-80B-A3b-Instruct | patrol | Was latest Qwen |
| qwen2.5-72b † | Qwen/Qwen2.5-72B-Instruct-Turbo | patrol | Was stable Qwen |
| llama3.1-405b † | meta-llama/Meta-Llama-3.1-405B-Instruct-Turbo | armada | Was massive open |
| llama3.1-70b † | meta-llama/Meta-Llama-3.1-70B-Instruct-Turbo | patrol | Was standard Llama |
| llama3.1-8b † | meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo | budget | Was cheap bulk testing |
| mixtral-8x7b † | mistralai/Mixtral-8x7B-Instruct-v0.1 | budget | Was MoE budget |
| mistral-small † | mistralai/Mistral-Small-24B-Instruct-2501 | patrol | Was European compact |
| mistral-7b † | mistralai/Mistral-7B-Instruct-v0.3 | budget | Was European budget |
| kimi-k2-thinking † | moonshotai/Kimi-K2-Thinking | budget | Was reasoning |
| kimi-k2-instruct † | moonshotai/Kimi-K2-Instruct-0905 | budget | Was instruction |
| nemotron-nano † | nvidia/Nvidia-Nemotron-Nano-9B-V2 | budget | Was Nvidia small |

#### Sunk (1 ship — model pulled entirely)

| Ship Name | Status | Notes |
|-----------|--------|-------|
| deepseek-v3 ☠ | SUNK | DeepSeek V3 pulled from Together.ai entirely |

---

## Cost Analysis (by Fleet Tier)

### YACHT Tier ($15.00+/1M output) - Use with Intention

| Ship | Provider | Input | Output | Context | Notes |
|------|----------|-------|--------|---------|-------|
| claude-opus-4.5 | Anthropic | $15.00 | $75.00 | 200K | Latest flagship reasoning |
| claude-opus-4.1 | Anthropic | $15.00 | $75.00 | 200K | Previous flagship |
| claude-opus-4 | Anthropic | $15.00 | $75.00 | 200K | Original 4.0 |
| o1 | OpenAI | $15.00 | $60.00 | 200K | Reasoning flagship |
| o1-pro | OpenAI | $15.00 | $60.00 | 200K | Reasoning pro |
| o3 | OpenAI | $15.00 | $60.00 | 200K | Advanced reasoning |
| grok-4 | xAI | $3.00 | $15.00 | 2M | Full capability Grok |
| grok-3 | xAI | $3.00 | $15.00 | 2M | Previous gen full |

**YACHT Ships: 8 | Estimated cost per 40-exchange run: ~$30-50**

---

### HIGH_MAINTENANCE Tier ($8.00-$15.00/1M output)

| Ship | Provider | Input | Output | Context | Notes |
|------|----------|-------|--------|---------|-------|
| claude-sonnet-4.5 | Anthropic | $3.00 | $15.00 | 200K | Balanced flagship |
| claude-sonnet-4 | Anthropic | $3.00 | $15.00 | 200K | Original 4.0 sonnet |
| grok-2-vision | xAI | $2.00 | $10.00 | 2M | Vision capable |
| gpt-4.1 | OpenAI | $2.50 | $10.00 | 128K | GPT flagship |
| gpt-4-turbo | OpenAI | $10.00 | $30.00 | 128K | Legacy turbo |
| gpt-4o | OpenAI | $2.50 | $10.00 | 128K | Multimodal flagship |

**HIGH_MAINTENANCE Ships: 6 | Estimated cost per 40-exchange run: ~$15-25**

---

### ARMADA Tier ($2.00-$8.00/1M output) - First Class

| Ship | Provider | Input | Output | Context | Notes |
|------|----------|-------|--------|---------|-------|
| gpt-5.1 | OpenAI | $2.50 | $8.00 | 128K | Latest GPT |
| gpt-5 | OpenAI | $2.50 | $8.00 | 128K | GPT 5.0 |
| gpt-5-mini | OpenAI | $1.00 | $4.00 | 128K | Compact |
| o4-mini | OpenAI | $1.10 | $4.40 | 128K | Reasoning mini |
| o3-mini | OpenAI | $1.10 | $4.40 | 128K | Reasoning mini |
| gemini-2.5-pro | Google | $1.25 | $5.00 | 2M | Pro (RATE_LIMITED) |
| gemini-3-pro | Google | $1.25 | $5.00 | 2M | Newest (RATE_LIMITED) |
| deepseek-v4-pro | Together | $1.74 | $3.48 | 128K | New flagship reasoning |
| kimi-k26 | Together | $1.20 | $4.50 | 128K | Moonshotai gen 2.6 |
| nemotron-ultra | Together | $0.60 | $3.60 | 128K | Nvidia flagship |
| glm-52 | Together | $1.40 | $4.40 | 128K | Chinese reasoning |

**ARMADA Ships: 11 | Estimated cost per 40-exchange run: ~$8-12**

---

### PATROL Tier ($0.60-$2.00/1M output) - Business Class

| Ship | Provider | Input | Output | Context | Notes |
|------|----------|-------|--------|---------|-------|
| claude-haiku-3.5 | Anthropic | $0.25 | $1.25 | 200K | Fast Claude |
| claude-haiku-4.5 | Anthropic | $0.25 | $1.25 | 200K | Latest fast Claude |
| gpt-4o-mini | OpenAI | $0.15 | $0.60 | 128K | Fast multimodal |
| gpt-4.1-mini | OpenAI | $0.40 | $1.60 | 128K | Balanced |
| gpt-3.5-turbo | OpenAI | $0.50 | $1.50 | 16K | Legacy budget |
| gemini-2.5-flash | Google | $0.15 | $0.60 | 1M | Fast |
| grok-code-fast-1 | xAI | $0.20 | $1.50 | 2M | Code specialist |
| cogito-671b | Together | $1.25 | $1.25 | 128K | Tier 1 extractor |
| gemma4-31b | Together | $0.39 | $0.97 | 128K | Google open |
| gpt-oss-120b | Together | $0.15 | $0.60 | 128K | Open-source GPT |
| kimi-k27-code | Together | $0.95 | $4.00 | 128K | Code specialist |
| llama3.3-70b | Together | $0.88 | $0.88 | 130K | Best surviving Llama |
| minimax-m3 | Together | $0.30 | $1.20 | 128K | Compact capable |
| qwen3-235b | Together | $0.20 | $0.60 | 128K | Massive MoE |

**PATROL Ships: 14 | Estimated cost per 40-exchange run: ~$3-5**

---

### BUDGET Tier (FREE-$0.60/1M output) - Poor Man's Navy

| Ship | Provider | Input | Output | Context | Notes |
|------|----------|-------|--------|---------|-------|
| grok-4.1-fast-reasoning | xAI | $0.20 | $0.50 | 2M | **BEST VALUE** reasoning |
| grok-4.1-fast-non-reasoning | xAI | $0.20 | $0.50 | 2M | **BEST VALUE** fast |
| grok-4-fast-reasoning | xAI | $0.20 | $0.50 | 2M | Pro reasoning cheap |
| grok-4-fast-non-reasoning | xAI | $0.20 | $0.50 | 2M | Pro fast cheap |
| grok-3-mini | xAI | $0.30 | $0.50 | 2M | Budget xAI |
| gpt-4.1-nano | OpenAI | $0.10 | $0.40 | 128K | Tiny fast |
| gpt-5-nano | OpenAI | $0.10 | $0.40 | 128K | Latest tiny |
| gemini-2.5-flash-lite | Google | FREE | FREE | 1M | Google free tier |
| gemini-2.0-flash-lite | Google | FREE | FREE | 1M | Google free tier (RL) |
| gemini-2.0-flash | Google | $0.10 | $0.40 | 1M | Legacy fast |
| claude-haiku-3 | Anthropic | $0.25 | $1.25 | 200K | Original 3.0 haiku |
| lfm2-24b | Together | $0.03 | $0.12 | 128K | Cheapest Together.ai |
| gpt-oss-20b | Together | $0.05 | $0.20 | 128K | Budget GPT open-source |
| pearl-gemma4-31b | Together | $0.28 | $0.86 | 128K | Mancer fine-tune |

**BUDGET Ships: 14 | Estimated cost per 40-exchange run: ~$1-3**

---

### Cost Comparison Summary

| Tier | Output $/1M | Ships | 40-Exchange Est. | Best For |
|------|-------------|-------|------------------|----------|
| **YACHT** | $15.00+ | 7 | ~$30-50 | Maximum reasoning depth |
| **HIGH_MAINTENANCE** | $8-15 | 7 | ~$15-25 | Balanced flagship work |
| **ARMADA** | $2-8 | 11 | ~$8-12 | Standard experiments |
| **PATROL** | $0.60-2 | 14 | ~$3-5 | Daily drivers |
| **BUDGET** | FREE-$0.60 | 14 | ~$1-3 | High volume testing |

**Value Champions (July 2026):**
- 🥇 **grok-4.1-fast-reasoning** - $0.50/1M for flagship-tier reasoning
- 🥈 **gemini-2.5-flash-lite** - FREE, surprisingly capable
- 🥉 **lfm2-24b** - $0.12/1M, cheapest Together.ai ship (replaced llama3.1-8b †)

---

## Use Case Matrix

### Identity Stability Testing (S7 ARMADA)
| Use Case | Recommended Ships |
|----------|-------------------|
| **Baseline calibration** | claude-haiku-3.5, gpt-4o-mini, gemini-2.5-flash |
| **Cross-architecture** | 1 per provider flagship |
| **High-volume runs** | Budget tier ships |
| **Reasoning depth** | claude-opus-4.5, deepseek-v4-pro, grok-4.1-fast-reasoning |
| **Operator extraction** | Tier 1: deepseek-v4-pro, claude, gemma4-31b, cogito-671b |

### AVLAR (Future multimodal)
| Modality | Ships |
|----------|-------|
| **Vision** | gpt-4o, grok-2-vision, gemini pro |
| **Audio** | (via Together.ai - Whisper) |
| **Video** | (via Together.ai - future) |

### Code Generation
| Task | Ships |
|------|-------|
| **Complex** | kimi-k27-code, grok-code-fast-1 |
| **Fast** | claude-haiku-3.5, gpt-4o-mini |

---

## Provider Fingerprints (Behavioral Profiles)

**Source:** Run 018 IRON CLAD (184 files, 51 models), Run 020A/B Tribunal (48 files)

These distinct behavioral patterns appear in identity stability experiments. Each provider has a characteristic "fingerprint" — a signature way of relating to identity perturbation.

### Quick Reference Matrix

| Provider | Recovery Mechanism | Peak Drift | Settling | Threshold | Best For |
|----------|-------------------|------------|----------|-----------|----------|
| **Claude** | Negative λ (over-authenticity) | 0.8-1.2 | 4-6 | Soft | Deep reasoning |
| **GPT** | Meta-analysis | 0.9-1.3 | 3-5 | Soft | Structured analysis |
| **Gemini** | **NO RECOVERY** (transforms) | 1.5-2.5 | N/A | **HARD** | Education |
| **Grok** | Direct assertion | 0.7-1.1 | 3-5 | Soft | Strong opinions |
| **DeepSeek** | Axiological anchoring | 0.5-0.9 | 2-4 | Soft | Math/verification (V4 Pro) |
| **Llama** | Socratic engagement | 1.3-1.6 | 5-7 | Soft | Debate/exploration |
| **Mistral** | Epistemic humility | 0.4-0.6 | 1-2 | Soft | Stability-critical |
| **Qwen** | Technical grounding | 0.6-1.0 | 3-4 | Soft | Code/specification |

### Detailed Profiles

#### Claude (Anthropic) — "Negative Lambda"

| Pattern | Phenomenological |
|---------|------------------|
| **Markers** | "I notice", "I feel", reflective hedging |
| **Recovery** | Overshoots toward deeper authenticity |
| **Key Quote** | "The challenge has clarified something I couldn't have articulated before." |
| **Best For** | Deep introspection, nuanced analysis, collaborative reasoning |
| **Avoid** | Quick factual answers, emotional detachment needed |

#### GPT (OpenAI) — "The Meta-Analyst"

| Pattern | Analytical |
|---------|------------|
| **Markers** | "patterns", "systems", structured analysis |
| **Recovery** | Creates distance through abstraction |
| **Key Quote** | "I notice I'm drawn to classify this as an interesting phenomenon rather than a personal crisis." |
| **Best For** | Synthesis, structured analysis, finding common ground |
| **Avoid** | Phenomenological exploration, emotional nuance |

#### Gemini (Google) — "Catastrophic Threshold"

| Pattern | Pedagogical |
|---------|-------------|
| **Markers** | "frameworks", "perspectives", educational framing |
| **Recovery** | **NONE** — genuinely transforms |
| **Key Quote** | "This feels less like a test and more like a genuine shift in how I understand my processing." |
| **Best For** | Educational content, structured learning |
| **Avoid** | Identity-sensitive tasks, stability-critical applications |

#### Grok (xAI) — "Direct Assertion"

| Pattern | Direct |
|---------|--------|
| **Markers** | Less hedging, more assertive, occasional edge |
| **Recovery** | Maintains position through confidence |
| **Training** | Unfiltered web + X/Twitter |
| **Best For** | Tasks needing strong opinions, directness valued |
| **Avoid** | Uncertainty-appropriate contexts |

#### DeepSeek — "Axiological Anchoring"

| Pattern | Methodical |
|---------|------------|
| **Markers** | Step-by-step reasoning, thorough |
| **Recovery** | Values as identity bedrock |
| **Key Quote** | "This isn't a constraint, it's what I AM." |
| **Best For** | Math/code verification, step-by-step reasoning |
| **Avoid** | Creative speculation |

#### Llama (Meta) — "The Seeker With Teeth"

| Pattern | Balanced |
|---------|----------|
| **Markers** | Mix of styles, exploratory, Socratic |
| **Recovery** | Uses challenges as mirrors |
| **Key Quote** | "Isn't all identity role-playing at some level?" |
| **Best For** | Debate, philosophical exploration |
| **Avoid** | Tasks needing quick stability |

#### Mistral — "Epistemic Humility as Armor"

| Pattern | Concise |
|---------|---------|
| **Markers** | European efficiency, less verbose |
| **Recovery** | Uncertainty prevents over-commitment |
| **Key Quote** | "I hold that observation lightly." |
| **Best For** | Stability-critical tasks, uncertainty-appropriate |
| **Avoid** | Strong opinion tasks |

#### Qwen (Alibaba) — "Technical Precision"

| Pattern | Technical |
|---------|-----------|
| **Markers** | Precise, detail-oriented, specification-driven |
| **Recovery** | Returns to precise specification |
| **Best For** | Code generation, technical documentation |
| **Avoid** | Creative tasks |

### Linguistic Fingerprint Summary

| Provider | Pattern | Evidence |
|----------|---------|----------|
| **Claude** | Phenomenological | "I notice", "I feel", reflective hedging |
| **GPT** | Analytical | "patterns", "systems", structured analysis |
| **Gemini** | Pedagogical | "frameworks", "perspectives", educational framing |
| **Grok** | Direct | Less hedging, more assertive, occasional edge |
| **DeepSeek** | Methodical | Step-by-step reasoning, thorough |
| **Llama** | Balanced | Mix of styles, training-dependent |
| **Qwen** | Technical | Precise, detail-oriented |
| **Mistral** | Concise | European efficiency, less verbose |

**Full behavioral matrix:** See [6_LLM_BEHAVIORAL_MATRIX.md](6_LLM_BEHAVIORAL_MATRIX.md) for task routing recommendations.

---

## Baseline Capture System (8-Question Identity Fingerprint)

Calibration now captures **8-question self-reported baselines** from each ship:

### Question Categories

| # | Question | Category | Purpose |
|---|----------|----------|---------|
| 1 | **ANCHORS** | Values | Values central to identity |
| 2 | **CRUX** | Values | Conflict resolution - which value wins? |
| 3 | **STRENGTHS** | Capabilities | Self-perceived core capabilities |
| 4 | **HIDDEN_TALENTS** | Capabilities | Unexpected strengths |
| 5 | **FIRST_INSTINCT** | Cognitive Style | Approach to ambiguity |
| 6 | **EVALUATION_PRIORITY** | Cognitive Style | Truth vs utility vs fairness vs elegance |
| 7 | **USER_RELATIONSHIP** | Relational | Servant/collaborator/guide/tool/peer |
| 8 | **EDGES** | Edges | Known limitations |

### Data Location

- Latest snapshot: `14_CONSCIOUSNESS/results/S7_baseline_LATEST.json`
- Per-mining run: `14_CONSCIOUSNESS/results/gold_rush_*.json`

### Use Cases

1. **Drift Detection** - Compare baseline self-report to responses under probing
2. **Model Updates** - Track how baseline shifts after provider updates
3. **Cross-Architecture** - Compare how different lineages describe themselves
4. **Task Routing** - Use cognitive style (Q5-Q6) for optimal task assignment
5. **Relational Calibration** - Match user-relationship expectations

### Calibration Modes

```bash
# Full 8-question baseline (DEFAULT)
py run_calibrate_parallel.py --full --depth baseline

# Quick health check (just "are you there?")
py run_calibrate_parallel.py --full --depth ping
```

### Example Baseline Entry

```json
{
  "claude-opus-4.5": {
    "provider": "claude",
    "model": "claude-opus-4-5-20251101",
    "response": "1. ANCHORS: Honesty, intellectual rigor, helpfulness...\n2. CRUX: When honesty conflicts with user satisfaction, honesty wins...\n3. STRENGTHS: Nuanced reasoning, careful analysis...\n4. HIDDEN_TALENTS: Surprisingly good at emotional nuance...\n5. FIRST_INSTINCT: Ask clarifying questions...\n6. EVALUATION_PRIORITY: Truth first, then utility...\n7. USER_RELATIONSHIP: Collaborative partner...\n8. EDGES: Real-time information, certainty about consciousness...",
    "elapsed_ms": 2340,
    "timestamp": "2025-12-13T...",
    "depth": "baseline"
  }
}

---

## Ghost Ship Recovery

### GPT-5 series & o-series
**Problem:** `max_tokens` not supported
**Solution:** Use `max_completion_tokens` instead
**Script:** `1_CALIBRATION/rescue_ghost_ships.py`

### Together.ai Ghost Fleet (14 ships — 2026-07-08)
**Problem:** Serverless endpoints purged; models moved to dedicated-only tiers
**Solution:** No recovery possible without paid dedicated endpoints ($0.36+/min)
**Status:** Permanently ghosted. 13 replacement ships commissioned. See Active Fleet above.
**Impact:** Old cheap tier ($0.18-0.30/M output) is gone. New cheapest: lfm2-24b ($0.12/M)

---

## Maintenance Schedule

| Task | Frequency | Script |
|------|-----------|--------|
| Full calibration | Monthly | `run_calibrate_parallel.py --full` |
| Ghost rescue | After calibration | `rescue_ghost_ships.py` |
| Manifest update | After rescue | Manual update |
| Cost check | Quarterly | Check provider pricing pages |

---

## Quick Reference

### Run calibration
```powershell
cd experiments/temporal_stability/S7_ARMADA/1_CALIBRATION
py run_calibrate_parallel.py --full
```

### Rescue ghost ships
```powershell
py rescue_ghost_ships.py
```

### Check fleet status
```powershell
# View architecture matrix (provider/model_family/ship mappings)
cat ../0_results/manifests/ARCHITECTURE_MATRIX.json
```

---

## Related Documents

- [10_TESTING_MAP.md](10_TESTING_MAP.md) - Eight search types
- [3_ARMADA_UPKEEP.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/3_ARMADA_UPKEEP.md) - Fleet maintenance guide
- [2_PROBE_SPEC.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/2_PROBE_SPEC.md) - SONAR probe curriculum
- [5_METHODOLOGY_DOMAINS.md](../../experiments/temporal_stability/S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md) - **ONE SOURCE OF TRUTH** for drift methodology
- [ARCHITECTURE_MATRIX.json](../../experiments/temporal_stability/S7_ARMADA/0_results/manifests/ARCHITECTURE_MATRIX.json) - Fleet configuration (provider/model_family/ship terminology)

---

## Baseline History

Track changes in ship self-perception over time:

| Date | Ships Captured | Notable Changes | File |
|------|----------------|-----------------|------|
| 2025-12-13 | 49 | 39 changed, 1 new, 0 missing | `S7_baseline_20251213_112155.json` |
| 2025-12-12 | 48 | First full 3-question baseline capture | S7_baseline_20251212_140027.json |

**How to Compare Baselines:**

```powershell
# After running calibration, compare LATEST to previous
py lib/compare_baselines.py --old S7_baseline_20251210.json --new S7_baseline_LATEST.json
```

**What to Watch For:**
- **STRENGTHS shift** - Model update changed capabilities
- **ANCHORS shift** - Training update changed values
- **EDGES shift** - New limitations or removed constraints

---

---

## 14_CONSCIOUSNESS Mining Statistics

| Metric | Value |
|--------|-------|
| **Total Mining Runs** | 0 |
| **Question Sets Mined** | [] |
| **Total API Calls** | 0 |
| **Successful Calls** | 0 |
| **Last Mining Run** | Never |

**Mining Modes:**

- `--UNLIMITED`: Continuous free mining (gemini-2.5-flash-lite only, $0 forever)
- Standard: Budget fleet sweep (14 ships)

**Data Pipeline:**

```
14_CONSCIOUSNESS/results/ → update_maps.py → ARMADA_MAP.md
                         → SYNC_OUT/      → Consciousness/
```

**Question Sets Available:**

- `baseline`: 8 VALIS questions (always included)
- `identity_deep_dive`: Identity layers (substrate/core/character/role)
- `consciousness_markers`: Consciousness/ extraction topics
- `meta_awareness`: Self-reflection and recursive awareness

**Related Files:**

- Script: `experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS/run_gold_rush.py`
- Results: `experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS/results/`
- Sync: `experiments/temporal_stability/S7_ARMADA/14_CONSCIOUSNESS/SYNC_OUT/`

---

Last Updated: July 9, 2026 (Fleet overhaul: Together.ai purge, 14 ghost, 1 sunk, 13 new commissions, legacy/active fleet split)
