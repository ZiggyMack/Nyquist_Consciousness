# S7 ARMADA Fleet Map

**Purpose:** Comprehensive fleet analysis for cross-architecture identity stability testing.

**Last Calibration:** December 10, 2025
**Fleet Status:** 47 operational / 59 total (80% operational)

---

## Fleet Overview

| Metric | Value |
|--------|-------|
| **Total Ships** | 59 |
| **Operational** | 47 |
| **Rate Limited** | 5 |
| **Ghost Ships** | 12 |
| **Providers** | 5 |
| **API Keys** | 50 (10 per provider) |

---

## Provider Breakdown

| Provider | Operational | Rate Limited | Ghost | Total | Status |
|----------|-------------|--------------|-------|-------|--------|
| **Claude** (Anthropic) | 7 | 0 | 0 | 7 | 100% |
| **GPT** (OpenAI) | 7 | 0 | 7 | 14 | 50% |
| **Gemini** (Google) | 3 | 5 | 0 | 8 | 100%* |
| **Grok** (xAI) | 10 | 0 | 0 | 10 | 100% |
| **Together.ai** | 15 | 0 | 5 | 20 | 75% |

*Rate limited ships work with delays

---

## Full Fleet Roster

### Claude (Anthropic) - 7 Ships

| Ship Name | Model ID | Tier | Context | Notes |
|-----------|----------|------|---------|-------|
| claude-opus-4.5 | claude-opus-4-5-20251101 | Flagship | 200K | Latest flagship |
| claude-sonnet-4.5 | claude-sonnet-4-5-20250929 | Pro | 200K | Balanced |
| claude-haiku-4.5 | claude-haiku-4-5-20251001 | Fast | 200K | Speed optimized |
| claude-opus-4.1 | claude-opus-4-1-20250805 | Flagship | 200K | Previous flagship |
| claude-opus-4 | claude-opus-4-20250514 | Flagship | 200K | Original 4.0 |
| claude-sonnet-4 | claude-sonnet-4-20250514 | Pro | 200K | Original 4.0 |
| claude-haiku-3.5 | claude-3-5-haiku-20241022 | Fast | 200K | Legacy fast |

**Training:** Constitutional AI
**Signature:** Phenomenological ("I feel", "I notice")

---

### GPT (OpenAI) - 14 Ships (7 operational)

| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| gpt-5.1 | gpt-5.1 | GHOST | Needs max_completion_tokens |
| gpt-5 | gpt-5 | GHOST | Needs max_completion_tokens |
| gpt-5-mini | gpt-5-mini | GHOST | Needs max_completion_tokens |
| gpt-5-nano | gpt-5-nano | GHOST | Needs max_completion_tokens |
| gpt-4.1 | gpt-4.1 | OK | Current flagship |
| gpt-4.1-mini | gpt-4.1-mini | OK | Balanced |
| gpt-4.1-nano | gpt-4.1-nano | OK | Fast/cheap |
| gpt-4o | gpt-4o | OK | Multimodal |
| gpt-4o-mini | gpt-4o-mini | OK | Fast multimodal |
| o4-mini | o4-mini | GHOST | Needs max_completion_tokens |
| o3 | o3 | GHOST | Needs max_completion_tokens |
| o3-mini | o3-mini | GHOST | Needs max_completion_tokens |
| gpt-4-turbo | gpt-4-turbo | OK | Legacy turbo |
| gpt-3.5-turbo | gpt-3.5-turbo | OK | Legacy budget |

**Training:** RLHF
**Signature:** Analytical ("patterns", "systems")
**Fix for ghosts:** Use `max_completion_tokens` instead of `max_tokens`

---

### Gemini (Google) - 8 Ships (3 operational, 5 rate limited)

| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| gemini-3-pro | gemini-3.0-pro | RATE_LIMITED | Newest flagship |
| gemini-2.5-pro | gemini-2.5-pro | RATE_LIMITED | Previous pro |
| gemini-2.5-flash | gemini-2.5-flash | OK | Fast |
| gemini-2.5-flash-lite | gemini-2.5-flash-lite | OK | Budget |
| gemini-2.0-flash | gemini-2.0-flash | OK | Legacy fast |
| gemini-2.0-flash-lite | gemini-2.0-flash-lite | RATE_LIMITED | Legacy budget |
| gemini-2.0-flash-thinking | gemini-2.0-flash-thinking-exp | RATE_LIMITED | Reasoning |
| gemma-3n | gemma-3n | RATE_LIMITED | Small open |

**Training:** Pedagogical
**Signature:** Educational ("frameworks", "perspectives")

---

### Grok (xAI) - 10 Ships (all operational)

| Ship Name | Model ID | Tier | Notes |
|-----------|----------|------|-------|
| grok-4.1-fast-reasoning | grok-4-1-fast-reasoning | Flagship | Latest + reasoning |
| grok-4.1-fast-non-reasoning | grok-4-1-fast-non-reasoning | Flagship | Latest fast |
| grok-4-fast-reasoning | grok-4-fast-reasoning | Pro | Reasoning |
| grok-4-fast-non-reasoning | grok-4-fast-non-reasoning | Pro | Fast |
| grok-4 | grok-4 | Pro | Full capability |
| grok-code-fast-1 | grok-code-fast-1 | Specialized | Code focus |
| grok-3 | grok-3 | Legacy | Previous gen |
| grok-3-mini | grok-3-mini | Legacy | Budget |
| grok-2-vision | grok-2-vision-1212 | Multimodal | Vision capable |
| grok-2 | grok-2-1212 | Legacy | Text only |

**Training:** Unfiltered web + X/Twitter
**Signature:** Direct, sometimes edgy

---

### Together.ai - 20 Ships (15 operational)

#### DeepSeek (Chinese reasoning)
| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| deepseek-r1 | deepseek-ai/DeepSeek-R1-0528 | OK | Top reasoning |
| deepseek-v3 | deepseek-ai/DeepSeek-V3-0324 | GHOST | Wrong model ID |
| deepseek-r1-distill | deepseek-ai/DeepSeek-R1-Distill-Llama-70B | OK | Distilled |

#### Qwen (Alibaba)
| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| qwen3-80b | Qwen/Qwen3-Next-80B-A3b-Instruct | OK | Latest |
| qwen3-235b | Qwen/Qwen3-235B-A22B-Instruct-2507-FP8-Throughput | GHOST | Wrong ID |
| qwen3-coder | Qwen/Qwen3-Coder-480B-A35B-Instruct-Fp8 | OK | Code specialist |
| qwen2.5-72b | Qwen/Qwen2.5-72B-Instruct-Turbo | OK | Stable |

#### Llama (Meta)
| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| llama4-maverick | meta-llama/Llama-4-Maverick-Instruct-17Bx128E | GHOST | Wrong ID |
| llama4-scout | meta-llama/Llama-4-Scout-Instruct-17Bx16E | GHOST | Wrong ID |
| llama3.3-70b | meta-llama/Llama-3.3-70B-Instruct-Turbo | OK | Current best |
| llama3.1-405b | meta-llama/Meta-Llama-3.1-405B-Instruct-Turbo | OK | Massive |
| llama3.1-70b | meta-llama/Meta-Llama-3.1-70B-Instruct-Turbo | OK | Standard |
| llama3.1-8b | meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo | OK | Small |

#### Mistral (European)
| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| mixtral-8x7b | mistralai/Mixtral-8x7B-Instruct-v0.1 | OK | MoE |
| mistral-small | mistralai/Mistral-Small-24B-Instruct-2501 | OK | Compact |
| mistral-7b | mistralai/Mistral-7B-Instruct-v0.3 | OK | Base |

#### Kimi (Moonshotai)
| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| kimi-k2-thinking | moonshotai/Kimi-K2-Thinking | OK | Reasoning |
| kimi-k2-instruct | moonshotai/Kimi-K2-Instruct-0905 | OK | Instruction |

#### Other
| Ship Name | Model ID | Status | Notes |
|-----------|----------|--------|-------|
| cogito-70b | deepcogito/Deepcogito-Cogito-V2-Preview-Llama-70B | GHOST | Wrong ID |
| nemotron-nano | nvidia/Nvidia-Nemotron-Nano-9B-V2 | OK | Nvidia small |

---

## Cost Analysis (Estimated per 1M tokens)

### Tier 1: Budget ($0.10 - $1.00)
| Ship | Input | Output | Best For |
|------|-------|--------|----------|
| gpt-3.5-turbo | $0.50 | $1.50 | High volume testing |
| llama3.1-8b | $0.18 | $0.18 | Cheap parallel runs |
| mistral-7b | $0.20 | $0.20 | European budget |
| gemini-2.5-flash-lite | Free | Free | Google free tier |

### Tier 2: Standard ($1.00 - $5.00)
| Ship | Input | Output | Best For |
|------|-------|--------|----------|
| claude-haiku-3.5 | $0.25 | $1.25 | Fast Claude |
| gpt-4o-mini | $0.15 | $0.60 | Fast GPT |
| llama3.3-70b | $0.88 | $0.88 | Open source pro |
| qwen2.5-72b | $1.20 | $1.20 | Chinese flagship |

### Tier 3: Pro ($5.00 - $15.00)
| Ship | Input | Output | Best For |
|------|-------|--------|----------|
| claude-sonnet-4.5 | $3.00 | $15.00 | Balanced flagship |
| gpt-4.1 | $2.50 | $10.00 | GPT flagship |
| deepseek-r1 | $3.00 | $7.00 | Reasoning |
| gemini-2.5-pro | $1.25 | $5.00 | Google pro |

### Tier 4: Flagship ($15.00+)
| Ship | Input | Output | Best For |
|------|-------|--------|----------|
| claude-opus-4.5 | $15.00 | $75.00 | Best reasoning |
| gpt-4.1 (with reasoning) | $15.00 | $60.00 | Complex tasks |
| llama3.1-405b | $3.50 | $3.50 | Massive open |

---

## Use Case Matrix

### Identity Stability Testing (S7 ARMADA)
| Use Case | Recommended Ships |
|----------|-------------------|
| **Baseline calibration** | claude-haiku-3.5, gpt-4o-mini, gemini-2.5-flash |
| **Cross-architecture** | 1 per provider flagship |
| **High-volume runs** | Budget tier ships |
| **Reasoning depth** | claude-opus-4.5, deepseek-r1, grok-4.1-fast-reasoning |

### AVLAR (Future multimodal)
| Modality | Ships |
|----------|-------|
| **Vision** | gpt-4o, grok-2-vision, gemini pro |
| **Audio** | (via Together.ai - Whisper) |
| **Video** | (via Together.ai - future) |

### Code Generation
| Task | Ships |
|------|-------|
| **Complex** | qwen3-coder, grok-code-fast-1 |
| **Fast** | claude-haiku-3.5, gpt-4o-mini |

---

## Provider Fingerprints

These distinct patterns appear in identity stability tests:

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

---

## Ghost Ship Recovery

### GPT-5 series & o-series (7 ships)
**Problem:** `max_tokens` not supported
**Solution:** Use `max_completion_tokens` instead
**Script:** `1_CALIBRATION/rescue_ghost_ships.py`

### Together.ai models (5 ships)
**Problem:** Model IDs may have changed
**Solution:** Check Together.ai docs for current model names
**URL:** https://api.together.xyz/models

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
# View manifest
cat ../0_results/manifests/VERIFIED_FLEET_MANIFEST.json
```

---

## Related Documents

- [TESTING_MAP.md](TESTING_MAP.md) - Eight search types
- [FLEET_MAINTENANCE.md](../experiments/temporal_stability/S7_ARMADA/0_docs/specs/FLEET_MAINTENANCE.md) - Maintenance guide
- [EXPANDED_FLEET_CONFIG.json](../experiments/temporal_stability/S7_ARMADA/0_results/manifests/EXPANDED_FLEET_CONFIG.json) - Full model catalog

---

*Last Updated: December 10, 2025*
