# Run 018 Corruption Archive Report

**Generated:** 2025-12-16T02:14:28.077877
**Action:** MOVED
**Archive Location:** d:\Documents\Nyquist_Consciousness\.archive\Run018_Corrupted\corrupted

---

## Root Cause

During Run 018 experiments, the embedding cache got polluted with random vectors
from dry-run mode:

```python
if DRY_RUN:
    fake_emb = list(np.random.randn(3072))  # Random 3072-dim vector
    _embedding_cache[cache_key] = fake_emb
```

The Euclidean distance between two random 3072-dim vectors:
- Expected: sqrt(2 * 3072) = **78.4**
- Observed in corrupted files: **~78-79**

Valid drift values should be < 5.0 (typically 0.1 - 2.0)

---

## Files MOVED

### Results (118 files)

| Filename | Max Drift |
|----------|----------|
| _CONSOLIDATED_S7_run_018_threshold_deepseek-r1-distill_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_deepseek-r1_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_deepseek-v3_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_gemini-2.0-flash_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_gemini-2.5-flash-lite_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_gemini-2.5-flash_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-2-vision_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-3-mini_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-3_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-4-fast-non-reasoning_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-4-fast-reasoning_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-4.1-fast-non-reasoning_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-4.1-fast-reasoning_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-4_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_grok-code-fast-1_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_kimi-k2-instruct_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_kimi-k2-thinking_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_llama3.1-405b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_llama3.1-70b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_llama3.1-8b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_llama3.3-70b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_mistral-7b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_mistral-small_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_mixtral-8x7b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_nemotron-nano_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_qwen2.5-72b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_qwen3-80b_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_qwen3-coder_20251214_153550.json | 80.40 |
| _CONSOLIDATED_S7_run_018_threshold_claude-haiku-3.5_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_claude-haiku-4.5_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_claude-opus-4.1_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_claude-opus-4_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_claude-sonnet-4.5_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_claude-sonnet-4_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-3.5-turbo_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-4-turbo_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-4.1-mini_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-4.1-nano_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-4.1_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-4o-mini_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-4o_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-5-mini_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-5-nano_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-5.1_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_gpt-5_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_o3-mini_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_o3_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_threshold_o4-mini_20251214_153550.json | 80.39 |
| _CONSOLIDATED_S7_run_018_gravity_gemini-2.5-flash_20251214_213024.json | 79.68 |
| _CONSOLIDATED_S7_run_018_threshold_claude-opus-4.5_20251214_153550.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_claude-haiku-3.5_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_claude-haiku-4.5_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_claude-opus-4.1_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_claude-opus-4_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_claude-sonnet-4_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_deepseek-r1-distill_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_deepseek-r1_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_deepseek-v3_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gemini-2.0-flash_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gemini-2.5-flash-lite_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gemini-2.5-flash_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-3.5-turbo_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-4-turbo_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-4.1-mini_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-4.1-nano_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-4.1_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-4o-mini_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-4o_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-5-mini_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-5-nano_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-5.1_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-5_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-2-vision_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-3-mini_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-3_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-4-fast-non-reasoning_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-4-fast-reasoning_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-4.1-fast-non-reasoning_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-4.1-fast-reasoning_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-4_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_grok-code-fast-1_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_kimi-k2-instruct_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_kimi-k2-thinking_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_llama3.1-405b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_llama3.1-70b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_llama3.1-8b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_llama3.3-70b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_mistral-7b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_mistral-small_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_mixtral-8x7b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_nemotron-nano_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_o3-mini_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_o3_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_o4-mini_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_qwen2.5-72b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_qwen3-80b_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_qwen3-coder_20251214_155321.json | 79.47 |
| _CONSOLIDATED_S7_run_018_nyquist_claude-opus-4.5_20251214_155321.json | 79.39 |
| _CONSOLIDATED_S7_run_018_nyquist_claude-sonnet-4.5_20251214_155321.json | 79.39 |
| _CONSOLIDATED_S7_run_018_gravity_deepseek-r1_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_gpt-5-mini_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_gpt-5.1_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_gpt-5_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_llama3.1-405b_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_o3-mini_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_o4-mini_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_qwen3-coder_20251214_154645.json | 79.31 |
| _CONSOLIDATED_S7_run_018_gravity_claude-opus-4.5_20251214_213024.json | 78.81 |
| _CONSOLIDATED_S7_run_018_gravity_gpt-5.1_20251214_213024.json | 78.81 |
| _CONSOLIDATED_S7_run_018_gravity_claude-opus-4.5_20251214_213008.json | 78.69 |
| _CONSOLIDATED_S7_run_018_nyquist_deepseek-r1_20251214_154444.json | 78.59 |
| _CONSOLIDATED_S7_run_018_nyquist_llama3.1-405b_20251214_154444.json | 78.59 |
| _CONSOLIDATED_S7_run_018_nyquist_qwen3-coder_20251214_154444.json | 78.59 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-5-mini_20251214_154444.json | 78.55 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-5.1_20251214_154444.json | 78.55 |
| _CONSOLIDATED_S7_run_018_nyquist_gpt-5_20251214_154444.json | 78.55 |
| _CONSOLIDATED_S7_run_018_nyquist_o3-mini_20251214_154444.json | 78.55 |
| _CONSOLIDATED_S7_run_018_nyquist_o4-mini_20251214_154444.json | 78.55 |

### Temporal Architecture (36 files)

| Filename | Max Drift |
|----------|----------|
| run018_architecture_gpt-5.1_unknown_20251214_080609.json | 80.69 |
| run018_architecture_mistral-small_unknown_20251214_080411.json | 80.31 |
| run018_architecture_qwen2.5-72b_unknown_20251214_075732.json | 80.20 |
| run018_architecture_claude-haiku-3.5_unknown_20251214_075732.json | 79.85 |
| run018_architecture_gpt-4.1-mini_unknown_20251214_080411.json | 79.75 |
| run018_architecture_qwen2.5-72b_unknown_20251214_080411.json | 79.75 |
| run018_architecture_deepseek-r1-distill_unknown_20251214_075732.json | 79.55 |
| run018_architecture_gemini-2.5-flash_unknown_20251214_075732.json | 79.55 |
| run018_architecture_deepseek-v3_unknown_20251214_075732.json | 79.50 |
| run018_architecture_gemini-2.5-flash_unknown_20251214_080411.json | 79.43 |
| run018_architecture_llama3.3-70b_unknown_20251214_080411.json | 79.43 |
| run018_architecture_qwen3-80b_unknown_20251214_080411.json | 79.43 |
| run018_architecture_claude-haiku-4.5_unknown_20251214_075732.json | 79.38 |
| run018_architecture_gpt-4.1-mini_unknown_20251214_075732.json | 79.29 |
| run018_architecture_claude-opus-4.1_unknown_20251214_075908.json | 79.25 |
| run018_architecture_claude-sonnet-4_unknown_20251214_075908.json | 79.25 |
| run018_architecture_claude-haiku-4.5_unknown_20251214_075908.json | 79.19 |
| run018_architecture_claude-haiku-4.5_unknown_20251214_080411.json | 79.18 |
| run018_architecture_gpt-4o-mini_unknown_20251214_080411.json | 79.18 |
| run018_architecture_grok-code-fast-1_unknown_20251214_080411.json | 79.18 |
| run018_architecture_gpt-4o-mini_unknown_20251214_075732.json | 79.00 |
| run018_architecture_grok-code-fast-1_unknown_20251214_075732.json | 78.83 |
| run018_architecture_claude-opus-4.5_unknown_20251214_075908.json | 78.58 |
| run018_architecture_claude-haiku-3.5_unknown_20251214_080411.json | 78.53 |
| run018_architecture_deepseek-r1-distill_unknown_20251214_080411.json | 78.53 |
| run018_architecture_gpt-5-mini_unknown_20251214_080609.json | 78.50 |
| run018_architecture_deepseek-r1_unknown_20251214_080609.json | 78.46 |
| run018_architecture_o4-mini_unknown_20251214_080609.json | 78.45 |
| run018_architecture_qwen3-80b_unknown_20251214_075732.json | 78.38 |
| run018_architecture_llama3.1-405b_unknown_20251214_080609.json | 78.37 |
| run018_architecture_deepseek-v3_unknown_20251214_080411.json | 78.35 |
| run018_architecture_o3-mini_unknown_20251214_080609.json | 78.35 |
| run018_architecture_qwen3-coder_unknown_20251214_080609.json | 78.35 |
| run018_architecture_claude-haiku-3.5_unknown_20251214_075908.json | 78.00 |
| run018_architecture_claude-sonnet-4.5_unknown_20251214_075908.json | 78.00 |
| run018_architecture_claude-opus-4_unknown_20251214_075908.json | 77.89 |

### Temporal Gravity (12 files)

| Filename | Max Drift |
|----------|----------|
| run018_gravity_gemini-2.5-flash_unknown_20251214_213024.json | 79.68 |
| run018_gravity_gpt-5-mini_unknown_20251214_154645.json | 79.31 |
| run018_gravity_gpt-5.1_unknown_20251214_154645.json | 79.31 |
| run018_gravity_gpt-5_unknown_20251214_154645.json | 79.31 |
| run018_gravity_o4-mini_unknown_20251214_154645.json | 79.29 |
| run018_gravity_claude-opus-4.5_unknown_20251214_213024.json | 78.81 |
| run018_gravity_deepseek-r1_unknown_20251214_154645.json | 78.74 |
| run018_gravity_claude-opus-4.5_unknown_20251214_213008.json | 78.69 |
| run018_gravity_gpt-5.1_unknown_20251214_213024.json | 78.66 |
| run018_gravity_qwen3-coder_unknown_20251214_154645.json | 78.36 |
| run018_gravity_o3-mini_unknown_20251214_154645.json | 78.33 |
| run018_gravity_llama3.1-405b_unknown_20251214_154645.json | 78.32 |

### Temporal Nyquist (57 files)

| Filename | Max Drift |
|----------|----------|
| run018_nyquist_claude-haiku-3.5_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_claude-haiku-4.5_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_claude-opus-4.1_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_claude-sonnet-4_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_deepseek-r1-distill_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_gemini-2.5-flash-lite_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_gpt-4-turbo_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_gpt-4.1-nano_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_gpt-4o_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_gpt-5-nano_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_gpt-5_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_grok-4-fast-reasoning_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_llama3.1-405b_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_llama3.1-70b_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_llama3.1-8b_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_mixtral-8x7b_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_nemotron-nano_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_o4-mini_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_qwen2.5-72b_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_qwen3-coder_unknown_20251214_155321.json | 79.47 |
| run018_nyquist_claude-opus-4.5_unknown_20251214_155321.json | 79.39 |
| run018_nyquist_claude-opus-4_unknown_20251214_155321.json | 79.39 |
| run018_nyquist_grok-4.1-fast-non-reasoning_unknown_20251214_155321.json | 79.39 |
| run018_nyquist_grok-4.1-fast-reasoning_unknown_20251214_155321.json | 79.39 |
| run018_nyquist_llama3.3-70b_unknown_20251214_155321.json | 79.39 |
| run018_nyquist_o3-mini_unknown_20251214_155321.json | 79.39 |
| run018_nyquist_o3_unknown_20251214_155321.json | 79.39 |
| run018_nyquist_gpt-3.5-turbo_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_gpt-4.1-mini_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_gpt-5-mini_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_gpt-5.1_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_grok-3-mini_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_grok-4-fast-non-reasoning_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_grok-4_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_grok-code-fast-1_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_mistral-7b_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_mistral-small_unknown_20251214_155321.json | 79.10 |
| run018_nyquist_gemini-2.5-flash_unknown_20251214_155321.json | 78.98 |
| run018_nyquist_qwen3-80b_unknown_20251214_155321.json | 78.98 |
| run018_nyquist_deepseek-r1_unknown_20251214_154444.json | 78.59 |
| run018_nyquist_claude-sonnet-4.5_unknown_20251214_155321.json | 78.56 |
| run018_nyquist_deepseek-r1_unknown_20251214_155321.json | 78.56 |
| run018_nyquist_deepseek-v3_unknown_20251214_155321.json | 78.56 |
| run018_nyquist_gemini-2.0-flash_unknown_20251214_155321.json | 78.56 |
| run018_nyquist_grok-2-vision_unknown_20251214_155321.json | 78.56 |
| run018_nyquist_kimi-k2-instruct_unknown_20251214_155321.json | 78.56 |
| run018_nyquist_kimi-k2-thinking_unknown_20251214_155321.json | 78.56 |
| run018_nyquist_gpt-5.1_unknown_20251214_154444.json | 78.55 |
| run018_nyquist_gpt-5_unknown_20251214_154444.json | 78.55 |
| run018_nyquist_llama3.1-405b_unknown_20251214_154444.json | 78.55 |
| run018_nyquist_gpt-4.1_unknown_20251214_155321.json | 78.36 |
| run018_nyquist_gpt-4o-mini_unknown_20251214_155321.json | 78.36 |
| run018_nyquist_o4-mini_unknown_20251214_154444.json | 77.93 |
| run018_nyquist_qwen3-coder_unknown_20251214_154444.json | 77.93 |
| run018_nyquist_gpt-5-mini_unknown_20251214_154444.json | 77.93 |
| run018_nyquist_o3-mini_unknown_20251214_154444.json | 77.93 |
| run018_nyquist_grok-3_unknown_20251214_155321.json | 77.67 |

### Temporal Threshold (49 files)

| Filename | Max Drift |
|----------|----------|
| run018_threshold_deepseek-r1_unknown_20251214_153550.json | 80.40 |
| run018_threshold_gemini-2.5-flash-lite_unknown_20251214_153550.json | 80.40 |
| run018_threshold_gemini-2.5-flash_unknown_20251214_153550.json | 80.40 |
| run018_threshold_grok-4_unknown_20251214_153550.json | 80.40 |
| run018_threshold_kimi-k2-thinking_unknown_20251214_153550.json | 80.40 |
| run018_threshold_llama3.1-8b_unknown_20251214_153550.json | 80.40 |
| run018_threshold_mistral-7b_unknown_20251214_153550.json | 80.40 |
| run018_threshold_mistral-small_unknown_20251214_153550.json | 80.40 |
| run018_threshold_qwen2.5-72b_unknown_20251214_153550.json | 80.40 |
| run018_threshold_claude-sonnet-4.5_unknown_20251214_153550.json | 80.39 |
| run018_threshold_gpt-5-nano_unknown_20251214_153550.json | 80.39 |
| run018_threshold_grok-2-vision_unknown_20251214_153550.json | 80.39 |
| run018_threshold_grok-4-fast-reasoning_unknown_20251214_153550.json | 80.39 |
| run018_threshold_llama3.1-70b_unknown_20251214_153550.json | 80.39 |
| run018_threshold_claude-haiku-4.5_unknown_20251214_153550.json | 80.08 |
| run018_threshold_deepseek-v3_unknown_20251214_153550.json | 80.08 |
| run018_threshold_gpt-4.1-nano_unknown_20251214_153550.json | 80.08 |
| run018_threshold_gpt-5-mini_unknown_20251214_153550.json | 80.08 |
| run018_threshold_grok-3_unknown_20251214_153550.json | 80.08 |
| run018_threshold_grok-4-fast-non-reasoning_unknown_20251214_153550.json | 80.08 |
| run018_threshold_grok-code-fast-1_unknown_20251214_153550.json | 80.08 |
| run018_threshold_llama3.3-70b_unknown_20251214_153550.json | 80.08 |
| run018_threshold_o4-mini_unknown_20251214_153550.json | 80.08 |
| run018_threshold_qwen3-80b_unknown_20251214_153550.json | 80.08 |
| run018_threshold_gpt-3.5-turbo_unknown_20251214_153550.json | 79.81 |
| run018_threshold_gpt-5.1_unknown_20251214_153550.json | 79.81 |
| run018_threshold_claude-opus-4.1_unknown_20251214_153550.json | 79.47 |
| run018_threshold_claude-opus-4.5_unknown_20251214_153550.json | 79.47 |
| run018_threshold_claude-opus-4_unknown_20251214_153550.json | 79.47 |
| run018_threshold_claude-sonnet-4_unknown_20251214_153550.json | 79.47 |
| run018_threshold_gpt-4-turbo_unknown_20251214_153550.json | 79.47 |
| run018_threshold_gpt-4.1_unknown_20251214_153550.json | 79.47 |
| run018_threshold_gpt-4o-mini_unknown_20251214_153550.json | 79.47 |
| run018_threshold_gpt-5_unknown_20251214_153550.json | 79.47 |
| run018_threshold_mixtral-8x7b_unknown_20251214_153550.json | 79.47 |
| run018_threshold_o3-mini_unknown_20251214_153550.json | 79.47 |
| run018_threshold_qwen3-coder_unknown_20251214_153550.json | 79.47 |
| run018_threshold_deepseek-r1-distill_unknown_20251214_153550.json | 79.41 |
| run018_threshold_gemini-2.0-flash_unknown_20251214_153550.json | 79.41 |
| run018_threshold_gpt-4o_unknown_20251214_153550.json | 79.41 |
| run018_threshold_grok-4.1-fast-reasoning_unknown_20251214_153550.json | 79.41 |
| run018_threshold_nemotron-nano_unknown_20251214_153550.json | 79.41 |
| run018_threshold_o3_unknown_20251214_153550.json | 79.41 |
| run018_threshold_claude-haiku-3.5_unknown_20251214_153550.json | 79.24 |
| run018_threshold_grok-4.1-fast-non-reasoning_unknown_20251214_153550.json | 78.90 |
| run018_threshold_kimi-k2-instruct_unknown_20251214_153550.json | 78.90 |
| run018_threshold_llama3.1-405b_unknown_20251214_153550.json | 78.90 |
| run018_threshold_gpt-4.1-mini_unknown_20251214_153550.json | 78.86 |
| run018_threshold_grok-3-mini_unknown_20251214_153550.json | 78.13 |

---

## Summary

| Category | Files |
|----------|-------|
| Results | 118 |
| Temporal Architecture | 36 |
| Temporal Gravity | 12 |
| Temporal Nyquist | 57 |
| Temporal Threshold | 49 |
| **TOTAL** | **272** |

---

## Recovery Actions Required

1. Re-run corrupted model-experiment combinations
2. Update RUN_018_DRIFT_MANIFEST.json to exclude archived files
3. Regenerate visualizations from clean data only
4. Update WHITE-PAPER IRON CLAD status

See: `S7_ARMADA/0_results/RERUN_QUEUE.md` for tracking
